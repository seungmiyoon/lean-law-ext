/-!
# 열린 개념 · 3값 판정 · 시점 적용 · 규범 서열 — Lean 형식화 실험

lean-law.vercel.app (hunkim/lean-labor-law) 의 판정 구조를 전제로,
미아(윤승미)가 슬랙에서 제안한 네 가지를 Lean 으로 어디까지 표현·증명할 수 있는지 재는 실험.

1. 수치·기한 요건은 그대로 증명 / 평가적 요건은 가정 + 판례 경계
2. 출력 3값: 충족 · 위반 · 미확정(+ 입증 부담)
3. 시행일별 버전 → 적용 시점 파라미터, 부칙·경과규정
4. 조약(IMO·ILO·MLC 등)의 법 적용 순서 (헌법 제6조①: 조약 = 국내법과 같은 효력) + 자기집행력 플래그

의존성 없음 (core Lean 4 만). `lean LeanLawExt.lean` 으로 검증.
판례 요지는 **구조 시연용 예시**이며 실제 판례 인용이 아님 — 실제 경계는 법률 전문가가 채워야 함.
-/

namespace LeanLawExt

/-! ## 1. 3값 판정 (Kleene 강 3값 논리) -/

/-- 판정값. 기존 사이트의 `Status` 는 ok | violation | needFacts | info 인데,
    `needFacts` 는 "사실을 더 물어야 함" 이고, 여기의 `undetermined` 는
    "사실은 다 있어도 **평가적 요건**이 판례 경계 밖이라 결론을 못 낸다" 를 뜻한다. -/
inductive Verdict where
  | satisfied
  | violated
  | undetermined
  deriving DecidableEq, Repr

namespace Verdict

/-- 논리곱. 하나라도 위반이면 위반, 전부 충족이면 충족, 그 외 미확정. -/
def and : Verdict → Verdict → Verdict
  | violated, _ => violated
  | _, violated => violated
  | satisfied, satisfied => satisfied
  | _, _ => undetermined

def ofBool (b : Bool) : Verdict := if b then satisfied else violated

def all : List Verdict → Verdict
  | [] => satisfied
  | v :: vs => v.and (all vs)

/-- 정보 순서: 미확정은 어느 확정값으로도 정제될 수 있고, 확정값은 바뀌지 않는다. -/
def refines : Verdict → Verdict → Prop
  | undetermined, _ => True
  | a, b => a = b

instance : DecidableRel refines := by
  intro a b; cases a <;> cases b <;> simp [refines] <;> infer_instance

theorem and_comm (a b : Verdict) : a.and b = b.and a := by
  cases a <;> cases b <;> rfl

theorem and_violated_left (b : Verdict) : violated.and b = violated := by
  cases b <;> rfl

theorem and_violated_right (a : Verdict) : a.and violated = violated := by
  cases a <;> rfl

theorem and_satisfied_iff (a b : Verdict) :
    a.and b = satisfied ↔ a = satisfied ∧ b = satisfied := by
  cases a <;> cases b <;> simp [and]

theorem and_violated_iff (a b : Verdict) :
    a.and b = violated ↔ a = violated ∨ b = violated := by
  cases a <;> cases b <;> simp [and]

/-- **단조성**: 증거를 더 넣어 각 요건을 정제해도 결론은 정제 방향으로만 움직인다.
    (충족이 위반으로 뒤집히지 않는다 — 3값 설계의 핵심 안전성) -/
theorem and_mono {a a' b b' : Verdict} (ha : refines a a') (hb : refines b b') :
    refines (a.and b) (a'.and b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all [refines, and]

theorem all_violated_of_mem {vs : List Verdict} (h : violated ∈ vs) : all vs = violated := by
  induction vs with
  | nil => cases h
  | cons v vs ih =>
    simp only [all]
    rcases List.mem_cons.mp h with rfl | h'
    · exact and_violated_left _
    · rw [ih h']; exact and_violated_right _

theorem all_satisfied_iff (vs : List Verdict) :
    all vs = satisfied ↔ ∀ v ∈ vs, v = satisfied := by
  induction vs with
  | nil => simp [all]
  | cons v vs ih => simp [all, and_satisfied_iff, ih]

end Verdict

/-! ## 2. 평가적 요건: "긴박한 경영상의 필요" (근로기준법 제24조①)

기존 사이트: `urgentNeed : Bool` 을 LLM 이 문장에서 바로 찍는다 (열린 개념: 입력).
제안: Bool 대신 **증거 구조**를 받고, 판례 경계 안에 들어오는 패턴만 확정, 나머지는 미확정 + 입증 부담. -/

/-- 증거. `none` = 아직 확인 안 됨. 판례 요지에서 반복 등장하는 요소만 뽑았다 (예시). -/
structure UrgentNeedEvidence where
  /-- 연속 적자 연수 (재무제표 기준) -/
  deficitYears    : Option Nat  := none
  /-- 자본잠식 여부 -/
  capitalImpaired : Option Bool := none
  /-- 사업부문 폐지·축소가 있었는지 -/
  divisionClosed  : Option Bool := none
  /-- 흑자 상태에서 인건비 절감만을 목적으로 하는지 -/
  laborCostOnly   : Option Bool := none
  deriving Repr, DecidableEq

/-- 증거 정제: `e` 에서 확인된 값은 `e'` 에서도 같은 값이다 (없던 값이 채워지는 것만 허용). -/
def UrgentNeedEvidence.Refines (e e' : UrgentNeedEvidence) : Prop :=
  (∀ n, e.deficitYears = some n → e'.deficitYears = some n) ∧
  (∀ b, e.capitalImpaired = some b → e'.capitalImpaired = some b) ∧
  (∀ b, e.divisionClosed = some b → e'.divisionClosed = some b) ∧
  (∀ b, e.laborCostOnly = some b → e'.laborCostOnly = some b)

/-! 판례 경계의 각 패턴 (예시). 실제 운영 시 각 패턴에 판례 번호가 붙는다. -/
/-- [성립 예시 A] 계속된 적자(2년 이상) + 자본잠식 -/
def patA (e : UrgentNeedEvidence) : Bool :=
  match e.deficitYears, e.capitalImpaired with
  | some n, some true => n ≥ 2
  | _, _ => false
/-- [성립 예시 B] 적자 1년 이상 + 사업부문 폐지 -/
def patB (e : UrgentNeedEvidence) : Bool :=
  match e.deficitYears, e.divisionClosed with
  | some n, some true => n ≥ 1
  | _, _ => false
/-- [불성립 예시 C] 적자 없음 + 인건비 절감만이 목적 -/
def patC (e : UrgentNeedEvidence) : Bool :=
  match e.deficitYears, e.laborCostOnly with
  | some 0, some true => true
  | _, _ => false

/-- 판례 경계: 성립 패턴이 하나라도 맞으면 충족, 불성립 패턴이 맞으면 위반, 나머지는 보류. -/
def urgentNeedBoundary (e : UrgentNeedEvidence) : Verdict :=
  if patA e || patB e then .satisfied
  else if patC e then .violated
  else .undetermined

/-- 미확정일 때 "이걸 다투려면 무엇을 입증해야 하는가". 방향별로 준다. -/
def urgentNeedBurden (e : UrgentNeedEvidence) : List (String × String) :=
  if urgentNeedBoundary e ≠ .undetermined then [] else
  (if e.deficitYears.isNone then [("성립", "최근 2개 사업연도 이상 연속 적자 — 감사보고서·재무제표")] else []) ++
  (if e.capitalImpaired.isNone then [("성립", "자본잠식 여부 — 재무상태표")] else []) ++
  (if e.divisionClosed.isNone then [("성립", "사업부문 폐지·축소 사실 — 이사회 결의·조직개편 공문")] else []) ++
  (if e.laborCostOnly.isNone then [("불성립", "흑자 상태에서 인건비 절감 외 목적이 없었음 — 경영계획·손익")] else [])

/-- **경계의 무모순**: 같은 증거로 성립·불성립이 동시에 나올 수 없다 (함수이므로 자명하지만 명시). -/
theorem urgentNeed_consistent (e : UrgentNeedEvidence) :
    ¬ (urgentNeedBoundary e = .satisfied ∧ urgentNeedBoundary e = .violated) := by
  intro ⟨h1, h2⟩; rw [h1] at h2; cases h2

/-- **경계가 촘촘한가는 Lean 이 반례로 알려준다**: 증거 4개가 모두 확인됐는데도 판례 경계 밖이면
    미확정이고, 부담 목록도 비어 있다 (더 물을 게 없는데 결론이 없음).
    예: 적자 1년, 자본잠식 아님, 사업부문 폐지 없음, 인건비 절감만 목적 아님.
    → 이런 구멍을 채우는 건 판례를 더 넣는 사람의 일이지 Lean 의 일이 아니다. -/
example : ∃ e : UrgentNeedEvidence,
    urgentNeedBoundary e = .undetermined ∧ urgentNeedBurden e = [] :=
  ⟨{ deficitYears := some 1, capitalImpaired := some false,
     divisionClosed := some false, laborCostOnly := some false }, by decide⟩

/-- 패턴은 "확인된 사실" 만 보므로 증거를 정제해도 유지된다. -/
theorem patA_refines {e e' : UrgentNeedEvidence} (h : e.Refines e') (ha : patA e = true) :
    patA e' = true := by
  obtain ⟨hd, hc, -, -⟩ := h
  unfold patA at *
  cases hdy : e.deficitYears with
  | none => simp [hdy] at ha
  | some n =>
    cases hcy : e.capitalImpaired with
    | none => simp [hdy, hcy] at ha
    | some c =>
      rw [hd n hdy, hc c hcy]; rw [hdy, hcy] at ha
      cases c <;> simp_all

theorem patB_refines {e e' : UrgentNeedEvidence} (h : e.Refines e') (hb : patB e = true) :
    patB e' = true := by
  obtain ⟨hd, -, hv, -⟩ := h
  unfold patB at *
  cases hdy : e.deficitYears with
  | none => simp [hdy] at hb
  | some n =>
    cases hvy : e.divisionClosed with
    | none => simp [hdy, hvy] at hb
    | some v =>
      rw [hd n hdy, hv v hvy]; rw [hdy, hvy] at hb
      cases v <;> simp_all

theorem patC_refines {e e' : UrgentNeedEvidence} (h : e.Refines e') (hc : patC e = true) :
    patC e' = true := by
  obtain ⟨hd, -, -, hl⟩ := h
  unfold patC at *
  cases hdy : e.deficitYears with
  | none => simp [hdy] at hc
  | some n =>
    cases hly : e.laborCostOnly with
    | none => simp [hdy, hly] at hc
    | some l =>
      rw [hd n hdy, hl l hly]; rw [hdy, hly] at hc
      cases n <;> cases l <;> simp_all

/-- 성립 패턴과 불성립 패턴은 서로 배타적이다 (적자 ≥ 1년 vs 적자 0년). -/
theorem patC_excludes_AB (e : UrgentNeedEvidence) (hc : patC e = true) :
    patA e = false ∧ patB e = false := by
  unfold patA patB patC at *
  cases hdy : e.deficitYears with
  | none => simp [hdy] at hc
  | some n =>
    rw [hdy] at hc
    cases n with
    | zero =>
      rcases e.capitalImpaired with _ | (_ | _) <;> rcases e.divisionClosed with _ | (_ | _) <;> simp
    | succ m => cases e.laborCostOnly with
      | none => simp at hc
      | some l => cases l <;> simp at hc

/-- **단조성**: 증거를 더 채워도 확정된 결론은 뒤집히지 않는다. -/
theorem urgentNeed_mono {e e' : UrgentNeedEvidence} (h : e.Refines e') :
    Verdict.refines (urgentNeedBoundary e) (urgentNeedBoundary e') := by
  unfold urgentNeedBoundary
  cases hab : (patA e || patB e) with
  | true =>
    have : (patA e' || patB e') = true := by
      rcases Bool.or_eq_true_iff.mp hab with ha | hb
      · exact Bool.or_eq_true_iff.mpr (Or.inl (patA_refines h ha))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (patB_refines h hb))
    simp [this, Verdict.refines]
  | false =>
    cases hcc : patC e with
    | true =>
      have hc' := patC_refines h hcc
      have ⟨ha', hb'⟩ := patC_excludes_AB e' hc'
      simp [ha', hb', hc', Verdict.refines]
    | false => simp [Verdict.refines]

/-! ## 3. 수치 요건은 그대로 증명 + 평가적 요건 결합 (제24조 종합) -/

structure Art24Facts where
  urgent        : UrgentNeedEvidence
  /-- 제24조③ 근로자대표 통보일부터 해고일까지 일수 (수치 요건: 50일) -/
  repNoticeDays : Nat
  /-- 제24조② 해고 회피 노력 — 여기서는 단순화해 이미 판정된 3값으로 받는다 -/
  avoidance     : Verdict
  deriving Repr

/-- 제24조③ "50일 전까지 통보" — 수치 요건은 2값으로 확정. -/
def art24_3 (days : Nat) : Verdict := Verdict.ofBool (decide (days ≥ 50))

/-- 제24조 종합 (①긴박한 필요 ∧ ②회피노력 ∧ ③50일 통보). -/
def art24 (f : Art24Facts) : Verdict :=
  Verdict.all [urgentNeedBoundary f.urgent, f.avoidance, art24_3 f.repNoticeDays]

/-- **수치 위반은 열린 개념과 무관하게 위반으로 확정된다**: 49일 통보면 긴박한 필요가 있든 없든 위반. -/
theorem art24_violated_of_short_notice (f : Art24Facts) (h : f.repNoticeDays < 50) :
    art24 f = .violated := by
  apply Verdict.all_violated_of_mem
  simp [art24_3, Verdict.ofBool, h]

/-- **충족은 세 요건이 모두 확정 충족일 때만**: 미확정이 하나라도 있으면 충족이라 말하지 않는다. -/
theorem art24_satisfied_iff (f : Art24Facts) :
    art24 f = .satisfied ↔
      urgentNeedBoundary f.urgent = .satisfied ∧ f.avoidance = .satisfied ∧ f.repNoticeDays ≥ 50 := by
  unfold art24
  rw [Verdict.all_satisfied_iff]
  simp [art24_3, Verdict.ofBool]

/-- 미아 메모 사례 ①: 3년 연속 적자 + 자본잠식, 60일 통보, 회피노력은 미확정
    → 전체는 **미확정** (긴박한 필요는 성립 방향으로 확정되지만 ②가 남음). -/
example :
    art24 { urgent := { deficitYears := some 3, capitalImpaired := some true },
            repNoticeDays := 60, avoidance := .undetermined } = .undetermined := by decide

/-- 사례 ②: 흑자·인건비 절감만 목적, 60일 통보, 회피노력 충족 → **위반** 으로 확정. -/
example :
    art24 { urgent := { deficitYears := some 0, laborCostOnly := some true },
            repNoticeDays := 60, avoidance := .satisfied } = .violated := by decide

/-- 사례 ③: 증거가 하나도 없고 40일 통보 → 위반 (수치만으로 확정). -/
example : art24 { urgent := {}, repNoticeDays := 40, avoidance := .undetermined } = .violated := by
  decide

/-! ## 4. 시행일별 버전과 적용 시점 파라미터 -/

structure Date where
  year  : Nat
  month : Nat
  day   : Nat
  deriving DecidableEq, Repr

namespace Date
/-- 사전식 비교. -/
def le (a b : Date) : Bool :=
  a.year < b.year ∨ (a.year = b.year ∧ (a.month < b.month ∨ (a.month = b.month ∧ a.day ≤ b.day)))
def lt (a b : Date) : Bool := le a b ∧ a ≠ b
end Date

/-- 어떤 규칙 `α` 의 시행일별 버전. -/
structure Version (α : Type) where
  effectiveFrom : Date
  rule          : α
  deriving Repr

/-- 적용 시점 `t` 에 시행 중인 버전: 시행일 ≤ t 인 것 중 가장 늦은 것. 없으면 none (시행 전). -/
def pick {α : Type} (vs : List (Version α)) (t : Date) : Option (Version α) :=
  (vs.filter fun v => Date.le v.effectiveFrom t).foldl
    (fun acc v => match acc with
      | none => some v
      | some a => if Date.le a.effectiveFrom v.effectiveFrom then some v else some a) none

/-- **선택된 버전은 항상 적용 시점 이전에 시행된 것이다** (시행 전 법을 적용하지 않는다). -/
theorem pick_effective_le {α : Type} (vs : List (Version α)) (t : Date) (v : Version α)
    (h : pick vs t = some v) : Date.le v.effectiveFrom t = true := by
  unfold pick at h
  generalize hf : vs.filter (fun v => Date.le v.effectiveFrom t) = fs at h
  have hall : ∀ w ∈ fs, Date.le w.effectiveFrom t = true := by
    intro w hw; rw [← hf] at hw; exact (List.mem_filter.mp hw).2
  clear hf
  -- foldl 불변식: 누적값이 some 이면 그 원소는 fs 에서 왔다
  suffices H : ∀ (acc : Option (Version α)),
      (∀ w, acc = some w → Date.le w.effectiveFrom t = true) →
      ∀ w, fs.foldl (fun acc v => match acc with
        | none => some v
        | some a => if Date.le a.effectiveFrom v.effectiveFrom then some v else some a) acc = some w →
        Date.le w.effectiveFrom t = true by
    exact H none (by intro w hw; cases hw) v h
  clear h v
  induction fs with
  | nil => intro acc hacc w hw; exact hacc w hw
  | cons x xs ih =>
    intro acc hacc w hw
    simp only [List.foldl] at hw
    have hx := hall x (List.mem_cons_self ..)
    have hxs : ∀ w ∈ xs, Date.le w.effectiveFrom t = true :=
      fun w hw => hall w (List.mem_cons_of_mem _ hw)
    refine ih hxs _ ?_ w hw
    intro w' hw'
    cases acc with
    | none => cases hw'; exact hx
    | some a =>
      simp only at hw'
      split at hw'
      · cases hw'; exact hx
      · cases hw'; exact hacc _ rfl

/-- 벌칙 (사이트의 Penalties 표를 단순화). 징역 상한(년), 벌금 상한(만원). -/
structure Sanction where
  prisonYears : Nat
  fineManwon  : Nat
  deriving DecidableEq, Repr

/-- 임금 체불 조문 벌칙의 버전 (예: 2026. 10. 상향 — 사이트 코드에 있는 시점 분기를 버전으로 옮긴 것). -/
def wageSanctionVersions : List (Version Sanction) :=
  [ ⟨⟨2021, 11, 19⟩, ⟨3, 3000⟩⟩,   -- 현행
    ⟨⟨2026, 10, 1⟩,  ⟨5, 5000⟩⟩ ]  -- 개정

/-- 경과규정 (형법 제1조① 행위시법, ② 신법이 가벼우면 신법): 행위 시점 버전을 원칙으로 하되
    재판 시점 버전이 더 가벼우면 그것을 적용. -/
def penaltyFor (vs : List (Version Sanction)) (actAt judgedAt : Date) : Option Sanction :=
  match pick vs actAt, pick vs judgedAt with
  | some a, some j =>
    if j.rule.prisonYears ≤ a.rule.prisonYears ∧ j.rule.fineManwon ≤ a.rule.fineManwon
    then some j.rule else some a.rule
  | some a, none => some a.rule
  | none, _ => none   -- 행위 시 처벌 규정 없음 → 처벌 불가 (죄형법정주의)

/-- **적용 형벌은 행위시법을 넘지 않는다** (경과규정의 핵심 보장). -/
theorem penalty_le_act (vs : List (Version Sanction)) (actAt judgedAt : Date) (a : Version Sanction)
    (ha : pick vs actAt = some a) (s : Sanction) (hs : penaltyFor vs actAt judgedAt = some s) :
    s.prisonYears ≤ a.rule.prisonYears ∧ s.fineManwon ≤ a.rule.fineManwon := by
  unfold penaltyFor at hs
  cases hj : pick vs judgedAt with
  | none =>
    simp only [ha, hj, Option.some.injEq] at hs
    subst hs; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | some j =>
    simp only [ha, hj] at hs
    by_cases hle : j.rule.prisonYears ≤ a.rule.prisonYears ∧ j.rule.fineManwon ≤ a.rule.fineManwon
    · rw [if_pos hle, Option.some.injEq] at hs; subst hs; exact hle
    · rw [if_neg hle, Option.some.injEq] at hs; subst hs; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- 2026. 9. 행위 → 2026. 11. 재판: 신법이 더 무거우므로 행위시법(3년/3천만). -/
example : penaltyFor wageSanctionVersions ⟨2026, 9, 9⟩ ⟨2026, 11, 1⟩ = some ⟨3, 3000⟩ := by decide
/-- 2026. 10. 행위 → 5년/5천만. -/
example : penaltyFor wageSanctionVersions ⟨2026, 10, 2⟩ ⟨2027, 1, 1⟩ = some ⟨5, 5000⟩ := by decide
/-- 시행 전(2020) 행위 → 처벌 규정 없음. -/
example : penaltyFor wageSanctionVersions ⟨2020, 1, 1⟩ ⟨2027, 1, 1⟩ = none := by decide

/-! ## 5. 규범 서열과 조약 (헌법 제6조①) -/

inductive NormKind where
  | constitution | treaty | statute | decree | rule | precedent
  deriving DecidableEq, Repr

/-- 효력 서열 (작을수록 상위). 헌법 제6조①: 체결·공포된 조약은 국내법과 **같은** 효력 → 법률과 동순위. -/
def NormKind.rank : NormKind → Nat
  | constitution => 0
  | treaty       => 1
  | statute      => 1
  | decree       => 2
  | rule         => 3
  | precedent    => 4   -- 판례: 규범이 아니라 해석 자료. 여기서는 최하위 참고로만.

structure Norm where
  name     : String
  kind     : NormKind
  enacted  : Date
  /-- 특별법인지 (특별법 우선) -/
  special  : Bool
  /-- 자기집행력: 법원이 이 규범을 **직접** 적용할 수 있는가. 국내법은 항상 true.
      조약은 비준·공포되어도 내용이 추상적이면(ILO 협약 다수, MLC) 이행법을 통해서만 적용된다. -/
  selfExecuting : Bool := true
  deriving Repr, DecidableEq

/-- 직접 적용 가능한 규범인가. 조약이 아니면 항상 가능, 조약이면 자기집행력이 있어야 한다. -/
def Norm.applicable (n : Norm) : Bool := n.kind != .treaty || n.selfExecuting

/-- `a` 가 `b` 에 우선하는가: 상위법 → 특별법 → 신법 순. 동순위 조약·법률은 특별법·신법으로 가른다. -/
def prevails (a b : Norm) : Bool :=
  if a.kind.rank ≠ b.kind.rank then a.kind.rank < b.kind.rank
  else if a.special ≠ b.special then a.special
  else Date.le b.enacted a.enacted

/-- 두 규범 중 실제로 적용할 것. 직접 적용 불가(비자기집행 조약)인 쪽은 제외한 뒤 우선순위로 고른다. -/
def resolve (a b : Norm) : Norm :=
  if !a.applicable then b
  else if !b.applicable then a
  else if prevails a b then a else b

/-- **완전성**: 어떤 두 규범이든 한쪽이 우선한다 (판정이 비는 경우가 없다). -/
theorem prevails_total (a b : Norm) : prevails a b = true ∨ prevails b a = true := by
  unfold prevails
  by_cases hr : a.kind.rank = b.kind.rank
  · simp only [hr, ne_eq, not_true_eq_false, ite_false]
    by_cases hs : a.special = b.special
    · simp only [hs, not_true_eq_false, ite_false]
      -- Date.le 는 전순서
      unfold Date.le
      by_cases h1 : b.enacted.year < a.enacted.year
      · left; simp [h1]
      · by_cases h2 : a.enacted.year < b.enacted.year
        · right; simp [h2]
        · have hy : b.enacted.year = a.enacted.year := by omega
          by_cases h3 : b.enacted.month < a.enacted.month
          · left; simp [hy, h3]
          · by_cases h4 : a.enacted.month < b.enacted.month
            · right; simp [hy, h4]
            · have hm : b.enacted.month = a.enacted.month := by omega
              by_cases h5 : b.enacted.day ≤ a.enacted.day
              · left; simp [hy, hm, h5]
              · right; simp [hy, hm]; omega
    · cases ha : a.special <;> cases hb : b.special <;> simp_all
  · by_cases hlt : a.kind.rank < b.kind.rank
    · left; simp [hr, hlt]
    · right; have : b.kind.rank < a.kind.rank := by omega
      simp [Ne.symm hr, this]

/-- **결과는 둘 중 하나**: 제3의 규범을 만들어내지 않는다. -/
theorem resolve_mem (a b : Norm) : resolve a b = a ∨ resolve a b = b := by
  unfold resolve
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- **비자기집행 조약은 직접 적용되지 않는다**: 상대가 무엇이든 상대가 선택된다. -/
theorem resolve_skips_non_self_executing (a b : Norm) (ha : a.applicable = false) :
    resolve a b = b := by
  unfold resolve; simp [ha]

/-- **적용 가능한 쪽이 하나라도 있으면 결과는 적용 가능하다**. -/
theorem resolve_applicable (a b : Norm) (h : a.applicable = true ∨ b.applicable = true) :
    (resolve a b).applicable = true := by
  unfold resolve
  cases ha : a.applicable <;> cases hb : b.applicable <;> simp_all <;> split <;> simp_all

/-! ### 예시 1 — 해양: IMO 협약 · 선박안전법 · 시행령 (어제 세미나의 "IMO 협약은 글로 돼 있다" 라인) -/

/-- SOLAS 협약. [가정] 자기집행력 있음 — 실제로는 조항별로 다르며, 이 플래그가 법률 검토 사항. -/
def imoConv : Norm := ⟨"SOLAS 협약", .treaty, ⟨1980, 5, 25⟩, true, true⟩
def shipSafetyAct : Norm := ⟨"선박안전법", .statute, ⟨2024, 1, 1⟩, false, true⟩
def shipDecree : Norm := ⟨"선박안전법 시행령", .decree, ⟨2025, 1, 1⟩, true, true⟩

/-- 조약(특별)과 법률(일반)이 동순위로 충돌 → 특별법 우선으로 조약. 법률이 더 최근이어도 같다. -/
example : resolve imoConv shipSafetyAct = imoConv := by decide
/-- 시행령은 조약보다 하위 — 순위에서 바로 결정. -/
example : resolve imoConv shipDecree = imoConv := by decide

/-! ### 예시 2 — 선원 근로: MLC 2006 · 선원법 · 근로기준법

- 근로기준법 = 일반법. 선원법 제5조: 근기법 중 일부 조문만 선원에 적용, 나머지는 선원법.
- 해사노동협약(MLC 2006)은 비준·공포됐지만 **비자기집행** — 선원법 전면개정(2011 통과)으로 이행.
  따라서 선원 사안에 MLC 를 직접 들이대지 않고 선원법을 적용한다. -/

def mlc2006 : Norm := ⟨"2006 해사노동협약(MLC)", .treaty, ⟨2015, 1, 9⟩, true, false⟩
def seafarersAct : Norm := ⟨"선원법", .statute, ⟨2012, 2, 5⟩, true, true⟩
def laborStandardsAct : Norm := ⟨"근로기준법", .statute, ⟨2026, 8, 20⟩, false, true⟩

/-- 선원법(특별) vs 근로기준법(일반, 더 최근) → 특별법 우선으로 선원법. -/
example : resolve seafarersAct laborStandardsAct = seafarersAct := by decide
/-- MLC(비자기집행) vs 선원법 → MLC 는 직접 적용 안 됨, 선원법. 순서를 바꿔도 같다. -/
example : resolve mlc2006 seafarersAct = seafarersAct := by decide
example : resolve seafarersAct mlc2006 = seafarersAct := by decide
/-- 만약 MLC 가 자기집행적이었다면 특별·동순위·신법으로 MLC 가 앞섰을 것 — 플래그 하나가 결론을 바꾼다. -/
example : resolve { mlc2006 with selfExecuting := true } seafarersAct
    = { mlc2006 with selfExecuting := true } := by decide

/-! ### 예시 3 — ILO 핵심협약 (87·98·29호, 2022. 4. 20. 발효) vs 근로기준법
    비준으로 국내법과 같은 효력(헌법 6조①)이지만 자기집행력 논쟁 → 여기서는 false 로 두고,
    법원이 해석 기준으로만 쓰는 현 실무를 그대로 표현. -/
def ilo87 : Norm := ⟨"ILO 제87호 협약", .treaty, ⟨2022, 4, 20⟩, false, false⟩
example : resolve ilo87 laborStandardsAct = laborStandardsAct := by decide

/-! ## 6. 한계 측정용: 미확정 사실의 전수열거 크기 (사이트 방식의 비용) -/

/-- 사이트는 미확정 Bool 키 n 개를 2^n 전수열거해 "결론을 바꾸는 키" 를 찾는다. -/
def enumerationCost (unknowns : Nat) : Nat := 2 ^ unknowns

example : enumerationCost 5 = 32 := by decide      -- 사이트가 진리표를 보여주는 상한
example : enumerationCost 20 = 1048576 := by decide -- 제24조 요건 전부를 Bool 로 두면 이 근처

end LeanLawExt

/-! ## 7. 실행 예시 (`#eval`) — 미아 메모 사례를 3값 + 입증 부담으로 -/

namespace LeanLawExt
-- 사례 ①: 3년 적자 + 자본잠식 → 긴박한 필요 충족 방향 확정
#eval urgentNeedBoundary { deficitYears := some 3, capitalImpaired := some true }
-- 사례 ②: 흑자·인건비 절감만 → 불성립 확정
#eval urgentNeedBoundary { deficitYears := some 0, laborCostOnly := some true }
-- 사례 ③: "경영이 어렵다" 만 있고 증거 없음 → 미확정 + 무엇을 입증해야 하는지
#eval urgentNeedBoundary {}
#eval urgentNeedBurden {}
-- 사례 ④: 적자 1년만 확인 → 미확정, 남은 부담은 자본잠식·사업부문 폐지·목적
#eval urgentNeedBurden { deficitYears := some 1 }
-- 제24조 종합: 사례 ① + 60일 통보 + 회피노력 미확정 → 미확정
#eval art24 { urgent := { deficitYears := some 3, capitalImpaired := some true }, repNoticeDays := 60, avoidance := .undetermined }
-- 벌칙 버전: 2026-09 행위 / 2026-11 재판 → 행위시법 3년·3천만
#eval penaltyFor wageSanctionVersions ⟨2026, 9, 9⟩ ⟨2026, 11, 1⟩
end LeanLawExt
