import PG_lean_0

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace PG

-- ============================================================
--  点几何：Lean 4 / Mathlib 版本（第 1 部分）
--  对应 Coq 文件：A_1.v
--
--  转换约定（Coq -> Lean）：
--    λ（标量变量）         -> a（λ 是 Lean 关键字，不可作标识符）
--    Coq 的 `-- X`         -> -X（在 A_0.v 中 `--` 是 point_inverse 的记号，即单重取反）
--    induction; simpl       -> ext <;> simp [...] <;> ring / nlinarith
--    坐标线性等式           -> nlinarith（linear 与二次均可）
--    含除法等式             -> field_simp <;> nlinarith
-- ============================================================

-- 性质1 若 B = λA，则 O、A、B 共线，且向量 OB = λ * 向量 OA。
theorem point_col (A B : Point) (a : ℝ) :
    a ≠ 0 → B = a *. A → vector O B = a *. vector O A ∧ col B O A := by
  intro ha hB
  constructor
  · rw [hB]
    unfold vector point_minus point_mult O
    ext <;> simp
  · unfold col
    left
    refine ⟨a, ha, ?_⟩
    rw [hB]
    unfold vector point_minus point_mult O
    ext <;> simp

-- 性质2 (1) 若 A+B=P，则 AOBP 为平行四边形。
theorem locate_P_1 (A B P : Point) :
    A ≠ O → B ≠ O → A ≠ B → P = A +. B → Parallelogram A O P B := by
  intro hA hB hAB hP
  unfold Parallelogram
  constructor
  · rw [hP]
    ext <;> simp [vector, point_minus, point_plus, O] <;> ring
  · intro hAP
    apply hB
    have hAeq : A = A +. B := by simpa [← hAP] using hP
    ext
    · have hx := congrArg Point.x hAeq
      simp [point_plus, O] at hx ⊢
      linarith
    · have hy := congrArg Point.y hAeq
      simp [point_plus, O] at hy ⊢
      linarith

theorem locate_P_1' (A B P : Point) : Parallelogram A O P B → P = A +. B := by
  intro h
  rcases h with ⟨hvec, hAP⟩
  ext <;> simp [vector, point_minus, point_plus, O] at hvec ⊢ <;> nlinarith

-- 性质2 (2) 若 A+B=2*P，则 P 为 AB 中点。
lemma Midpoint_tran (A B P : Point) :
    A +. B = 2 *. P ↔ (A +. B) /. 2 = P := by
  constructor
  · intro h
    rw [h]
    ext <;> simp [point_divR, point_mult] <;> ring_nf
  · intro h
    rw [← h]
    ext <;> simp [point_divR, point_mult] <;> ring_nf

theorem locate_P_2 (A B P : Point) :
    A +. B = 2 *. P ↔ Midpoint P A B := by
  constructor
  · intro h
    unfold Midpoint
    ext <;> simp [vector, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith
  · intro h
    unfold Midpoint at h
    ext <;> simp [vector, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

-- 性质2 (3) 若 A+B=3*P，则 P 是 ▲ABO 的重心。
theorem locate_P_3 (A B P : Point) :
    A +. B = 3 *. P → focus P A B O := by
  intro h
  unfold focus v0
  ext <;> simp [vector, point_minus, point_plus, point_mult, O] at h ⊢ <;> nlinarith

theorem locate_P_3' (A B P : Point) :
    focus P A B O → A +. B = 3 *. P := by
  intro h
  unfold focus v0 at h
  ext <;> simp [vector, point_minus, point_plus, point_mult, O] at h ⊢ <;> nlinarith

-- 性质3 两点差为向量：B-A=t*P。
def cons (A B : Point) : Prop :=
  A ≠ O ∧ B ≠ O ∧ A ≠ B → ∃ t P, B -. A = t *. P

-- 当 t=1 时，OABP 为平行四边形。
theorem switch_1 (A B P : Point) :
    A ≠ O → B ≠ O → A ≠ B → B -. A = P → Parallelogram B A P O := by
  intro hA hB hAB hP
  unfold Parallelogram
  constructor
  · unfold vector
    rw [hP]
    simp [point_minus, O]
  · intro hBP
    apply hA
    have hx : A.x = 0 := by
      have hsub := congrArg Point.x (by simpa [hBP] using hP)
      simp [point_minus] at hsub
      linarith
    have hy : A.y = 0 := by
      have hsub := congrArg Point.y (by simpa [hBP] using hP)
      simp [point_minus] at hsub
      linarith
    ext
    · simp [O, hx]
    · simp [O, hy]

theorem switch_1' (A B P : Point) : Parallelogram B A P O → B -. A = P := by
  intro h
  rcases h with ⟨hvec, hBP⟩
  ext <;> simp [vector, point_minus, O] at hvec ⊢ <;> nlinarith

-- 性质4 (1) 若 u*A+v*B=(u+v)*P，则 u*(A-P)=v*(P-B)。
theorem linear_com1 (A B P : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. P → u *.(A -. P) = v *.(P -. B) := by
  intro h
  ext <;> simp [point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

theorem linear_com1' (A B P : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. P → u *. vector A P = v *. vector P B := by
  intro h
  ext <;> simp [vector, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

-- 当 t=u+v 时，令 u*A+v*B=(u+v)*F，此时 F 在直线 AB 上。
theorem linear_com2 (A B P : Point) (u v : ℝ) :
    u ≠ 0 → v ≠ 0 → u *. A +. v *. B = (u + v) *. P → col A P B := by
  intro hu hv h
  have h1 := linear_com1 A B P u v h
  unfold col
  left
  refine ⟨-v / u, ?_, ?_⟩
  · exact div_ne_zero (neg_ne_zero.mpr hv) hu
  · ext
    · have hx := congrArg Point.x h1
      simp [vector, point_minus, point_mult] at hx ⊢
      field_simp [hu]
      nlinarith [hx]
    · have hy := congrArg Point.y h1
      simp [vector, point_minus, point_mult] at hy ⊢
      field_simp [hu]
      nlinarith [hy]

theorem linear_com2' (A B P : Point) :
    col A P B → ∃ u v, u *. A +. v *. P = (u + v) *. B := by
  intro h
  unfold col at h
  rcases h with hvec | heq
  · rcases hvec with ⟨x, hx, hvec⟩
    refine ⟨1, -(1 - x), ?_⟩
    ext <;> simp [point_plus, point_mult, vector, point_minus] at hvec ⊢ <;> nlinarith
  · rcases heq with hAP | hAB | hPB
    · refine ⟨0, 0, ?_⟩
      simp [point_plus, point_mult, hAP]
    · refine ⟨1, 0, ?_⟩
      simp [point_plus, point_mult, hAB]
    · refine ⟨0, 1, ?_⟩
      simp [point_plus, point_mult, hPB]

lemma pplus_minus (A B C : Point) : A -. B = C ↔ A = B +. C := by
  constructor
  · intro h
    ext
    · have hx := congrArg Point.x h
      simp [point_minus, point_plus] at hx ⊢
      linarith
    · have hy := congrArg Point.y h
      simp [point_minus, point_plus] at hy ⊢
      linarith
  · intro h
    ext
    · have hx := congrArg Point.x h
      simp [point_minus, point_plus] at hx ⊢
      linarith
    · have hy := congrArg Point.y h
      simp [point_minus, point_plus] at hy ⊢
      linarith

theorem linear_com2'' (A B P : Point) :
    col A B P → B ≠ P → ∃ u, A = u *. P +. (1 - u) *. B := by
  intro h hBP
  unfold col at h
  rcases h with hvec | heq
  · rcases hvec with ⟨x, hx, hvec⟩
    refine ⟨x, ?_⟩
    ext <;> simp [point_plus, point_mult, vector, point_minus] at hvec ⊢ <;> nlinarith
  · rcases heq with hAB | hAP | hBP'
    · refine ⟨0, ?_⟩
      simp [point_plus, point_mult, O, hAB]
    · refine ⟨1, ?_⟩
      simp [point_plus, point_mult, O, hAP]
    · contradiction

-- 性质4 (2) u*A+v*B=(u+v)*F，一般地 P 是直线 OF 上的点。
theorem linear_com3 (A B P F : Point) (u v t : ℝ) :
    (u + v) ≠ 0 → t ≠ 0 →
    u *. A +. v *. B = t *. P →
    u *. A +. v *. B = (u + v) *. F → col P O F := by
  intro huv ht h1 h2
  have hEq : t *. P = (u + v) *. F := by
    rw [← h1, h2]
  unfold col
  left
  refine ⟨(u + v) / t, ?_, ?_⟩
  · exact div_ne_zero huv ht
  · ext
    · have hx := congrArg Point.x hEq
      simp [vector, point_minus, point_mult, O] at hx ⊢
      field_simp [ht]
      nlinarith [hx]
    · have hy := congrArg Point.y hEq
      simp [vector, point_minus, point_mult, O] at hy ⊢
      field_simp [ht]
      nlinarith [hy]

-- 性质5 两线相交的表示。
def Inter (A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧ ∃ u v r s, u *. A +. v *. B = r *. C +. s *. D

def Inter_p (A B C D X : Point) : Prop :=
  ∀ u v r s, u *. A +. v *. B = r *. C +. s *. D ∧ u + v = r + s ∧ u + v ≠ 0 →
    u *. A +. v *. B = (u + v) *. X

def Inter_p' (A B C D P : Point) : Prop :=
  ∀ a b c d, a + b = c + d ∧ a + b ≠ 0 ∧ (a + b) *. P = a *. A +. b *. B ∧
    (c + d) *. P = c *. C +. d *. D

-- 性质5 (2) 一般情形表示 O、G、F 共线。
theorem TL_relate2 (A B C D F G : Point) (u v r s : ℝ) :
    u + v ≠ 0 → r + s ≠ 0 → u *. A +. v *. B = r *. C +. s *. D →
    (u + v) *. F = u *. A +. v *. B → r *. C +. s *. D = (r + s) *. G →
    col G O F := by
  intro huv hrs h1 h2 h3
  have hEq : (u + v) *. F = (r + s) *. G := by
    rw [h2, h1, h3]
  unfold col
  left
  refine ⟨(u + v) / (r + s), ?_, ?_⟩
  · exact div_ne_zero huv hrs
  · ext
    · have hx := congrArg Point.x hEq
      simp [vector, point_minus, point_mult, O] at hx ⊢
      field_simp [hrs]
      nlinarith [hx]
    · have hy := congrArg Point.y hEq
      simp [vector, point_minus, point_mult, O] at hy ⊢
      field_simp [hrs]
      nlinarith [hy]

lemma Midpoint_p (A B : Point) : Midpoint A O B → B = 2 *. A := by
  intro h
  unfold Midpoint at h
  ext <;> simp [vector, point_minus, point_mult, O] at h ⊢ <;> linarith

lemma Midpoint_p' (A B : Point) : B = 2 *. A → Midpoint A O B := by
  intro h
  unfold Midpoint
  ext
  · have hx := congrArg Point.x h
    simp [vector, point_minus, point_mult, O] at hx ⊢
    linarith
  · have hy := congrArg Point.y h
    simp [vector, point_minus, point_mult, O] at hy ⊢
    linarith

-- 性质6 数量积的交换律与分配律。
lemma Pmagn_comm (A B : Point) : A ·. B = B ·. A := by
  simp [point_magn] <;> ring

lemma Pminus_magn_v (A B C D : Point) :
    (A -. B) ·. (C -. D) = vector A B ·. vector C D := by
  simp [vector, point_minus, point_magn] <;> ring

-- 性质8 AB = -BA。（Coq 中 `-- X` 表示 point_inverse X，即单重取反。）
lemma Oprod_comm (A B : Point) : A /p B = - (B /p A) := by
  change A /p B = point_inverse (B /p A)
  ext <;> simp [point_Oprod, point_minus, point_inverse] <;> ring

-- 性质9 若 u*A+v*B=(u+v)*C，则 u*AP+v*BP=(u+v)*CP。
lemma Oprod_plus_distr (A B C P : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u *.(P /p A) +. v *.(P /p B) = (u + v) *.(P /p C) := by
  intro h
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

lemma Oprod_plus_distr' (A B C P : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u *.(A /p P) +. v *.(B /p P) = (u + v) *.(C /p P) := by
  intro h
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

-- 两端同用 B 做外积：u*AB=(u+v)*CB。
lemma Oprod_B (A B C : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u *.(A /p B) = (u + v) *.(C /p B) := by
  intro h
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

-- 两端同用 C 做外积：u*AC=v*CB。
lemma Oprod_C (A B C : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u *.(A /p C) = v *.(C /p B) := by
  intro h
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith

-- 性质10 原点配平公式。
lemma Oprod_plus_distr_ex (A B C P : Point) (u v r : ℝ) :
    u *. A +. v *. B = r *. C →
    u *. A +. v *. B = r *. C +. (u + v - r) *. O →
    u *.(A /p P) +. v *.(B /p P) = r *.(C /p P) +. (u + v - r) *. P := by
  intro h1 h2
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult, O] at h1 h2 ⊢ <;> nlinarith

lemma Oprod_plus_distr_ex' (A B C P : Point) (u v r : ℝ) :
    u *. A +. v *. B = r *. C →
    u *. A +. v *. B = r *. C +. (u + v - r) *. O →
    u *.(P /p A) +. v *.(P /p B) = r *.(P /p C) -. (u + v - r) *. P := by
  intro h1 h2
  ext <;> simp [point_Oprod, point_minus, point_plus, point_mult, O] at h1 h2 ⊢ <;> nlinarith

-- 特款 (1) 若 A=r*C，则 AP=r*CP+(1-r)*P，且 PA=r*PC-(1-r)*P。
lemma Oprod_plus_distr_sp1 (A C P : Point) (r : ℝ) :
    A = r *. C →
    A /p P = r *.(C /p P) +. (1 - r) *. P ∧ P /p A = r *.(P /p C) -. (1 - r) *. P := by
  intro h
  have hx := congrArg Point.x h
  have hy := congrArg Point.y h
  simp [point_mult] at hx hy
  constructor
  · ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] <;> nlinarith [hx, hy]
  · ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] <;> nlinarith [hx, hy]

-- 特款 (2) 若 u*A=r*C，则 u*AP=r*CP+(u-r)*P，且 u*PA=r*PC-(u-r)*P。
lemma Oprod_plus_distr_sp2 (A C P : Point) (u r : ℝ) :
    u *. A = r *. C →
    u *.(A /p P) = r *.(C /p P) +. (u - r) *. P ∧
    u *.(P /p A) = r *.(P /p C) -. (u - r) *. P := by
  intro h
  have hx := congrArg Point.x h
  have hy := congrArg Point.y h
  simp [point_mult] at hx hy
  constructor
  · ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] <;> nlinarith [hx, hy]
  · ext <;> simp [point_Oprod, point_minus, point_plus, point_mult] <;> nlinarith [hx, hy]

-- 性质11 三外积的循环与反号。
lemma pprod_order (A B C : Point) :
    point_3prod A B C = point_3prod B C A ∧
    point_3prod B C A = point_3prod C A B ∧
    point_3prod C A B = - point_3prod A C B ∧
    point_3prod A C B = point_3prod B A C ∧
    point_3prod B A C = point_3prod C B A := by
  constructor
  · unfold point_3prod <;> ring
  · constructor
    · unfold point_3prod <;> ring
    · constructor
      · unfold point_3prod <;> ring
      · constructor
        · unfold point_3prod <;> ring
        · unfold point_3prod <;> ring

-- 辅助定义：向量的二维外积（叉积），用于三外积线性性质的证明。
def point_cross (u v : Point) : ℝ := u.x * v.y - u.y * v.x

lemma point_cross_scale_r (a : ℝ) (u v : Point) :
    point_cross u (a *. v) = a * point_cross u v := by
  simp [point_cross, point_mult] <;> ring

lemma point_cross_add_r (u v w : Point) :
    point_cross w (u +. v) = point_cross w u + point_cross w v := by
  simp [point_cross, point_plus] <;> ring

lemma point_cross_self (u : Point) : point_cross u u = 0 := by
  simp [point_cross] <;> ring

-- 三外积与叉积的关系：ABC = cross(C-B, A-B)。
lemma pprod_cross (X P Q : Point) :
    point_3prod X P Q = point_cross (Q -. P) (X -. P) := by
  unfold point_3prod point_cross point_minus <;> ring

lemma pprod_col (A B C : Point) : col A B C → point_3prod A B C = 0 := by
  intro h
  unfold col at h
  rcases h with hvec | heq
  · rcases hvec with ⟨x, hx, hvec⟩
    have hdiff : A -. B = x *.(C -. B) := by simpa [vector] using hvec
    rw [pprod_cross A B C]
    rw [hdiff]
    rw [point_cross_scale_r, point_cross_self]
    simp
  · rcases heq with hAB | hAC | hBC
    · rw [hAB]
      unfold point_3prod <;> ring
    · rw [hAC]
      unfold point_3prod <;> ring
    · rw [hBC]
      unfold point_3prod <;> ring

-- 性质12 三外积的分配律。
lemma pprod_distr_eq1 (A B C P Q : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u * point_3prod A P Q + v * point_3prod B P Q = (u + v) * point_3prod C P Q := by
  intro h
  have hvec : u *.(A -. P) +. v *.(B -. P) = (u + v) *.(C -. P) := by
    ext <;> simp [point_minus, point_plus, point_mult] at h ⊢ <;> nlinarith
  rw [pprod_cross A P Q, pprod_cross B P Q, pprod_cross C P Q]
  rw [← point_cross_scale_r]
  rw [← point_cross_scale_r]
  rw [← point_cross_scale_r]
  rw [← point_cross_add_r]
  rw [hvec]

lemma pprod_distr_eq2 (A B C P Q : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u * point_3prod P A Q + v * point_3prod P B Q = (u + v) * point_3prod P C Q := by
  intro h
  have h1 := pprod_order P A Q
  have h2 := pprod_order P B Q
  have h3 := pprod_order P C Q
  rw [h1.1, h2.1, h3.1]
  exact pprod_distr_eq1 A B C Q P u v h

lemma pprod_distr_eq3 (A B C P Q : Point) (u v : ℝ) :
    u *. A +. v *. B = (u + v) *. C →
    u * point_3prod P Q A + v * point_3prod P Q B = (u + v) * point_3prod P Q C := by
  intro h
  have h1 := pprod_order P Q A
  have h2 := pprod_order P Q B
  have h3 := pprod_order P Q C
  rw [h1.1, h1.2.1, h2.1, h2.2.1, h3.1, h3.2.1]
  exact pprod_distr_eq1 A B C P Q u v h

-- 共边定理。
lemma pprod_distr_uneq (A B C D F : Point) (u v r s : ℝ) :
    u + v = r + s → u + v ≠ 0 →
    (u + v) *. F = u *. A +. v *. B →
    (u + v) *. F = r *. C +. s *. D →
    u * point_3prod A C D + v * point_3prod B C D = 0 := by
  intro huv hneq h1 h2
  have h3 : (u + v) * point_3prod F C D = u * point_3prod A C D + v * point_3prod B C D := by
    symm
    exact pprod_distr_eq1 A B F C D u v h1.symm
  have h4' : (r + s) * point_3prod F C D = r * point_3prod C C D + s * point_3prod D C D := by
    symm
    exact pprod_distr_eq1 C D F C D r s (by simpa [huv] using h2.symm)
  have h4 : (u + v) * point_3prod F C D = r * point_3prod C C D + s * point_3prod D C D := by
    rw [← huv] at h4'
    exact h4'
  have h5 : r * point_3prod C C D + s * point_3prod D C D = 0 := by
    unfold point_3prod <;> ring
  rw [← h3]
  rw [h4]
  exact h5

-- 性质13 原点配平的三外积公式。
lemma pprod_distr_uneq_trim (A B C P Q : Point) (u v r : ℝ) :
    u *. A +. v *. B = r *. C →
    u * point_3prod A P Q + v * point_3prod B P Q =
      r * point_3prod C P Q + (u + v - r) * point_3prod O P Q := by
  intro h
  have hvec : u *.(A -. P) +. v *.(B -. P) = r *.(C -. P) +. (u + v - r) *.(O -. P) := by
    ext <;> simp [point_minus, point_plus, point_mult, O] at h ⊢ <;> nlinarith
  rw [pprod_cross A P Q, pprod_cross B P Q, pprod_cross C P Q, pprod_cross O P Q]
  rw [← point_cross_scale_r]
  rw [← point_cross_scale_r]
  rw [← point_cross_scale_r]
  rw [← point_cross_scale_r]
  rw [← point_cross_add_r]
  rw [hvec]
  rw [← point_cross_add_r]

-- 特款：若原点在直线 PQ 上，则附加的配平项为 0。
lemma pprod_distr_uneq_trim' (A B C P Q : Point) (u v r : ℝ) :
    u *. A +. v *. B = r *. C → col O P Q →
    u * point_3prod A P Q + v * point_3prod B P Q = r * point_3prod C P Q := by
  intro h hcol
  have htrim := pprod_distr_uneq_trim A B C P Q u v r h
  have h0 : point_3prod O P Q = 0 := pprod_col O P Q hcol
  rw [htrim, h0]
  simp

-- 性质14 i(iA)=-A。（Coq 中 `-- A` 表示 point_inverse A。）
lemma point_mult_ii (A : Point) : point_mult_i (point_mult_i A) = -A := by
  change point_mult_i (point_mult_i A) = point_inverse A
  ext <;> simp [point_mult_i, point_inverse] <;> ring

-- 性质15 iA·A=0。
lemma point_mult_i_inprod (A : Point) : (i*. A) ·. A = 0 := by
  simp [point_mult_i, point_magn] <;> ring

-- 性质16 iA·B = -A·iB。
lemma point_mult_i_opp (A B : Point) : (i*. A) ·. B = -(A ·. (i*. B)) := by
  simp [point_mult_i, point_magn] <;> ring

-- ============================================================
--  性质 17–20 及辅助引理（对应 A_1.v 后半部分）
--  （Coq 的 exp 定义已在 PG_lean_0 中给出，不再重复定义）
-- ============================================================

-- A 绕原点旋转 theta 弧度。
def PrO (theta : ℝ) (A : Point) : Point := exp theta */c A

-- 性质17 复数乘点的几何意义：A = (x, y) 时，
-- exp θ */c A = (x cos θ - y sin θ, y cos θ + x sin θ)。
theorem property17 (A : Point) (x y theta : ℝ) :
    A = Point.mk x y →
    exp theta */c A =
      Point.mk (x * Real.cos theta - y * Real.sin theta)
               (y * Real.cos theta + x * Real.sin theta) := by
  intro h
  subst h
  ext <;> simp [exp, point_mult_complex, point_mult, point_mult_i, point_plus] <;> ring

-- 性质18 A 绕点 B 反时针旋转 theta 弧度得到的点。
def PrP (A B : Point) (theta : ℝ) : Point := B +. exp theta */c (A -. B)

-- 性质19 复数乘点的运算法则：(α+β)A = αA+βA。
lemma Complex_mult_ppdistr (c1 c2 : Complex) (A : Point) :
    (c1 +/C c2) */c A = c1 */c A +. c2 */c A := by
  ext <;> simp [point_mult_complex, point_mult, point_mult_i, point_plus, Cplus, Cmult] <;> ring

-- 性质19 α(A+B) = αA+αB。
lemma Complex_mult_pcdistr (c : Complex) (A B : Point) :
    c */c (A +. B) = c */c A +. c */c B := by
  ext <;> simp [point_mult_complex, point_mult, point_mult_i, point_plus, Cmult] <;> ring

lemma Cmult_comm (c1 c2 : Complex) : c1 */C c2 = c2 */C c1 := by
  unfold Cmult
  rw [Complex.mk.injEq]
  exact ⟨by ring, by ring⟩

-- 性质19 α(βA) = (αβ)A。
lemma Complex_mult_passoc1 (c1 c2 : Complex) (A : Point) :
    c1 */c (c2 */c A) = (c1 */C c2) */c A := by
  ext <;> simp [point_mult_complex, point_mult, point_mult_i, point_plus, Cmult] <;> ring

lemma Complex_mult_passoc (c1 c2 : Complex) (A : Point) :
    c1 */c (c2 */c A) = (c1 */C c2) */c A ∧
    c1 */c (c2 */c A) = c2 */c (c1 */c A) ∧
    (c1 */C c2) */c A = c2 */c (c1 */c A) := by
  constructor
  · exact Complex_mult_passoc1 c1 c2 A
  · constructor
    · rw [Complex_mult_passoc1 c1 c2 A, Complex_mult_passoc1 c2 c1 A, Cmult_comm c1 c2]
    · rw [Complex_mult_passoc1 c2 c1 A, Cmult_comm c1 c2]

-- A—B—C 逆时针方向。
def PrP_order (A B C : Point) : Prop := point_3prod A B C > 0

-- A—B—C 顺时针方向。
def PrP_order' (A B C : Point) : Prop := point_3prod A B C < 0

-- （性质20 的 ThirdP 定义及其平凡重述已删除，真定理见 Morley/property20_Morley.lean。）

lemma sin2_cos2' (x : ℝ) : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x

-- 辅助引理：点 X 到原点距离的平方 = X.x² + X.y²。
lemma point_sqr_O_minus (X : Point) : point_sqr (O -. X) = X.x ^ 2 + X.y ^ 2 := by
  simp [point_sqr, point_magn, point_minus, O] <;> ring

-- 旋转模长不变。
lemma r_length (A : Point) (theta : ℝ) :
    gap O (exp theta */c A) = gap O A := by
  have hsc := sin2_cos2' theta
  have hx : (exp theta */c A).x = Real.cos theta * A.x - Real.sin theta * A.y := by
    simp [exp, point_mult_complex, point_mult, point_mult_i, point_plus] <;> ring
  have hy : (exp theta */c A).y = Real.cos theta * A.y + Real.sin theta * A.x := by
    simp [exp, point_mult_complex, point_mult, point_mult_i, point_plus] <;> ring
  unfold gap
  rw [Real.sqrt_inj]
  · rw [point_sqr_O_minus, point_sqr_O_minus, hx, hy]
    linear_combination (A.x ^ 2 + A.y ^ 2) * hsc
  · rw [point_sqr_O_minus]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [point_sqr_O_minus]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma exp_mult (a b : ℝ) : exp a */C exp b = exp (a + b) := by
  unfold exp Cmult
  rw [Complex.mk.injEq, Real.cos_add, Real.sin_add]
  exact ⟨rfl, by ring⟩

lemma exp_period (theta : ℝ) (k : ℕ) :
    exp (theta + 2 * (k : ℝ) * Real.pi) = exp theta := by
  unfold exp
  have h : 2 * (k : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) := by ring
  rw [h, (Real.sin_periodic.nat_mul k theta), (Real.cos_periodic.nat_mul k theta)]

lemma exp_period' (theta : ℝ) : exp (theta + 2 * Real.pi) = exp theta := by
  unfold exp
  rw [(Real.sin_periodic theta), (Real.cos_periodic theta)]

lemma CPmult_exc (a : ℝ) (b c : Complex) (D : Point) :
    a *. (b */C c */c D) = b */c (a *. (c */c D)) := by
  ext <;> simp [point_mult_complex, point_mult, point_mult_i, point_plus, Cmult] <;> ring

lemma exp_0 : exp 0 = R_R_to_C 1 0 := by
  unfold exp R_R_to_C
  rw [Real.cos_zero, Real.sin_zero]

lemma exp_multP (theta : ℝ) (A : Point) :
    exp theta */C exp (-theta) */c A = A := by
  rw [exp_mult]
  have h0 : theta + -theta = 0 := by ring
  rw [h0, exp_0]
  ext <;> simp [R_R_to_C, point_mult_complex, point_mult, point_mult_i, point_plus] <;> ring

lemma reverse (a b : ℝ) (h : a = b) : -a = -b := by
  rw [h]

-- 共线关系对三点的置换：col A B C → col C B A。
lemma col_exc (A B C : Point) : col A B C → col C B A := by
  intro h
  unfold col at h ⊢
  rcases h with ⟨x, hx, hvec⟩ | heq
  · refine Or.inl ⟨1 / x, div_ne_zero one_ne_zero hx, ?_⟩
    unfold vector at hvec ⊢
    rw [hvec, pmult_l_l_p]
    have h1 : 1 / x * x = 1 := by field_simp
    rw [h1, pmult_1_p]
  · rcases heq with hAB | hAC | hBC
    · exact Or.inr (Or.inr (Or.inr hAB.symm))
    · exact Or.inr (Or.inr (Or.inl hAC.symm))
    · exact Or.inr (Or.inl hBC.symm)

-- 共线关系对三点的置换：col A B C → col C A B。
lemma col_exc' (A B C : Point) : col A B C → col C A B := by
  intro h
  unfold col at h ⊢
  rcases h with ⟨x, hx, hvec⟩ | heq
  · by_cases hx1 : x = 1
    · subst hx1
      rw [pmult_1_p] at hvec
      have hAC : A = C := by
        ext
        · have h5 := congrArg Point.x hvec
          simp [vector, point_minus] at h5 ⊢
          linarith
        · have h5 := congrArg Point.y hvec
          simp [vector, point_minus] at h5 ⊢
          linarith
      exact Or.inr (Or.inl hAC.symm)
    · refine Or.inl ⟨(x - 1) / x, div_ne_zero (sub_ne_zero_of_ne hx1) hx, ?_⟩
      unfold vector at hvec ⊢
      ext
      · have h5 := congrArg Point.x hvec
        simp only [point_minus, point_mult] at h5 ⊢
        -- h5 : A.x - B.x = x * (C.x - B.x)，目标：C.x - A.x = (x-1)/x * (B.x - A.x)
        have key : (x - 1) * (B.x - A.x) = x * (C.x - A.x) := by
          linear_combination h5
        field_simp
        linear_combination key.symm
      · have h6 := congrArg Point.y hvec
        simp only [point_minus, point_mult] at h6 ⊢
        have key : (x - 1) * (B.y - A.y) = x * (C.y - A.y) := by
          linear_combination h6
        field_simp
        linear_combination key.symm
  · rcases heq with hAB | hAC | hBC
    · exact Or.inr (Or.inr (Or.inr hAB))
    · exact Or.inr (Or.inl hAC.symm)
    · exact Or.inr (Or.inr (Or.inl hBC.symm))

-- 共线关系对三点的置换：col A B C → col A C B。
lemma col_exc'' (A B C : Point) : col A B C → col A C B := by
  intro h
  unfold col at h ⊢
  rcases h with ⟨x, hx, hvec⟩ | heq
  · by_cases hx1 : x = 1
    · subst hx1
      rw [pmult_1_p] at hvec
      have hAC : A = C := by
        ext
        · have h5 := congrArg Point.x hvec
          simp [vector, point_minus] at h5 ⊢
          linarith
        · have h5 := congrArg Point.y hvec
          simp [vector, point_minus] at h5 ⊢
          linarith
      exact Or.inr (Or.inl hAC)
    · refine Or.inl ⟨1 - x, sub_ne_zero_of_ne (Ne.symm hx1), ?_⟩
      unfold vector at hvec ⊢
      ext
      · have h1 := congrArg Point.x hvec
        simp only [point_minus, point_mult] at h1 ⊢
        linear_combination h1
      · have h2 := congrArg Point.y hvec
        simp only [point_minus, point_mult] at h2 ⊢
        linear_combination h2
  · rcases heq with hAB | hAC | hBC
    · exact Or.inr (Or.inr (Or.inl hAB))
    · exact Or.inr (Or.inl hAC)
    · exact Or.inr (Or.inr (Or.inr hBC.symm))

end PG
