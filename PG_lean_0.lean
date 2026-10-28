import Mathlib

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace PG

-- ============================================================
--  点几何：Lean 4 / Mathlib 版本
--  对应 Coq 文件：A_0.v
--
--  转换约定（Coq -> Lean）：
--    pair / (x, y)      -> Point 结构体（字段 x, y），构造器 Point.mk
--    -- A（点的相反）     -> -A（利用 Neg 实例）
--    λ *. A（数乘）       -> a *. A（λ 是 Lean 关键字，标量改用 a）
--    A ·. B（数量积）     -> A ·. B
--    [u, v]（复数）       -> 结构体 Complex（字段 re, im）
--    Rsqr x             -> x ^ 2
--    sqrt / acos / PI   -> Real.sqrt / Real.arccos / Real.pi
--    Coq 的 induction; unfold; ring
--                       -> ext <;> simp [...] <;> ring
-- ============================================================

-- 点的定义
@[ext] structure Point where
  x : ℝ
  y : ℝ

def O : Point := { x := 0, y := 0 }

def point_inverse (A : Point) : Point := { x := -A.x, y := -A.y }

instance : Neg Point where
  neg := point_inverse

theorem point_eq (A B : Point) (x1 y1 x2 y2 : ℝ) :
    (A = Point.mk x1 y1 ∧ B = Point.mk x2 y2) → (A = B ↔ x1 = x2 ∧ y1 = y2) := by
  rintro ⟨hA, hB⟩
  subst A
  subst B
  constructor
  · intro h
    exact ⟨congrArg Point.x h, congrArg Point.y h⟩
  · rintro ⟨hx, hy⟩
    subst x1
    subst y1
    rfl

-- 点的加法
def point_plus (A B : Point) : Point := { x := A.x + B.x, y := A.y + B.y }

infixl:65 " +. " => point_plus

theorem pplus_comm (A B : Point) : A +. B = B +. A := by
  ext <;> simp [point_plus] <;> ring

theorem pplus_assoc (A B C : Point) : (A +. B) +. C = A +. (B +. C) := by
  ext <;> simp [point_plus] <;> ring

theorem pplus_assoc' (A B C : Point) : A +. B +. C = A +. (B +. C) := by
  ext <;> simp [point_plus] <;> ring

theorem pplus_O_p (A : Point) : O +. A = A := by
  ext <;> simp [O, point_plus]

theorem pplus_O_p' (A : Point) : A +. O = A := by
  ext <;> simp [O, point_plus]

-- 点的数乘
def point_mult (a : ℝ) (A : Point) : Point := { x := a * A.x, y := a * A.y }

infixl:70 " *. " => point_mult

theorem pmult_0_p (A : Point) : 0 *. A = O := by
  ext <;> simp [O, point_mult]

theorem pmult_1_p (A : Point) : 1 *. A = A := by
  ext <;> simp [point_mult]

theorem pmult_l_l_p (A : Point) (a b : ℝ) : a *. (b *. A) = (a * b) *. A := by
  ext <;> simp [point_mult, mul_assoc]

theorem pmult_opp_p (A : Point) : (-1) *. A = -A := by
  change (-1) *. A = point_inverse A
  ext <;> simp [point_mult, point_inverse] <;> ring

theorem pmult_opp_p' (A : Point) (a : ℝ) : (-a) *. A = - (a *. A) := by
  change (-a) *. A = point_inverse (a *. A)
  ext <;> simp [point_mult, point_inverse] <;> ring

theorem pmult_0_l (a : ℝ) : a *. O = O := by
  ext <;> simp [O, point_mult]

theorem pmult_plus_distr_l (a : ℝ) (A B : Point) : a *. (A +. B) = a *. A +. a *. B := by
  ext <;> simp [point_mult, point_plus, mul_add]

theorem pmult_plus_distr_l' (a b : ℝ) (A : Point) : (a + b) *. A = a *. A +. b *. A := by
  ext <;> simp [point_mult, point_plus, add_mul]

theorem pmult_plus_distr_l'' (a : ℝ) (A : Point) : (a + 1) *. A = a *. A +. A := by
  ext <;> simp [point_mult, point_plus] <;> ring

-- 点的数除
def point_divR (a : ℝ) (A : Point) : Point := { x := A.x / a, y := A.y / a }

infixl:70 " /. " => fun A a => point_divR a A

-- 点的减法
def point_minus (A B : Point) : Point := { x := A.x - B.x, y := A.y - B.y }

infixl:65 " -. " => point_minus

theorem pminus_O (A : Point) : A -. O = A := by
  ext <;> simp [O, point_minus]

theorem pminus_O_A (A : Point) : O -. A = -A := by
  change O -. A = point_inverse A
  ext <;> simp [O, point_minus, point_inverse]

theorem pminus_eq_O (A : Point) : A -. A = O := by
  ext <;> simp [O, point_minus]

theorem pmult_minus_distr (a : ℝ) (A B : Point) : a *. (A -. B) = a *. A -. a *. B := by
  ext <;> simp [point_mult, point_minus] <;> ring

theorem pmult_minus_distr' (a b : ℝ) (A : Point) : (a - b) *. A = a *. A -. b *. A := by
  ext <;> simp [point_mult, point_minus] <;> ring

theorem pmult_minus_opp (A B : Point) : (-1) *. (A -. B) = B -. A := by
  ext <;> simp [point_mult, point_minus] <;> ring

theorem pmult_minus_opp' (A B : Point) (a : ℝ) : (-a) *. (A -. B) = a *. (B -. A) := by
  ext <;> simp [point_mult, point_minus] <;> ring

theorem pplus_minus_tran (A B : Point) : A +. (-B) = A -. B := by
  change A +. point_inverse B = A -. B
  ext <;> simp [point_plus, point_minus, point_inverse] <;> ring

theorem pplus_minus_tran' (A B : Point) : (-A) +. B = B -. A := by
  change point_inverse A +. B = B -. A
  ext <;> simp [point_plus, point_minus, point_inverse] <;> ring

theorem pplus_minus_assoc (A B C : Point) : (A +. B) -. C = A +. (B -. C) := by
  ext <;> simp [point_plus, point_minus] <;> ring

theorem pplus_minus_assoc' (A B C : Point) : (A -. B) +. C = A -. (B -. C) := by
  ext <;> simp [point_plus, point_minus] <;> ring

theorem pmult_minus_distr_l (a : ℝ) (A B : Point) : a *. (A -. B) = a *. A -. a *. B := by
  ext <;> simp [point_mult, point_minus] <;> ring

-- 点的数量积
def point_magn (A B : Point) : ℝ := A.x * B.x + A.y * B.y

infixl:70 " ·. " => point_magn

theorem Pmagn_minus_distr (A B C : Point) : A ·. (B -. C) = A ·. B - A ·. C := by
  simp [point_magn, point_minus] <;> ring

theorem Pmagn_minus_distr' (A B C : Point) : (B -. C) ·. A = B ·. A - C ·. A := by
  simp [point_magn, point_minus] <;> ring

theorem Pmagn_minus3_distr (A B C D : Point) : (A -. B -. C) ·. D = A ·. D - B ·. D - C ·. D := by
  simp [point_magn, point_minus] <;> ring

theorem Pmagn_plus_distr (A B C : Point) : A ·. (B +. C) = A ·. B + A ·. C := by
  simp [point_magn, point_plus] <;> ring

theorem Pmagn_plus_distr' (A B C : Point) : (A +. B) ·. C = A ·. C + B ·. C := by
  simp [point_magn, point_plus] <;> ring

theorem Pmagn_mult_assoc (a : ℝ) (A B : Point) : (a *. A) ·. B = a * (A ·. B) := by
  simp [point_magn, point_mult] <;> ring

theorem Pmagn_mult_assoc' (a : ℝ) (A B : Point) : A ·. (a *. B) = a * (A ·. B) := by
  simp [point_magn, point_mult] <;> ring

theorem Pmagn_minus_0 (A B : Point) : A ·. B - A ·. B = 0 := by
  simp [point_magn] <;> ring

-- 向量的定义
def vector (A B : Point) : Point := B -. A
def v0 : Point := vector O O

-- 记A²=A·A，则(A—B)²=|AB|²，而A²为点A到原点距离的平方。
-- 当A和B都不是原点时，A·B=0表示∠AOB为直角；(A-B)·(C-D)=0表示向量AB⊥向量CD。

def point_sqr (A : Point) : ℝ := A ·. A
def gap_sqr (A B : Point) : ℝ := point_sqr (A -. B)
def gap (A B : Point) : ℝ := Real.sqrt (point_sqr (A -. B))
def Per (A O B : Point) : Prop := A ≠ O ∧ B ≠ O ∧ A ·. B = 0
def Perp (A B C D : Point) : Prop := (A -. B) ·. (C -. D) = 0

theorem gap_sqr_O (A : Point) : gap_sqr A O = point_sqr A := by
  simp [gap_sqr, point_sqr, pminus_O]

theorem gap_O (A : Point) : gap A O = Real.sqrt (point_sqr A) := by
  simp [gap, point_sqr, pminus_O]

theorem sqr_incr_0 (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by
  exact add_nonneg (sq_nonneg a) (sq_nonneg b)

theorem sqr_0 {a : ℝ} (h : a ≠ 0) : a ^ 2 ≠ 0 := by
  exact pow_ne_zero 2 h

theorem gap_to_sqr (A B : Point) : (gap A B) ^ 2 = gap_sqr A B := by
  unfold gap gap_sqr point_sqr point_minus point_magn
  change (Real.sqrt ((A.x - B.x) * (A.x - B.x) + (A.y - B.y) * (A.y - B.y))) ^ 2 =
         (A.x - B.x) * (A.x - B.x) + (A.y - B.y) * (A.y - B.y)
  rw [Real.sq_sqrt]
  exact add_nonneg (mul_self_nonneg (A.x - B.x)) (mul_self_nonneg (A.y - B.y))

theorem gap_to_sqr_O (A : Point) : (gap A O) ^ 2 = point_sqr A := by
  rw [gap_to_sqr, gap_sqr_O]

-- 三点共线
def col (A B C : Point) : Prop :=
  (∃ a : ℝ, a ≠ 0 ∧ vector B A = a *. vector B C) ∨ (A = B ∨ A = C ∨ B = C)

-- 两点的外积
def point_Oprod (A B : Point) : Point := B -. A

infixl:70 " /p " => point_Oprod

theorem Oprod_l_l (P : Point) : P /p P = O := by
  simp [point_Oprod, O, pminus_eq_O]

theorem Oprod_O_l (P : Point) : P = O /p P := by
  ext <;> simp [point_Oprod, O, point_minus]

theorem Oprod_O_l_mult (P : Point) (u : ℝ) : u *. P = u *. (O /p P) := by
  ext <;> simp [point_Oprod, O, point_minus, point_mult]

theorem Oprod_O_l' (P : Point) : P = - (P /p O) := by
  change P = point_inverse (P /p O)
  ext <;> simp [point_Oprod, O, point_minus, point_inverse]

theorem Oprod_O_l'_mult (P : Point) (u : ℝ) : u *. P = - (u *. (P /p O)) := by
  change u *. P = point_inverse (u *. (P /p O))
  ext <;> simp [point_Oprod, O, point_minus, point_inverse, point_mult]

-- 三点的外积
def point_3prod (A B C : Point) : ℝ :=
  A.x * B.y + B.x * C.y + C.x * A.y - A.x * C.y - B.x * A.y - C.x * B.y

notation A:60 " /e " B:60 " /e " C:60 => point_3prod A B C

-- 复数乘点
def point_mult_i (A : Point) : Point := { x := -A.y, y := A.x }

notation "i*. " A => point_mult_i A

-- 复数定义
structure Complex where
  re : ℝ
  im : ℝ

def R_R_to_C (a b : ℝ) : Complex := { re := a, im := b }

def Cre (c : Complex) : ℝ := c.re

def Cim (c : Complex) : ℝ := c.im

def Creal (c : Complex) : ℝ := Real.sqrt (c.re ^ 2 + c.im ^ 2)

def Cplus (c1 c2 : Complex) : Complex := { re := c1.re + c2.re, im := c1.im + c2.im }

infixl:60 " +/C " => Cplus

def Cminus (c1 c2 : Complex) : Complex := { re := c1.re - c2.re, im := c1.im - c2.im }

def Cmult (c1 c2 : Complex) : Complex :=
  { re := c1.re * c2.re - c1.im * c2.im, im := c1.re * c2.im + c1.im * c2.re }

infixl:70 " */C " => Cmult

def Cinv (c : Complex) : Complex :=
  { re := c.re / (c.re * c.re + c.im * c.im),
    im := -c.im / (c.re * c.re + c.im * c.im) }

def Cdiv (c1 c2 : Complex) : Complex := Cmult c1 (Cinv c2)

infixl:70 " /C " => Cdiv

-- 复数乘点
def point_mult_complex (A : Point) (α : Complex) : Point :=
  α.re *. A +. α.im *. (i*. A)

infixl:70 " */c " => fun α A => point_mult_complex A α

-- 复指数定义
def exp (theta : ℝ) : Complex := { re := Real.cos theta, im := Real.sin theta }

-- 角度α = ∠CAB定义
def angle (C A B : Point) : ℝ :=
  let AB := B -. A
  let AC := C -. A
  Real.arccos ((AB ·. AC) / (gap A B * gap A C))

-- ============================================================
--  三角形内角和（原为公理，现改为定理：由 Mathlib 桥接证明）
--  思路：Point 经坐标嵌入 pointE : Point → EuclideanSpace ℝ 2；
--  PG 的 angle 与 Mathlib 的 EuclideanGeometry.angle 是同一个 arccos 公式
--  （内积角 = arccos(⟪x,y⟫/(‖x‖‖y‖))），故内角和直接由
--  EuclideanGeometry.angle_add_angle_add_angle_eq_pi 导出。
-- ============================================================

/-- 坐标嵌入：Point → EuclideanSpace ℝ (Fin 2) -/
def pointE (P : Point) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![P.x, P.y]

-- 嵌入单射
theorem pointE_inj {P Q : Point} (h : pointE P = pointE Q) : P = Q := by
  have h0 : P.x = Q.x := by
    have h0 : (pointE P).ofLp = (pointE Q).ofLp := congrArg WithLp.ofLp h
    have h1 := congrFun h0 (0 : Fin 2)
    simpa only [pointE, WithLp.ofLp_toLp, Matrix.cons_val_zero] using h1
  have h1 : P.y = Q.y := by
    have h0 : (pointE P).ofLp = (pointE Q).ofLp := congrArg WithLp.ofLp h
    have h1 := congrFun h0 (1 : Fin 2)
    simpa only [pointE, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons] using h1
  ext
  · exact h0
  · exact h1

-- 嵌入后的差的内积 = PG 的点积
theorem pointE_sub_inner (A B C : Point) :
    @inner ℝ _ _ (pointE C - pointE A) (pointE B - pointE A) = (B -. A) ·. (C -. A) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, WithLp.ofLp_sub, pointE, WithLp.ofLp_toLp,
    Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    RCLike.inner_apply, conj_trivial, point_minus, point_magn]

-- 嵌入后的差的范数 = PG 的 gap
theorem pointE_sub_norm (A B : Point) : ‖pointE B - pointE A‖ = gap A B := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, WithLp.ofLp_sub, pointE, WithLp.ofLp_toLp, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Real.norm_eq_abs, sq_abs,
    gap, point_sqr, point_minus, point_magn]
  congr 1
  ring

-- 桥接引理：PG.angle 与 Mathlib 的 EuclideanGeometry.angle 相同
theorem angle_eq_euclid (C A B : Point) :
    angle C A B = EuclideanGeometry.angle (pointE C) (pointE A) (pointE B) := by
  show Real.arccos ((B -. A) ·. (C -. A) / (gap A B * gap A C))
      = Real.arccos (@inner ℝ _ _ (pointE C - pointE A) (pointE B - pointE A)
        / (‖pointE C - pointE A‖ * ‖pointE B - pointE A‖))
  rw [pointE_sub_inner]
  simp only [pointE_sub_norm, mul_comm (gap A C) (gap A B)]

-- 三角形内角和等于180度（定理，非公理）
theorem angle_sum : ∀ (A B C : Point), ¬ col A B C →
  angle C A B = Real.pi - angle A B C - angle A C B := by
  intro A B C hcol
  have hAC : A ≠ C := fun h => hcol (Or.inr (Or.inr (Or.inl h)))
  have hEAC : pointE A ≠ pointE C := fun h => hAC (pointE_inj h)
  rw [angle_eq_euclid C A B, angle_eq_euclid A B C, angle_eq_euclid A C B]
  rw [EuclideanGeometry.angle_comm (pointE A) (pointE C) (pointE B)]
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (P := EuclideanSpace ℝ (Fin 2))
    (p₃ := pointE B) hEAC
  linarith

-- 正三角形定义
def Etri (P Q R : Point) : Prop :=
  ¬ col P Q R ∧ Q = R +. (exp (Real.pi / 3) */c (P -. R))

-- 中点
def Midpoint (M A B : Point) : Prop := vector M A = vector B M

-- 重心
def focus (P A B C : Point) : Prop := vector P A +. vector P B +. vector P C = v0

-- 垂心
def orthocenter (P A B C : Point) : Prop :=
  vector P A ·. vector P B = vector P B ·. vector P C ∧
  vector P B ·. vector P C = vector P C ·. vector P A

-- 平行四边形：一组对边平行且相等。
def Parallelogram (A B C D : Point) : Prop := vector B A = vector D C ∧ A ≠ C

-- AC与BD互相平分
def Plg (M A B C D : Point) : Prop := (A ≠ C ∨ B ≠ D) ∧ Midpoint M A C ∧ Midpoint M B D

-- 三角形
def Triangle (A B C : Point) : Prop := ¬ col A B C

-- 垂直平分线
def Perp_bisect (X P Q A B : Point) : Prop :=
  (Midpoint X A B ∧ col P Q X) ∧ Perp P Q A B ∧ A ≠ B

-- 分角线
def Angle_div (E O B C : Point) : Prop :=
  (gap C O) *. B +. (gap B O) *. C = (gap B O + gap C O) *. E

-- 中位线
def Mid_line (D E A B C : Point) : Prop := Midpoint D A B ∧ Midpoint E A C

-- ============================================================
-- 以下为原 Coq 文件中被注释掉的代码，保留为注释（未转换）：
-- ============================================================
/-
(* Definition cos1 B A C := (A -.B) ·.(A -.C) / (gap A B * gap A C).
Definition sin1_sqr B A C := 1 - (cos1 B A C)².  *)
-/

/-
(* Definition Cconj c := match c with [a,b] => [a,-b] end.
Definition Cnorm_sqr c := match c with [a,b] => [a*a,b*b] end.
Definition Cnorm c := match c with [a,b] => [sqrt(a*a),sqrt(b*b)] end.
Definition Copp c := match c with [a,b] => [-a,-b] end.
Definition Cscal (λ : R) c := match c with [a,b] => [λ*a,λ*b] end.
(* Infix " '+i' " := R_R_to_C (at level 60). *) *)
-/

/-
(* Definition Cdiv c1 c2 := ...（旧版复数除法，已被 c1 */C Cinv c2 取代） *)
-/

/-
(* Definition point_to_complex A := match A with (x,y) => [x,y] end.
Notation "f( A )" := (point_to_complex A)(at level 40).
Definition complex_to_point (α : Complex) := match α with [x,y] => (x,y) end.
Notation "p( α )" := (complex_to_point α)(at level 40).
Lemma map_1 : forall A, p(f(A)) = A. ...
Lemma map_2 : forall α, f(p(α)) = α. ...
Lemma map_3 : forall A α, α */c A = p(α */C f(A)). ... *)
-/

/-
(* 旋转与三角形相关的注释代码：
Definition PrO (theta : R) A := exp theta */c A.
Definition PrP A B theta := B +.exp theta */c(A -.B).
Definition PrP_order (A B C : Point) : Prop := point_3prod A B C > 0.
Definition PrP_order'(A B C : Point) : Prop := point_3prod A B C < 0.
Definition ThirdP ... / property20_inver ... *)
-/

end PG

end
