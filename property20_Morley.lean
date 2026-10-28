import PG_lean_1

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PG

-- ============================================================
--  Morley：对应 Coq 文件 Morley/property20_Morley.v 第 0-495 行
--
--  该范围内绝大部分定义与引理已在主链中转换：
--    PG_lean_0.lean：Point/O/point_inverse、point_plus/mult/divR/minus、
--      point_magn、vector/point_sqr/gap_sqr/gap/Per/Perp、col、
--      point_Oprod(/p)、point_3prod(/e)、point_mult_i(i*.)、
--      Complex 及 Cplus/Cminus/Cmult/Cinv/Cdiv、point_mult_complex(*/c)、
--      exp、angle、angle_sum公理
--    PG_lean_1.lean：Pmagn_comm、Complex_mult_passoc1、CPmult_exc、
--      exp_mult、exp_period、exp_period'、PrP_order、PrP_order'
--
--  本文件补齐该范围内主链缺失的 4 项：cis、angle_name、Pm_elim'、Qelim'。
--  转换约定与主链一致（PI -> Real.pi，sqrt/acos -> Real.sqrt/Real.arccos，
--  λ（标量）-> a，Coq 的 A / B 为实数除法 A / B）。
-- ============================================================

-- Coq: Definition cis(theta : R) : Complex := [cos(theta),sin(theta)]（与 exp 同体）。
def cis (theta : ℝ) : Complex := { re := Real.cos theta, im := Real.sin theta }

-- 角度的对称性：∠CAB = ∠BAC（分子用点积交换律，分母用乘法交换律）。
theorem angle_name (A B C : Point) : angle C A B = angle B A C := by
  show Real.arccos ((B -. A) ·. (C -. A) / (gap A B * gap A C)) =
      Real.arccos ((C -. A) ·. (B -. A) / (gap A C * gap A B))
  rw [Pmagn_comm, mul_comm]

-- 非零数乘可消去（等式代入方向）。
theorem Pm_elim' (a : ℝ) (A B : Point) (ha : a ≠ 0) (h : A = B) : a *. A = a *. B := by
  rw [h]

-- Qelim'：用复指数改写的正弦恒等式（Morley2 第 4 步的组合引理）。
-- Coq 陈述：exp(PI*4/3) = exp(PI*(-2/3)) -> A <> 0 -> B <> 0 -> C <> 0 ->
--   exp (PI - alpha - beta) */c (A / B *.(exp (beta + PI / 3) */c Q)) =
--   C / B *.(A / C *.(exp (- alpha - PI / 3) */c (exp (- PI / 3) */c Q)))。
-- 证明：两端分别用 CPmult_exc / Complex_mult_passoc1 把数乘提出来，再用
-- exp_mult 合并复指数；角度和化简为 4π/3-α 与 -α-2π/3，二者相差 2π，
-- 由 exp_period' 相等，最后用 Pm_elim' 消去公因子 A/B。
-- （假设 hper 在本证明中未用到，仅为与 Coq 签名一致并供 Morley2 调用。）
theorem Qelim' (A B C : ℝ) (Q : Point) (alpha beta : ℝ)
    (hper : exp (Real.pi * 4 / 3) = exp (Real.pi * (-2 / 3)))
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (exp (Real.pi - alpha - beta)) */c
        ((A / B) *. ((exp (beta + Real.pi / 3)) */c Q)) =
      (C / B) *. ((A / C) *. ((exp (-alpha - Real.pi / 3)) */c (exp (-Real.pi / 3) */c Q))) := by
  have hAB0 : A / B ≠ 0 := div_ne_zero hA hB
  have hsum : Real.pi - alpha - beta + (beta + Real.pi / 3) = 4 * Real.pi / 3 - alpha := by
    linarith
  have hang : -alpha - Real.pi / 3 + -Real.pi / 3 = -alpha - 2 * Real.pi / 3 := by
    linarith
  have hscale : (C / B) * (A / C) = A / B := by
    field_simp
  have h2 : -alpha - 2 * Real.pi / 3 + 2 * Real.pi = 4 * Real.pi / 3 - alpha := by
    linarith
  -- 左端：(A/B) *. (exp(4π/3 - α) */c Q)
  have hL : (exp (Real.pi - alpha - beta)) */c
        ((A / B) *. ((exp (beta + Real.pi / 3)) */c Q)) =
      (A / B) *. ((exp (4 * Real.pi / 3 - alpha)) */c Q) := by
    rw [← CPmult_exc, exp_mult, hsum]
  -- 右端：(A/B) *. (exp(-α - 2π/3) */c Q)
  have hR : (C / B) *. ((A / C) *. ((exp (-alpha - Real.pi / 3)) */c (exp (-Real.pi / 3) */c Q))) =
      (A / B) *. ((exp (-alpha - 2 * Real.pi / 3)) */c Q) := by
    rw [Complex_mult_passoc1, exp_mult, hang, pmult_l_l_p, hscale]
  rw [hL, hR]
  refine Pm_elim' (A / B) _ _ hAB0 ?_
  have hp : exp (-alpha - 2 * Real.pi / 3) = exp (4 * Real.pi / 3 - alpha) := by
    rw [← exp_period' (-alpha - 2 * Real.pi / 3), h2]
  rw [hp]

-- ============================================================
--  Helper lemmas for property20
--  对应 Coq 文件 Morley/property20_Morley.v 第 497-569 行
-- ============================================================

-- Lagrange 恒等式：(pr+qs)² + (ps-qr)² = (p²+q²)(r²+s²)。
theorem lagrange_id (p q r s : ℝ) :
    (p * r + q * s) ^ 2 + (p * s - q * r) ^ 2 = (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) := by
  ring

-- Lagrange 恒等式（beta 角用）：(p²+q²-(pr+qs))² + (ps-qr)² = (p²+q²)((p-r)²+(q-s)²)。
theorem lagrange_id_beta (p q r s : ℝ) :
    (p ^ 2 + q ^ 2 - (p * r + q * s)) ^ 2 + (p * s - q * r) ^ 2 =
      (p ^ 2 + q ^ 2) * ((p - r) ^ 2 + (q - s) ^ 2) := by
  ring

-- Lagrange 恒等式（gamma 角用）：(r²+s²-(pr+qs))² + (ps-qr)² = (r²+s²)((p-r)²+(q-s)²)。
theorem lagrange_id_gamma (p q r s : ℝ) :
    (r ^ 2 + s ^ 2 - (p * r + q * s)) ^ 2 + (p * s - q * r) ^ 2 =
      (r ^ 2 + s ^ 2) * ((p - r) ^ 2 + (q - s) ^ 2) := by
  ring

-- 三点外积的坐标展开：point_3prod A B C = (B-A)_x * (C-A)_y - (B-A)_y * (C-A)_x。
theorem p3prod_cross (a1 a2 b1 b2 c1 c2 : ℝ) :
    point_3prod ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩ =
      (b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1) := by
  simp only [point_3prod]
  ring

-- 由 dot² + cross² = norm²（norm > 0）得 1 - (dot/norm)² = cross²/norm²。
theorem div_sqr_lemma (dot cross norm : ℝ) (hnorm : 0 < norm)
    (hlag : dot * dot + cross * cross = norm * norm) :
    1 - (dot / norm) ^ 2 = cross ^ 2 / norm ^ 2 := by
  have hne : norm ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hnorm)
  have hsub : norm ^ 2 - dot ^ 2 = cross ^ 2 := by
    have hlag2 : dot ^ 2 + cross ^ 2 = norm ^ 2 := by
      simp only [pow_two]
      exact hlag
    linarith
  have hpow : (dot / norm) ^ 2 = dot ^ 2 / norm ^ 2 := by ring
  rw [hpow]
  have h1 : 1 = norm ^ 2 / norm ^ 2 := (div_self hne).symm
  rw [h1, ← sub_div (norm ^ 2) (dot ^ 2) (norm ^ 2), hsub]

-- 从 arccos 提取 cos 与 sin：若 dot² + cross² = norm²（norm > 0，cross ≥ 0）
-- 且 alpha = arccos(dot/norm)，则 cos alpha = dot/norm 且 sin alpha = cross/norm。
theorem cos_sin_from_acos (dot cross norm : ℝ) (hnorm : 0 < norm) (hcross : 0 ≤ cross)
    (hlag : dot * dot + cross * cross = norm * norm) (alpha : ℝ)
    (halpha : alpha = Real.arccos (dot / norm)) :
    Real.cos alpha = dot / norm ∧ Real.sin alpha = cross / norm := by
  have hlag2 : dot ^ 2 + cross ^ 2 = norm ^ 2 := by
    simp only [pow_two]
    exact hlag
  have hnorm2pos : (0 : ℝ) < norm ^ 2 := pow_pos hnorm 2
  -- (dot/norm)² ≤ 1，从而 |dot/norm| ≤ 1
  have hsq1 : (dot / norm) ^ 2 ≤ 1 ^ 2 := by
    have hpow : (dot / norm) ^ 2 = dot ^ 2 / norm ^ 2 := by ring
    rw [hpow, one_pow, div_le_one hnorm2pos]
    linarith [sq_nonneg cross]
  have hbound : -1 ≤ dot / norm ∧ dot / norm ≤ 1 :=
    abs_le_of_sq_le_sq' hsq1 zero_le_one
  refine ⟨?_, ?_⟩
  · rw [halpha]
    exact Real.cos_arccos hbound.1 hbound.2
  · -- sin(arccos x) = √(1 - x²)，再用 div_sqr_lemma 与 √(a²) = a（a ≥ 0）
    rw [halpha, Real.sin_arccos, div_sqr_lemma dot cross norm hnorm hlag]
    have hsq2 : cross ^ 2 / norm ^ 2 = (cross / norm) ^ 2 := by ring
    rw [hsq2, Real.sqrt_sq (div_nonneg hcross hnorm.le)]

-- ============================================================
--  property20（逆时针 ASA 构造）
--  对应 Coq 文件 Morley/property20_Morley.v 第 571-832 行
--  证明思路（与 Coq 一致）：设 p,q = B-A 坐标，r,s = C-A 坐标，
--  dot = (B-A)·(C-A)，cross = p·s-q·r（即三点外积，PrP_order 给出 cross > 0），
--  nu = |B-A|，nv = |C-A|，nw = |B-C|。由 cos_sin_from_acos 与三个 Lagrange
--  恒等式提取三角函数值，内角和公理给出 γ = π-α-β；由正弦定理
--  sin β/sin(α+β) = nv/nu；由旋转恒等式 exp α */c (B-A) = (nu/nv)*(C-A)；
--  代入即得结论。
-- ============================================================

theorem property20 (A B C : Point) (alpha beta : ℝ)
    (hcol : ¬ col A B C) (horder : PrP_order A B C)
    (halpha : alpha = angle C A B) (hbeta : beta = angle C B A) :
    C = A +. ((Real.sin beta / Real.sin (alpha + beta)) *.
      (exp alpha */c (B -. A))) := by
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  obtain ⟨c1, c2⟩ := C
  -- 三点互异
  have hABne : (⟨a1, a2⟩ : Point) ≠ ⟨b1, b2⟩ := fun h => hcol (Or.inr (Or.inl h))
  have hACne : (⟨a1, a2⟩ : Point) ≠ ⟨c1, c2⟩ := fun h => hcol (Or.inr (Or.inr (Or.inl h)))
  have hBCne : (⟨b1, b2⟩ : Point) ≠ ⟨c1, c2⟩ := fun h => hcol (Or.inr (Or.inr (Or.inr h)))
  set p : ℝ := b1 - a1 with hp_def
  set q : ℝ := b2 - a2 with hq_def
  set r : ℝ := c1 - a1 with hr_def
  set s : ℝ := c2 - a2 with hs_def
  set dot : ℝ := p * r + q * s with hdot_def
  set cross : ℝ := p * s - q * r with hcross_def
  set nu : ℝ := Real.sqrt (p ^ 2 + q ^ 2) with hnu_def
  set nv : ℝ := Real.sqrt (r ^ 2 + s ^ 2) with hnv_def
  set nw : ℝ := Real.sqrt ((p - r) ^ 2 + (q - s) ^ 2) with hnw_def
  -- 坐标差的非零性
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hABne ?_
    ext
    · show a1 = b1
      have h1 : b1 - a1 = 0 := by rw [← hp_def]; exact hcon.1
      linarith
    · show a2 = b2
      have h2 : b2 - a2 = 0 := by rw [← hq_def]; exact hcon.2
      linarith
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hACne ?_
    ext
    · show a1 = c1
      have h1 : c1 - a1 = 0 := by rw [← hr_def]; exact hcon.1
      linarith
    · show a2 = c2
      have h2 : c2 - a2 = 0 := by rw [← hs_def]; exact hcon.2
      linarith
  have hprs : p - r ≠ 0 ∨ q - s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hBCne ?_
    ext
    · show b1 = c1
      have h1 : b1 - c1 = p - r := by
        rw [hp_def, hr_def]
        ring
      linarith
    · show b2 = c2
      have h2 : b2 - c2 = q - s := by
        rw [hq_def, hs_def]
        ring
      linarith
  -- cross > 0（来自 PrP_order 与外积坐标展开）
  have hcross : 0 < cross := by
    have h := horder
    unfold PrP_order at h
    rw [p3prod_cross, ← hp_def, ← hq_def, ← hr_def, ← hs_def, ← hcross_def] at h
    exact h
  -- 非零实数的平方为正
  have sq_pos' : ∀ a : ℝ, a ≠ 0 → 0 < a ^ 2 := by
    intro a h
    have h1 : (0 : ℝ) < |a| := abs_pos.2 h
    have h2 := pow_pos h1 2
    rwa [sq_abs] at h2
  have hpq2pos : 0 < p ^ 2 + q ^ 2 := by
    rcases hpq with h | h
    · linarith [sq_pos' p h, sq_nonneg q]
    · linarith [sq_pos' q h, sq_nonneg p]
  have hrs2pos : 0 < r ^ 2 + s ^ 2 := by
    rcases hrs with h | h
    · linarith [sq_pos' r h, sq_nonneg s]
    · linarith [sq_pos' s h, sq_nonneg r]
  have hprs2pos : 0 < (p - r) ^ 2 + (q - s) ^ 2 := by
    rcases hprs with h | h
    · linarith [sq_pos' (p - r) h, sq_nonneg (q - s)]
    · linarith [sq_pos' (q - s) h, sq_nonneg (p - r)]
  have hnu_pos : 0 < nu := Real.sqrt_pos.2 hpq2pos
  have hnv_pos : 0 < nv := Real.sqrt_pos.2 hrs2pos
  have hnw_pos : 0 < nw := Real.sqrt_pos.2 hprs2pos
  have hnu0 : nu ≠ 0 := ne_of_gt hnu_pos
  have hnv0 : nv ≠ 0 := ne_of_gt hnv_pos
  have hnw0 : nw ≠ 0 := ne_of_gt hnw_pos
  -- nu², nv², nw²
  have hnu2 : nu * nu = p ^ 2 + q ^ 2 := by
    rw [hnu_def, Real.mul_self_sqrt]
    positivity
  have hnv2 : nv * nv = r ^ 2 + s ^ 2 := by
    rw [hnv_def, Real.mul_self_sqrt]
    positivity
  have hnw2 : nw * nw = (p - r) ^ 2 + (q - s) ^ 2 := by
    rw [hnw_def, Real.mul_self_sqrt]
    positivity
  -- gap 的坐标表示
  have hgap_AB : gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ = nu := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnu_def]
    congr 1
    rw [hp_def, hq_def]
    ring
  have hgap_AC : gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ = nv := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnv_def]
    congr 1
    rw [hr_def, hs_def]
    ring
  have hgap_BA : gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ = nu := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnu_def]
    congr 1
    rw [hp_def, hq_def]
    ring
  have hgap_BC : gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩ = nw := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnw_def]
    congr 1
    rw [hp_def, hq_def, hr_def, hs_def]
    ring
  have hgap_CA : gap (⟨c1, c2⟩ : Point) ⟨a1, a2⟩ = nv := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnv_def]
    congr 1
    rw [hr_def, hs_def]
    ring
  have hgap_CB : gap (⟨c1, c2⟩ : Point) ⟨b1, b2⟩ = nw := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnw_def]
    congr 1
    rw [hp_def, hq_def, hr_def, hs_def]
    ring
  -- 数量积的坐标表示
  have hdot0 : (⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) = dot := by
    simp only [point_magn, point_minus]
    rw [hdot_def, hp_def, hq_def, hr_def, hs_def]
  have hdot_beta : (⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩) = nu * nu - dot := by
    simp only [point_magn, point_minus]
    rw [hnu2, hdot_def, hp_def, hq_def, hr_def, hs_def]
    ring
  have hdot_gamma : (⟨b1, b2⟩ -. ⟨c1, c2⟩) ·. (⟨a1, a2⟩ -. ⟨c1, c2⟩) = nv * nv - dot := by
    simp only [point_magn, point_minus]
    rw [hnv2, hdot_def, hp_def, hq_def, hr_def, hs_def]
    ring
  -- 角度即 arccos
  have heq_alpha : alpha = Real.arccos (dot / (nu * nv)) := by
    rw [halpha]
    show Real.arccos ((⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) /
        (gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ * gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩)) =
      Real.arccos (dot / (nu * nv))
    rw [hdot0, hgap_AB, hgap_AC]
  have heq_beta : beta = Real.arccos ((nu * nu - dot) / (nu * nw)) := by
    rw [hbeta]
    show Real.arccos ((⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩) /
        (gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ * gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩)) =
      Real.arccos ((nu * nu - dot) / (nu * nw))
    rw [hdot_beta, hgap_BA, hgap_BC]
  have habc : angle (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ ⟨c1, c2⟩ = beta := by
    rw [angle_name (⟨b1, b2⟩ : Point) ⟨c1, c2⟩ ⟨a1, a2⟩, hbeta]
  have hgamma_eq : Real.pi - alpha - beta = angle (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ ⟨b1, b2⟩ := by
    rw [halpha]
    have hasum := angle_sum (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ ⟨c1, c2⟩ hcol
    rw [hasum, habc]
    linarith
  have heq_gamma : angle (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ ⟨b1, b2⟩ =
      Real.arccos ((nv * nv - dot) / (nv * nw)) := by
    show Real.arccos ((⟨b1, b2⟩ -. ⟨c1, c2⟩) ·. (⟨a1, a2⟩ -. ⟨c1, c2⟩) /
        (gap (⟨c1, c2⟩ : Point) ⟨b1, b2⟩ * gap (⟨c1, c2⟩ : Point) ⟨a1, a2⟩)) =
      Real.arccos ((nv * nv - dot) / (nv * nw))
    rw [hdot_gamma, hgap_CB, hgap_CA, mul_comm nw nv]
  -- Lagrange 恒等式 + cos/sin 提取
  have hlag1 : dot * dot + cross * cross = (nu * nv) * (nu * nv) := by
    have h : (nu * nv) * (nu * nv) = (nu * nu) * (nv * nv) := by ring
    rw [h, hnu2, hnv2, hdot_def, hcross_def]
    linear_combination lagrange_id p q r s
  have halpha_cs : Real.cos alpha = dot / (nu * nv) ∧ Real.sin alpha = cross / (nu * nv) :=
    cos_sin_from_acos dot cross (nu * nv) (mul_pos hnu_pos hnv_pos) (le_of_lt hcross) hlag1
      alpha heq_alpha
  have hlag2 : (nu * nu - dot) * (nu * nu - dot) + cross * cross = (nu * nw) * (nu * nw) := by
    have h : (nu * nw) * (nu * nw) = (nu * nu) * (nw * nw) := by ring
    rw [h, hnu2, hnw2, hdot_def, hcross_def]
    linear_combination lagrange_id_beta p q r s
  have hbeta_cs : Real.cos beta = (nu * nu - dot) / (nu * nw) ∧ Real.sin beta = cross / (nu * nw) :=
    cos_sin_from_acos (nu * nu - dot) cross (nu * nw) (mul_pos hnu_pos hnw_pos)
      (le_of_lt hcross) hlag2 beta heq_beta
  have hlag3 : (nv * nv - dot) * (nv * nv - dot) + cross * cross = (nv * nw) * (nv * nw) := by
    have h : (nv * nw) * (nv * nw) = (nv * nv) * (nw * nw) := by ring
    rw [h, hnv2, hnw2, hdot_def, hcross_def]
    linear_combination lagrange_id_gamma p q r s
  have hgamma_cs : Real.cos (Real.pi - alpha - beta) = (nv * nv - dot) / (nv * nw) ∧
      Real.sin (Real.pi - alpha - beta) = cross / (nv * nw) :=
    cos_sin_from_acos (nv * nv - dot) cross (nv * nw) (mul_pos hnv_pos hnw_pos)
      (le_of_lt hcross) hlag3 (Real.pi - alpha - beta) (by rw [hgamma_eq, heq_gamma])
  -- sin(α+β) = sin(π-α-β)
  have hsin_ab : Real.sin (alpha + beta) = Real.sin (Real.pi - alpha - beta) := by
    have h : Real.pi - alpha - beta = Real.pi - (alpha + beta) := by ring
    rw [h, Real.sin_pi_sub]
  -- 旋转恒等式 dot·p - cross·q = nu²·r 等
  have hidx1 : dot * p - cross * q = (p ^ 2 + q ^ 2) * r := by
    rw [hdot_def, hcross_def]
    ring
  have hidx2 : dot * q + cross * p = (p ^ 2 + q ^ 2) * s := by
    rw [hdot_def, hcross_def]
    ring
  have hcancel : ∀ X : ℝ, (p ^ 2 + q ^ 2) * X / (nu * nv) = nu / nv * X := by
    intro X
    have h1 : (p ^ 2 + q ^ 2) * X = nu * (nu * X) := by rw [← hnu2]; ring
    rw [h1, mul_div_mul_left (nu * X) nv hnu0]
    ring
  -- 旋转：exp α */c (B-A) = (nu/nv) *.(C-A)
  have hrot : exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩) = (nu / nv) *. (⟨c1, c2⟩ -. ⟨a1, a2⟩) := by
    obtain ⟨hcossa, hsina⟩ := halpha_cs
    have hrhs : (nu / nv) *. (⟨c1, c2⟩ -. ⟨a1, a2⟩) =
        ⟨nu / nv * (c1 - a1), nu / nv * (c2 - a2)⟩ := by
      simp [point_mult, point_minus]
    have hx : (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).x = nu / nv * (c1 - a1) := by
      have hcomp : (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).x
          = Real.cos alpha * (b1 - a1) - Real.sin alpha * (b2 - a2) := by
        simp [exp, point_mult_complex, point_mult, point_mult_i, point_minus, point_plus] <;> ring
      rw [hcomp, hcossa, hsina, ← hp_def, ← hq_def, ← hr_def]
      have hcomb : dot / (nu * nv) * p - cross / (nu * nv) * q
          = (dot * p - cross * q) / (nu * nv) := by ring
      rw [hcomb, hidx1, hcancel]
    have hy : (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).y = nu / nv * (c2 - a2) := by
      have hcomp : (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).y
          = Real.cos alpha * (b2 - a2) + Real.sin alpha * (b1 - a1) := by
        simp [exp, point_mult_complex, point_mult, point_mult_i, point_minus, point_plus] <;> ring
      rw [hcomp, hcossa, hsina, ← hp_def, ← hq_def, ← hs_def]
      have hcomb : dot / (nu * nv) * q + cross / (nu * nv) * p
          = (dot * q + cross * p) / (nu * nv) := by ring
      rw [hcomb, hidx2, hcancel]
    rw [hrhs]
    ext
    · exact hx
    · exact hy
  -- 正弦定理：sin β / sin(α+β) = nv/nu
  have hsineratio : Real.sin beta / Real.sin (alpha + beta) = nv / nu := by
    rw [hsin_ab]
    obtain ⟨_, hsinb⟩ := hbeta_cs
    obtain ⟨_, hsing⟩ := hgamma_cs
    rw [hsinb, hsing]
    have hc : cross ≠ 0 := ne_of_gt hcross
    field_simp
  -- 最终组装
  rw [hsineratio, hrot, pmult_l_l_p]
  have hscale : (nv / nu) * (nu / nv) = 1 := by
    field_simp
  rw [hscale, pmult_1_p]
  ext <;> simp [point_plus, point_minus] <;> linarith

-- ============================================================
--  Infrastructure for Morley2
--  对应 Coq 文件 Morley/property20_Morley.v 第 834-926 行
--
--  其中 exp_0、exp_multP、col_exc、col_exc'、col_exc'' 已在主链
--  PG_lean_1.lean 中转换（内容与 Coq 一致），此处不再重复；
--  本节补齐：pminus_same_r、test8'、test9'、p3prod_swap、
--  PrP_order'_swap、sin_PI_x。
-- ============================================================

-- 右端相同的减法可消去：A -. B = C -. B → A = C。
theorem pminus_same_r (A B C : Point) (h : A -. B = C -. B) : A = C := by
  have h1 := congrArg Point.x h
  have h2 := congrArg Point.y h
  simp only [point_minus] at h1 h2
  ext <;> linarith

-- 数乘消去引理：a ≠ 0 ∧ b ≠ 0 时，A = (b/a)*.B → B = (a/b)*.A。
theorem test8' (a b : ℝ) (A B : Point) (hab : a ≠ 0 ∧ b ≠ 0) (h : A = (b / a) *. B) :
    B = (a / b) *. A := by
  obtain ⟨ha, hb⟩ := hab
  rw [h, pmult_l_l_p]
  have hscale : (a / b) * (b / a) = 1 := by
    field_simp
  rw [hscale, pmult_1_p]

-- 相反数相等则原数相等。
theorem test9' (r r1 : ℝ) (h : -r = -r1) : r = r1 := by
  linarith

-- 三点外积交换后两点反号：point_3prod A C B = - point_3prod A B C。
theorem p3prod_swap (A B C : Point) : point_3prod A C B = - point_3prod A B C := by
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  obtain ⟨c1, c2⟩ := C
  simp only [point_3prod]
  ring

-- 顺时针方向条件换两点等价于逆时针方向条件：PrP_order' A B C → PrP_order A C B。
theorem PrP_order'_swap (A B C : Point) (h : PrP_order' A B C) : PrP_order A C B := by
  unfold PrP_order' at h
  unfold PrP_order
  rw [p3prod_swap]
  linarith

-- sin(π - x) = sin x（Mathlib 已有 Real.sin_pi_sub）。
theorem sin_PI_x (x : ℝ) : Real.sin (Real.pi - x) = Real.sin x :=
  Real.sin_pi_sub x

-- ============================================================
--  property20_inver（ASA 构造的唯一性：从公式反推角度）
--  对应 Coq 文件 Morley/property20_Morley.v 第 1187-1392 行
--  证明思路（与 Coq 一致）：设 v = B-A（坐标 x,y），k = sinβ/sin(α+β)。
--  Part 1：由公式得 C-A = k*.(exp α */c v)，于是 (B-A)·(C-A) = k·cosα·|v|²，
--    gap AC = k·|v|，代入 angle 定义得 arccos(cos α) = α；
--  Part 2：C-B = k*.(exp α */c v) -. v，于是 (A-B)·(C-B) = |v|²(1-k·cosα)，
--    gap BC = |v|·sqrt(k²+1-2k·cosα)；用三角恒等式
--    1-k·cosα = sinα·cosβ/sin(α+β) 与 k²+1-2k·cosα = sin²α/sin²(α+β)
--    化简得 arccos(cos β) = β。
-- ============================================================

theorem property20_inver (A B C : Point) (alpha beta : ℝ)
    (hcol : ¬ col A B C) (horder : PrP_order A B C)
    (hformula : C = A +. ((Real.sin beta / Real.sin (alpha + beta)) *.
      (exp alpha */c (B -. A))))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hsum : alpha + beta < Real.pi) :
    alpha = angle C A B ∧ beta = angle C B A := by
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  obtain ⟨c1, c2⟩ := C
  -- 三角函数基本事实
  have halpha_lt : alpha < Real.pi := by linarith
  have hbeta_lt : beta < Real.pi := by linarith
  have hsin_a : 0 < Real.sin alpha := Real.sin_pos_of_pos_of_lt_pi halpha halpha_lt
  have hsin_b : 0 < Real.sin beta := Real.sin_pos_of_pos_of_lt_pi hbeta hbeta_lt
  have hsin_s : 0 < Real.sin (alpha + beta) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_s0 : Real.sin (alpha + beta) ≠ 0 := ne_of_gt hsin_s
  set k : ℝ := Real.sin beta / Real.sin (alpha + beta) with hk_def
  have hk0 : 0 < k := div_pos hsin_b hsin_s
  have hk_ne : k ≠ 0 := ne_of_gt hk0
  -- A ≠ B
  have hab : (⟨a1, a2⟩ : Point) ≠ ⟨b1, b2⟩ := fun h => hcol (Or.inr (Or.inl h))
  have hv_ne : b1 - a1 ≠ 0 ∨ b2 - a2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hab ?_
    ext
    · show a1 = b1
      linarith
    · show a2 = b2
      linarith
  have sq_pos' : ∀ a : ℝ, a ≠ 0 → 0 < a ^ 2 := by
    intro a h
    have h1 : (0 : ℝ) < |a| := abs_pos.2 h
    have h2 := pow_pos h1 2
    rwa [sq_abs] at h2
  have hvsq0 : 0 < (b1 - a1) ^ 2 + (b2 - a2) ^ 2 := by
    rcases hv_ne with h | h
    · linarith [sq_pos' (b1 - a1) h, sq_nonneg (b2 - a2)]
    · linarith [sq_pos' (b2 - a2) h, sq_nonneg (b1 - a1)]
  set s2 : ℝ := (b1 - a1) ^ 2 + (b2 - a2) ^ 2 with hs2_def
  have hvsq_ge : 0 ≤ s2 := le_of_lt hvsq0
  have hv_ne' : s2 ≠ 0 := ne_of_gt hvsq0
  -- cos² + sin² = 1（乘法形式）
  have hs2c : Real.cos alpha * Real.cos alpha + Real.sin alpha * Real.sin alpha = 1 := by
    linear_combination sin2_cos2' alpha
  have hs2c_b : Real.sin beta * Real.sin beta + Real.cos beta * Real.cos beta = 1 := by
    linear_combination sin2_cos2' beta
  -- 由公式：C -. A = k *. (exp α */c (B -. A))
  have hCA : (⟨c1, c2⟩ -. ⟨a1, a2⟩) = k *. (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)) := by
    rw [hformula, pplus_comm, pplus_minus_assoc, pminus_eq_O, pplus_O_p']
  -- ===== Part 1：alpha = angle C A B =====
  refine ⟨?_, ?_⟩
  · show alpha = Real.arccos ((⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) /
        (gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ * gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩))
    have hdot : (⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩)
        = k * Real.cos alpha * s2 := by
      rw [hCA]
      simp only [point_magn, point_minus, point_mult, point_mult_complex, point_mult_i,
        point_plus, exp]
      rw [hs2_def]
      ring
    have hgap_AB : gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ = Real.sqrt s2 := by
      simp only [gap, point_sqr, point_magn, point_minus]
      rw [hs2_def]
      congr 1
      ring
    have hsqr_CA : (c1 - a1) * (c1 - a1) + (c2 - a2) * (c2 - a2) = k * k * s2 := by
      show (⟨c1, c2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) = k * k * s2
      rw [hCA]
      simp only [point_magn, point_minus, point_mult, point_mult_complex, point_mult_i,
        point_plus, exp]
      rw [hs2_def]
      linear_combination (k * k * ((b1 - a1) ^ 2 + (b2 - a2) ^ 2)) * hs2c
    have hkk : Real.sqrt (k * k) = k := by
      rw [show k * k = k ^ 2 from by ring, Real.sqrt_sq hk0.le]
    have hgap_AC : gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ = k * Real.sqrt s2 := by
      simp only [gap, point_sqr, point_magn, point_minus]
      have hsym : (a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)
          = (c1 - a1) * (c1 - a1) + (c2 - a2) * (c2 - a2) := by ring
      rw [hsym, hsqr_CA, Real.sqrt_mul (mul_self_nonneg k), hkk]
    have hden : Real.sqrt s2 * (k * Real.sqrt s2) = k * s2 := by
      have h1 : Real.sqrt s2 * (k * Real.sqrt s2) = (Real.sqrt s2 * Real.sqrt s2) * k := by ring
      rw [h1, Real.mul_self_sqrt hvsq_ge, mul_comm]
    have hrat : k * Real.cos alpha * s2 / (k * s2) = Real.cos alpha := by
      field_simp
    rw [hdot, hgap_AB, hgap_AC, hden, hrat, Real.arccos_cos halpha.le halpha_lt.le]
  -- ===== Part 2：beta = angle C B A =====
  · show beta = Real.arccos ((⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩) /
        (gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ * gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩))
    have hCB : (⟨c1, c2⟩ -. ⟨b1, b2⟩)
        = k *. (exp alpha */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)) -. (⟨b1, b2⟩ -. ⟨a1, a2⟩) := by
      have htrans : (⟨c1, c2⟩ -. ⟨b1, b2⟩)
          = (⟨c1, c2⟩ -. ⟨a1, a2⟩) -. (⟨b1, b2⟩ -. ⟨a1, a2⟩) := by
        ext <;> simp only [point_minus] <;> ring
      rw [htrans, hCA]
    -- 三角恒等式
    have htrig1 : 1 - k * Real.cos alpha
        = Real.sin alpha * Real.cos beta / Real.sin (alpha + beta) := by
      have hD : Real.sin (alpha + beta)
          = Real.sin alpha * Real.cos beta + Real.sin beta * Real.cos alpha := by
        rw [Real.sin_add]
        ring
      have hDne : Real.sin alpha * Real.cos beta + Real.sin beta * Real.cos alpha ≠ 0 := by
        rw [← hD]
        exact hsin_s0
      have h1 : (1 : ℝ) - Real.sin beta * Real.cos alpha
            / (Real.sin alpha * Real.cos beta + Real.sin beta * Real.cos alpha)
          = Real.sin alpha * Real.cos beta
            / (Real.sin alpha * Real.cos beta + Real.sin beta * Real.cos alpha) := by
        rw [← div_self hDne, ← sub_div]
        ring
      rw [hk_def, div_mul_eq_mul_div, hD, h1]
    have hmain : Real.sin beta * Real.sin beta
        + Real.sin (alpha + beta) * Real.sin (alpha + beta)
        - 2 * Real.sin beta * Real.sin (alpha + beta) * Real.cos alpha
      = Real.sin alpha * Real.sin alpha := by
      rw [Real.sin_add alpha beta]
      linear_combination (Real.sin alpha * Real.sin alpha) * hs2c_b
        - (Real.sin beta * Real.sin beta) * hs2c
    have htrig2 : k * k + 1 - 2 * k * Real.cos alpha
        = Real.sin alpha * Real.sin alpha
          / (Real.sin (alpha + beta) * Real.sin (alpha + beta)) := by
      have hmid : 2 * (Real.sin beta / Real.sin (alpha + beta)) * Real.cos alpha
          = 2 * Real.sin beta * Real.cos alpha / Real.sin (alpha + beta) := by ring
      have hcomb : Real.sin beta ^ 2 / (Real.sin (alpha + beta)) ^ 2 + 1
          - 2 * Real.sin beta * Real.cos alpha / Real.sin (alpha + beta)
        = (Real.sin beta * Real.sin beta + Real.sin (alpha + beta) * Real.sin (alpha + beta)
            - 2 * Real.sin beta * Real.sin (alpha + beta) * Real.cos alpha)
          / (Real.sin (alpha + beta) * Real.sin (alpha + beta)) := by
        field_simp
      have hksq : k * k = (Real.sin beta / Real.sin (alpha + beta)) ^ 2 := by
        rw [hk_def, ← pow_two]
      rw [hksq, div_pow, hmid, hcomb, hmain]
    have hd0 : 0 < k * k + 1 - 2 * k * Real.cos alpha := by
      rw [htrig2]
      exact div_pos (mul_pos hsin_a hsin_a) (mul_pos hsin_s hsin_s)
    have hsqrtd : Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hd0)
    have hsqrt_trig2 : Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha)
        = Real.sin alpha / Real.sin (alpha + beta) := by
      rw [htrig2]
      have hform : Real.sin alpha * Real.sin alpha
            / (Real.sin (alpha + beta) * Real.sin (alpha + beta))
          = (Real.sin alpha / Real.sin (alpha + beta)) ^ 2 := by ring
      rw [hform, Real.sqrt_sq (div_nonneg hsin_a.le hsin_s.le)]
    -- 代入 angle 定义
    have hdot_CB : (⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩)
        = s2 * (1 - k * Real.cos alpha) := by
      rw [hCB]
      simp only [point_magn, point_minus, point_mult, point_mult_complex, point_mult_i,
        point_plus, exp]
      rw [hs2_def]
      ring
    have hgap_BA : gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ = Real.sqrt s2 := by
      simp only [gap, point_sqr, point_magn, point_minus]
      rw [hs2_def]
      congr 1
      ring
    have hsqr_CB : (c1 - b1) * (c1 - b1) + (c2 - b2) * (c2 - b2)
        = s2 * (k * k + 1 - 2 * k * Real.cos alpha) := by
      show (⟨c1, c2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩)
        = s2 * (k * k + 1 - 2 * k * Real.cos alpha)
      rw [hCB]
      simp only [point_magn, point_minus, point_mult, point_mult_complex, point_mult_i,
        point_plus, exp]
      rw [hs2_def]
      linear_combination (k * k * ((b1 - a1) ^ 2 + (b2 - a2) ^ 2)) * hs2c
    have hgap_BC : gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩
        = Real.sqrt (s2 * (k * k + 1 - 2 * k * Real.cos alpha)) := by
      simp only [gap, point_sqr, point_magn, point_minus]
      have hsym : (b1 - c1) * (b1 - c1) + (b2 - c2) * (b2 - c2)
          = (c1 - b1) * (c1 - b1) + (c2 - b2) * (c2 - b2) := by ring
      rw [hsym, hsqr_CB]
    have hden2 : Real.sqrt s2
          * Real.sqrt (s2 * (k * k + 1 - 2 * k * Real.cos alpha))
        = s2 * Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha) := by
      rw [Real.sqrt_mul hvsq_ge, ← mul_assoc, Real.mul_self_sqrt hvsq_ge]
    have hratio2 : s2 * (1 - k * Real.cos alpha)
          / (s2 * Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha))
        = (1 - k * Real.cos alpha) / Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha) := by
      have hd : s2 * Real.sqrt (k * k + 1 - 2 * k * Real.cos alpha) ≠ 0 :=
        mul_ne_zero hv_ne' hsqrtd
      field_simp
    have hratio3 : (Real.sin alpha * Real.cos beta / Real.sin (alpha + beta))
          / (Real.sin alpha / Real.sin (alpha + beta)) = Real.cos beta := by
      have hsa : Real.sin alpha ≠ 0 := ne_of_gt hsin_a
      field_simp
    rw [hdot_CB, hgap_BA, hgap_BC, hden2, hratio2, htrig1, hsqrt_trig2, hratio3,
      Real.arccos_cos hbeta.le hbeta_lt.le]

-- ============================================================
--  property20'（顺时针 ASA 构造）
--  对应 Coq 文件 Morley/property20_Morley.v 第 931-1177 行
--  与 property20 的差别仅在方向：PrP_order' 给出 cross < 0，
--  于是 sin α = -cross/(nu·nv)（cos_sin_from_acos 以 -cross ≥ 0 代入），
--  旋转方向变为 exp(-α) = [cos α, -sin α] = [dot/(nu·nv), cross/(nu·nv)]，
--  其余（gap、点积、Lagrange 恒等式、正弦定理、收尾）完全相同。
-- ============================================================

theorem property20' (A B C : Point) (alpha beta : ℝ)
    (hcol : ¬ col A B C) (horder : PrP_order' A B C)
    (halpha : alpha = angle C A B) (hbeta : beta = angle C B A) :
    C = A +. ((Real.sin beta / Real.sin (alpha + beta)) *.
      (exp (-alpha) */c (B -. A))) := by
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  obtain ⟨c1, c2⟩ := C
  have hABne : (⟨a1, a2⟩ : Point) ≠ ⟨b1, b2⟩ := fun h => hcol (Or.inr (Or.inl h))
  have hACne : (⟨a1, a2⟩ : Point) ≠ ⟨c1, c2⟩ := fun h => hcol (Or.inr (Or.inr (Or.inl h)))
  have hBCne : (⟨b1, b2⟩ : Point) ≠ ⟨c1, c2⟩ := fun h => hcol (Or.inr (Or.inr (Or.inr h)))
  set p : ℝ := b1 - a1 with hp_def
  set q : ℝ := b2 - a2 with hq_def
  set r : ℝ := c1 - a1 with hr_def
  set s : ℝ := c2 - a2 with hs_def
  set dot : ℝ := p * r + q * s with hdot_def
  set cross : ℝ := p * s - q * r with hcross_def
  set nu : ℝ := Real.sqrt (p ^ 2 + q ^ 2) with hnu_def
  set nv : ℝ := Real.sqrt (r ^ 2 + s ^ 2) with hnv_def
  set nw : ℝ := Real.sqrt ((p - r) ^ 2 + (q - s) ^ 2) with hnw_def
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hABne ?_
    ext
    · show a1 = b1
      have h1 : b1 - a1 = 0 := by rw [← hp_def]; exact hcon.1
      linarith
    · show a2 = b2
      have h2 : b2 - a2 = 0 := by rw [← hq_def]; exact hcon.2
      linarith
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hACne ?_
    ext
    · show a1 = c1
      have h1 : c1 - a1 = 0 := by rw [← hr_def]; exact hcon.1
      linarith
    · show a2 = c2
      have h2 : c2 - a2 = 0 := by rw [← hs_def]; exact hcon.2
      linarith
  have hprs : p - r ≠ 0 ∨ q - s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hBCne ?_
    ext
    · show b1 = c1
      have h1 : b1 - c1 = p - r := by
        rw [hp_def, hr_def]
        ring
      linarith
    · show b2 = c2
      have h2 : b2 - c2 = q - s := by
        rw [hq_def, hs_def]
        ring
      linarith
  -- cross < 0（来自 PrP_order'）
  have hcross : cross < 0 := by
    have h := horder
    unfold PrP_order' at h
    rw [p3prod_cross, ← hp_def, ← hq_def, ← hr_def, ← hs_def, ← hcross_def] at h
    exact h
  have hcross_neg : 0 ≤ -cross := neg_nonneg.mpr hcross.le
  have sq_pos' : ∀ a : ℝ, a ≠ 0 → 0 < a ^ 2 := by
    intro a h
    have h1 : (0 : ℝ) < |a| := abs_pos.2 h
    have h2 := pow_pos h1 2
    rwa [sq_abs] at h2
  have hpq2pos : 0 < p ^ 2 + q ^ 2 := by
    rcases hpq with h | h
    · linarith [sq_pos' p h, sq_nonneg q]
    · linarith [sq_pos' q h, sq_nonneg p]
  have hrs2pos : 0 < r ^ 2 + s ^ 2 := by
    rcases hrs with h | h
    · linarith [sq_pos' r h, sq_nonneg s]
    · linarith [sq_pos' s h, sq_nonneg r]
  have hprs2pos : 0 < (p - r) ^ 2 + (q - s) ^ 2 := by
    rcases hprs with h | h
    · linarith [sq_pos' (p - r) h, sq_nonneg (q - s)]
    · linarith [sq_pos' (q - s) h, sq_nonneg (p - r)]
  have hnu_pos : 0 < nu := Real.sqrt_pos.2 hpq2pos
  have hnv_pos : 0 < nv := Real.sqrt_pos.2 hrs2pos
  have hnw_pos : 0 < nw := Real.sqrt_pos.2 hprs2pos
  have hnu0 : nu ≠ 0 := ne_of_gt hnu_pos
  have hnv0 : nv ≠ 0 := ne_of_gt hnv_pos
  have hnw0 : nw ≠ 0 := ne_of_gt hnw_pos
  have hnu2 : nu * nu = p ^ 2 + q ^ 2 := by
    rw [hnu_def, Real.mul_self_sqrt]
    positivity
  have hnv2 : nv * nv = r ^ 2 + s ^ 2 := by
    rw [hnv_def, Real.mul_self_sqrt]
    positivity
  have hnw2 : nw * nw = (p - r) ^ 2 + (q - s) ^ 2 := by
    rw [hnw_def, Real.mul_self_sqrt]
    positivity
  have hgap_AB : gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ = nu := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnu_def]
    congr 1
    rw [hp_def, hq_def]
    ring
  have hgap_AC : gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ = nv := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnv_def]
    congr 1
    rw [hr_def, hs_def]
    ring
  have hgap_BA : gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ = nu := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnu_def]
    congr 1
    rw [hp_def, hq_def]
    ring
  have hgap_BC : gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩ = nw := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnw_def]
    congr 1
    rw [hp_def, hq_def, hr_def, hs_def]
    ring
  have hgap_CA : gap (⟨c1, c2⟩ : Point) ⟨a1, a2⟩ = nv := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnv_def]
    congr 1
    rw [hr_def, hs_def]
    ring
  have hgap_CB : gap (⟨c1, c2⟩ : Point) ⟨b1, b2⟩ = nw := by
    simp only [gap, point_sqr, point_magn, point_minus]
    rw [hnw_def]
    congr 1
    rw [hp_def, hq_def, hr_def, hs_def]
    ring
  have hdot0 : (⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) = dot := by
    simp only [point_magn, point_minus]
    rw [hdot_def, hp_def, hq_def, hr_def, hs_def]
  have hdot_beta : (⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩) = nu * nu - dot := by
    simp only [point_magn, point_minus]
    rw [hnu2, hdot_def, hp_def, hq_def, hr_def, hs_def]
    ring
  have hdot_gamma : (⟨b1, b2⟩ -. ⟨c1, c2⟩) ·. (⟨a1, a2⟩ -. ⟨c1, c2⟩) = nv * nv - dot := by
    simp only [point_magn, point_minus]
    rw [hnv2, hdot_def, hp_def, hq_def, hr_def, hs_def]
    ring
  have heq_alpha : alpha = Real.arccos (dot / (nu * nv)) := by
    rw [halpha]
    show Real.arccos ((⟨b1, b2⟩ -. ⟨a1, a2⟩) ·. (⟨c1, c2⟩ -. ⟨a1, a2⟩) /
        (gap (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ * gap (⟨a1, a2⟩ : Point) ⟨c1, c2⟩)) =
      Real.arccos (dot / (nu * nv))
    rw [hdot0, hgap_AB, hgap_AC]
  have heq_beta : beta = Real.arccos ((nu * nu - dot) / (nu * nw)) := by
    rw [hbeta]
    show Real.arccos ((⟨a1, a2⟩ -. ⟨b1, b2⟩) ·. (⟨c1, c2⟩ -. ⟨b1, b2⟩) /
        (gap (⟨b1, b2⟩ : Point) ⟨a1, a2⟩ * gap (⟨b1, b2⟩ : Point) ⟨c1, c2⟩)) =
      Real.arccos ((nu * nu - dot) / (nu * nw))
    rw [hdot_beta, hgap_BA, hgap_BC]
  have habc : angle (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ ⟨c1, c2⟩ = beta := by
    rw [angle_name (⟨b1, b2⟩ : Point) ⟨c1, c2⟩ ⟨a1, a2⟩, hbeta]
  have hgamma_eq : Real.pi - alpha - beta = angle (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ ⟨b1, b2⟩ := by
    rw [halpha]
    have hasum := angle_sum (⟨a1, a2⟩ : Point) ⟨b1, b2⟩ ⟨c1, c2⟩ hcol
    rw [hasum, habc]
    linarith
  have heq_gamma : angle (⟨a1, a2⟩ : Point) ⟨c1, c2⟩ ⟨b1, b2⟩ =
      Real.arccos ((nv * nv - dot) / (nv * nw)) := by
    show Real.arccos ((⟨b1, b2⟩ -. ⟨c1, c2⟩) ·. (⟨a1, a2⟩ -. ⟨c1, c2⟩) /
        (gap (⟨c1, c2⟩ : Point) ⟨b1, b2⟩ * gap (⟨c1, c2⟩ : Point) ⟨a1, a2⟩)) =
      Real.arccos ((nv * nv - dot) / (nv * nw))
    rw [hdot_gamma, hgap_CB, hgap_CA, mul_comm nw nv]
  -- Lagrange 恒等式 + cos/sin 提取（以 -cross 为 cos_sin_from_acos 的第二参数）
  have hlag1 : dot * dot + (-cross) * (-cross) = (nu * nv) * (nu * nv) := by
    have h : (-cross) * (-cross) = cross * cross := by ring
    rw [h]
    have h2 : (nu * nv) * (nu * nv) = (nu * nu) * (nv * nv) := by ring
    rw [h2, hnu2, hnv2, hdot_def, hcross_def]
    linear_combination lagrange_id p q r s
  have halpha_cs : Real.cos alpha = dot / (nu * nv) ∧ Real.sin alpha = -cross / (nu * nv) :=
    cos_sin_from_acos dot (-cross) (nu * nv) (mul_pos hnu_pos hnv_pos) hcross_neg
      hlag1 alpha heq_alpha
  have hlag2 : (nu * nu - dot) * (nu * nu - dot) + (-cross) * (-cross)
      = (nu * nw) * (nu * nw) := by
    have h : (-cross) * (-cross) = cross * cross := by ring
    rw [h]
    have h2 : (nu * nw) * (nu * nw) = (nu * nu) * (nw * nw) := by ring
    rw [h2, hnu2, hnw2, hdot_def, hcross_def]
    linear_combination lagrange_id_beta p q r s
  have hbeta_cs : Real.cos beta = (nu * nu - dot) / (nu * nw) ∧
      Real.sin beta = -cross / (nu * nw) :=
    cos_sin_from_acos (nu * nu - dot) (-cross) (nu * nw) (mul_pos hnu_pos hnw_pos)
      hcross_neg hlag2 beta heq_beta
  have hlag3 : (nv * nv - dot) * (nv * nv - dot) + (-cross) * (-cross)
      = (nv * nw) * (nv * nw) := by
    have h : (-cross) * (-cross) = cross * cross := by ring
    rw [h]
    have h2 : (nv * nw) * (nv * nw) = (nv * nv) * (nw * nw) := by ring
    rw [h2, hnv2, hnw2, hdot_def, hcross_def]
    linear_combination lagrange_id_gamma p q r s
  have hgamma_cs : Real.cos (Real.pi - alpha - beta) = (nv * nv - dot) / (nv * nw) ∧
      Real.sin (Real.pi - alpha - beta) = -cross / (nv * nw) :=
    cos_sin_from_acos (nv * nv - dot) (-cross) (nv * nw) (mul_pos hnv_pos hnw_pos)
      hcross_neg hlag3 (Real.pi - alpha - beta) (by rw [hgamma_eq, heq_gamma])
  have hsin_ab : Real.sin (alpha + beta) = Real.sin (Real.pi - alpha - beta) := by
    have h : Real.pi - alpha - beta = Real.pi - (alpha + beta) := by ring
    rw [h, Real.sin_pi_sub]
  have hidx1 : dot * p - cross * q = (p ^ 2 + q ^ 2) * r := by
    rw [hdot_def, hcross_def]
    ring
  have hidx2 : dot * q + cross * p = (p ^ 2 + q ^ 2) * s := by
    rw [hdot_def, hcross_def]
    ring
  have hcancel : ∀ X : ℝ, (p ^ 2 + q ^ 2) * X / (nu * nv) = nu / nv * X := by
    intro X
    have h1 : (p ^ 2 + q ^ 2) * X = nu * (nu * X) := by rw [← hnu2]; ring
    rw [h1, mul_div_mul_left (nu * X) nv hnu0]
    ring
  -- 旋转：exp(-α) = [cos α, -sin α] = [dot/(nu·nv), cross/(nu·nv)]
  have hrot : exp (-alpha) */c (⟨b1, b2⟩ -. ⟨a1, a2⟩) = (nu / nv) *. (⟨c1, c2⟩ -. ⟨a1, a2⟩) := by
    obtain ⟨hcossa, hsina⟩ := halpha_cs
    have hnegs : Real.sin (-alpha) = cross / (nu * nv) := by
      rw [Real.sin_neg, hsina]
      ring
    have hrhs : (nu / nv) *. (⟨c1, c2⟩ -. ⟨a1, a2⟩) =
        ⟨nu / nv * (c1 - a1), nu / nv * (c2 - a2)⟩ := by
      simp [point_mult, point_minus]
    have hx : (exp (-alpha) */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).x = nu / nv * (c1 - a1) := by
      have hcomp : (exp (-alpha) */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).x
          = Real.cos (-alpha) * (b1 - a1) - Real.sin (-alpha) * (b2 - a2) := by
        simp [exp, point_mult_complex, point_mult, point_mult_i, point_minus, point_plus] <;> ring
      rw [hcomp, Real.cos_neg, hnegs, hcossa, ← hp_def, ← hq_def, ← hr_def]
      have hcomb : dot / (nu * nv) * p - cross / (nu * nv) * q
          = (dot * p - cross * q) / (nu * nv) := by ring
      rw [hcomb, hidx1, hcancel]
    have hy : (exp (-alpha) */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).y = nu / nv * (c2 - a2) := by
      have hcomp : (exp (-alpha) */c (⟨b1, b2⟩ -. ⟨a1, a2⟩)).y
          = Real.cos (-alpha) * (b2 - a2) + Real.sin (-alpha) * (b1 - a1) := by
        simp [exp, point_mult_complex, point_mult, point_mult_i, point_minus, point_plus] <;> ring
      rw [hcomp, Real.cos_neg, hnegs, hcossa, ← hp_def, ← hq_def, ← hs_def]
      have hcomb : dot / (nu * nv) * q + cross / (nu * nv) * p
          = (dot * q + cross * p) / (nu * nv) := by ring
      rw [hcomb, hidx2, hcancel]
    rw [hrhs]
    ext
    · exact hx
    · exact hy
  have hsineratio : Real.sin beta / Real.sin (alpha + beta) = nv / nu := by
    rw [hsin_ab]
    obtain ⟨_, hsinb⟩ := hbeta_cs
    obtain ⟨_, hsing⟩ := hgamma_cs
    rw [hsinb, hsing]
    have hc : -cross ≠ 0 := by
      intro h
      exact ne_of_lt hcross (by linarith)
    field_simp
    exact div_self (ne_of_lt hcross)
  rw [hsineratio, hrot, pmult_l_l_p]
  have hscale : (nv / nu) * (nu / nv) = 1 := by
    field_simp
  rw [hscale, pmult_1_p]
  ext <;> simp [point_plus, point_minus] <;> linarith

-- ============================================================
--  Morley2（莫莱定理的逆/角格构造）
--  对应 Coq 文件 Morley/property20_Morley.v 第 1397-1513 行
--  证明思路（与 Coq 一致）：R = O；由 Etri 得 Q = exp(π/3) */c P。
--  Step 1：由内角和公理与 property20 得 A 的正弦公式；
--  Step 2：由内角和公理与 property20' 得 B 的正弦公式；
--  Step 3：由 Q = exp(π/3) */c P 与 exp_multP 得 P = exp(-π/3) */c Q；
--  Step 4：将 A、B 的公式代入并用 Qelim' 得
--    exp(π-α-β) */c A = (sinβ/sinα) *. B；
--  Step 5：由 test8' 改写 B 的公式为以 R(=O) 为顶点的 ASA 形式；
--  Step 6：由 property20_inver 反推得
--    π-α-β = angle B O A 且 α = angle B A O；
--  最后由内角和公理得 angle O A B = α 与 angle O B A = β。
-- ============================================================

theorem Morley2 (A B C P Q R : Point) (alpha beta gamma : ℝ)
    (hR : R = O)
    (h0 : Etri P Q R)
    (h1 : alpha = angle R A Q)
    (h2 : beta = angle P B R)
    (h3 : gamma = angle P C Q)
    (h4 : alpha + Real.pi / 3 = angle B R P)
    (h5 : alpha + Real.pi / 3 = angle C Q P)
    (h6 : beta + Real.pi / 3 = angle A R Q)
    (h7 : beta + Real.pi / 3 = angle C P Q)
    (h8 : gamma + Real.pi / 3 = angle A Q R)
    (h9 : gamma + Real.pi / 3 = angle B P R)
    (h10 : ¬ col A R Q)
    (h11 : ¬ col B P R)
    (h12 : PrP_order R Q A)
    (h13 : PrP_order' R P B)
    (h14 : 0 < alpha ∧ alpha < Real.pi / 2)
    (h15 : 0 < beta ∧ beta < Real.pi / 2)
    (h16 : 0 < gamma ∧ gamma < Real.pi / 2)
    (h17 : ¬ col R A B)
    (h18 : PrP_order R A B) :
    angle R A B = alpha ∧ angle R B A = beta := by
  subst hR
  obtain ⟨h0_col, h0_Q⟩ := h0
  rw [pplus_O_p, pminus_O] at h0_Q
  -- h0_Q : Q = exp (π/3) */c P
  -- ===== Step 1：A 的公式 =====
  have hsinA : Real.sin ((beta + Real.pi / 3) + (gamma + Real.pi / 3)) = Real.sin alpha := by
    have h1' : alpha = angle Q A O := by rw [h1, angle_name A Q O]
    have hasum := angle_sum A O Q h10
    rw [← h1', ← h6, ← h8] at hasum
    rw [hasum]
    have hr : Real.pi - (beta + Real.pi / 3) - (gamma + Real.pi / 3)
        = Real.pi - ((beta + Real.pi / 3) + (gamma + Real.pi / 3)) := by ring
    rw [hr, sin_PI_x]
  have hA : A = Real.sin (gamma + Real.pi / 3) / Real.sin alpha
      *. (exp (beta + Real.pi / 3) */c Q) := by
    have hp := property20 O Q A (beta + Real.pi / 3) (gamma + Real.pi / 3)
      (fun hc => h10 (col_exc' O Q A hc)) h12 h6 h8
    rw [hsinA, pplus_O_p, pminus_O] at hp
    exact hp
  -- ===== Step 2：B 的公式 =====
  have hsinB : Real.sin ((alpha + Real.pi / 3) + (gamma + Real.pi / 3)) = Real.sin beta := by
    have hcolBOP : ¬ col B O P := fun hc => h11 (col_exc'' B O P hc)
    have hasum := angle_sum B O P hcolBOP
    rw [← h2, ← h4, ← h9] at hasum
    rw [hasum]
    have hr : Real.pi - (alpha + Real.pi / 3) - (gamma + Real.pi / 3)
        = Real.pi - ((alpha + Real.pi / 3) + (gamma + Real.pi / 3)) := by ring
    rw [hr, sin_PI_x]
  have hB : B = Real.sin (gamma + Real.pi / 3) / Real.sin beta
      *. (exp (-alpha - Real.pi / 3) */c P) := by
    have hp' := property20' O P B (alpha + Real.pi / 3) (gamma + Real.pi / 3)
      (fun hc => h11 (col_exc O P B hc)) h13 h4 h9
    rw [hsinB] at hp'
    rw [show -(alpha + Real.pi / 3) = -alpha - Real.pi / 3 from by ring] at hp'
    rw [pplus_O_p, pminus_O] at hp'
    exact hp'
  -- ===== Step 3：P = exp(-π/3) */c Q =====
  have hP : P = exp (-Real.pi / 3) */c Q := by
    have him : exp (-Real.pi / 3) */C exp (Real.pi / 3) */c P = P := by
      have h2 : exp (-Real.pi / 3) */C exp (Real.pi / 3)
          = exp (-Real.pi / 3 + Real.pi / 3) := exp_mult (-Real.pi / 3) (Real.pi / 3)
      rw [h2, show -Real.pi / 3 + Real.pi / 3 = 0 from by ring, exp_0]
      ext <;> simp [R_R_to_C, point_mult_complex, point_mult, point_mult_i, point_plus] <;> ring
    rw [h0_Q, Complex_mult_passoc1]
    exact him.symm
  -- ===== Step 4：exp(π-α-β) */c A = (sinβ/sinα) *. B =====
  have hexp : exp (Real.pi - alpha - beta) */c A
      = (Real.sin beta / Real.sin alpha) *. B := by
    rw [hP] at hB
    rw [hA, hB]
    refine Qelim' (Real.sin (gamma + Real.pi / 3)) (Real.sin alpha) (Real.sin beta) Q
      alpha beta ?_ ?_ ?_ ?_
    · rw [← exp_period' (Real.pi * (-2 / 3))]
      congr 1
      field_simp
      ring
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  -- ===== Step 5：B 的 ASA 形式 =====
  have hBf : B = (Real.sin alpha / Real.sin beta) *. (exp (Real.pi - alpha - beta) */c A) := by
    have hne : Real.sin alpha ≠ 0 ∧ Real.sin beta ≠ 0 :=
      ⟨ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)),
       ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))⟩
    exact test8' (Real.sin alpha) (Real.sin beta)
      (exp (Real.pi - alpha - beta) */c A) B hne hexp
  -- ===== Step 6：反推角度 =====
  have hangles : Real.pi - alpha - beta = angle B O A ∧ alpha = angle B A O := by
    refine property20_inver O A B (Real.pi - alpha - beta) alpha h17 h18 ?_ ?_ ?_ ?_
    · rw [pplus_O_p, pminus_O,
        show (Real.pi - alpha - beta) + alpha = Real.pi - beta from by ring, sin_PI_x]
      exact hBf
    · linarith
    · obtain ⟨ha, _⟩ := h14
      exact ha
    · linarith
  obtain ⟨hangle_BOA, hangle_BAO⟩ := hangles
  have hangle_OAB : angle O A B = alpha := by
    rw [angle_name A B O]
    exact hangle_BAO.symm
  refine ⟨hangle_OAB, ?_⟩
  have hasum := angle_sum O A B h17
  rw [← hangle_BOA] at hasum
  rw [hangle_OAB] at hasum
  linarith

end PG
