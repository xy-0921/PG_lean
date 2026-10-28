import PG_lean_1

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PG

-- ============================================================
--  点几何：Lean 4 / Mathlib 版本（第 2 部分）
--  对应 Coq 文件：A_2.v（例 1 至例 9）
--
--  转换约定（Coq -> Lean）：
--    Coq 的 Example        -> theorem
--    数值字面量计算         -> norm_num
--    坐标线性等式           -> linarith；含除法 -> field_simp 后 linarith
-- ============================================================

-- 例1 求证：三角形 ABC 的三条中线 AM、BN、CP 共点。
-- 设 O 为原点，M、N、P 分别为 BC、OC、OB 的中点，G 为由 Inter_p 确定的
-- 直线 BN 与 CP 的交点，则 G 在中线 OM 上（即 col G O M）。
-- 证明思路（与 Coq 一致）：由中点条件得 C = 2*.N、B = 2*.P、B +. C = 2*.M，
-- 故 B +. 2*.N = C +. 2*.P；对 Inter_p 取 u=1, v=2, r=1, s=2 得
-- B +. 2*.N = 3*.G，于是 2*.M = 3*.G，即 G = (2/3)*.M，G 在中线 OM 上。
-- （注：假设 Triangle O B C 在代数证明中未被用到，与 Coq 原证明一致。）
theorem example_1 (B C G M N P : Point) :
    Triangle O B C →
    Inter_p B N C P G ∧ Midpoint M B C ∧ Midpoint N O C ∧ Midpoint P O B →
    col G O M := by
  intro hTri h
  rcases h with ⟨hInter, hM, hN, hP⟩
  -- 中点条件的代数转写：C = 2*.N，B = 2*.P，B +. C = 2*.M
  have hC : C = 2 *. N := Midpoint_p N C hN
  have hB : B = 2 *. P := Midpoint_p P B hP
  have hM2 : B +. C = 2 *. M := (locate_P_2 B C M).mpr hM
  -- 由中点条件改写 B +. C（对应 Coq 的 H4、H5）
  have h4 : B +. C = 2 *. P +. C := by rw [hB]
  have h5 : B +. C = B +. 2 *. N := by rw [hC]
  -- B +. 2N = C +. 2P
  have key : B +. 2 *. N = C +. 2 *. P := by
    rw [← h5, h4, pplus_comm C]
  -- 对 Inter_p 取 u=1, v=2, r=1, s=2，得 B +. 2*.N = 3*.G（对应 Coq 的 H6）
  have h6 : 1 *. B +. 2 *. N = (1 + 2) *. G := by
    refine hInter 1 2 1 2 ⟨?_, by ring, by norm_num⟩
    simp only [pmult_1_p]
    exact key
  norm_num at h6
  rw [pmult_1_p, ← h5, hM2] at h6
  -- h6 : 2*.M = 3*.G，故 G = (2/3)*.M，即 G、O、M 共线
  unfold col
  refine Or.inl ⟨2 / 3, by norm_num, ?_⟩
  ext
  · have h6x := congrArg Point.x h6
    simp [vector, point_minus, point_mult, O] at h6x ⊢
    field_simp
    linarith
  · have h6y := congrArg Point.y h6
    simp [vector, point_minus, point_mult, O] at h6y ⊢
    field_simp
    linarith

-- 例2 平行四边形（顶点 O、B、C、D；形式化条件 vector O B = vector D C，
-- 由 O 为原点即得 B +. D = C）的边 OB 中点为 M，直线 DM 交对角线 OC 于 P。
-- 求证：OC = 3·OP（即 C = 3*.P，P 为对角线 OC 的三等分点）。
-- 证明思路（与 Coq 一致）：由中点得 B = 2*.M；由平行四边形条件得 B +. D = C，
-- 即 D +. 2*.M = C；对 Inter_p 取 u=1, v=2, r=2, s=1（1+2 = 2+1 ≠ 0）
-- 得 D +. 2*.M = 3*.P，故 C = 3*.P。
theorem example_2 (B C D M P : Point) :
    Parallelogram B O C D → Midpoint M O B → Inter_p D M O C P →
    vector O C = 3 *. vector O P := by
  intro hPlg hMid hInter
  -- 目标化为 C = 3 *. P（vector O C = C -. O = C 等）
  simp only [vector, pminus_O]
  -- 中点条件：B = 2 *. M
  have hB : B = 2 *. M := Midpoint_p M B hMid
  -- 平行四边形条件：B -. O = C -. D，即 B +. D = C
  rcases hPlg with ⟨hvec, _hne⟩
  have h1 : B -. O = C -. D := hvec
  rw [pminus_O] at h1
  have hBDC : B +. D = C := by
    rw [h1, pplus_minus_assoc', pminus_eq_O, pminus_O]
  -- D +. 2*.M = C
  have key : D +. 2 *. M = C := by
    rw [← hBDC, hB, pplus_comm]
  -- Inter_p 取 u=1, v=2, r=2, s=1，得 D +. 2*.M = 3*.P
  have h6 : 1 *. D +. 2 *. M = (1 + 2) *. P := by
    refine hInter 1 2 2 1 ⟨?_, by ring, by norm_num⟩
    simp only [pmult_1_p, pmult_0_l, pplus_O_p]
    exact key
  norm_num at h6
  rw [pmult_1_p] at h6
  -- 结论：C = 3*.P
  rw [← key]
  exact h6

-- ============================================================
--  例 3 及其辅助引理
-- ============================================================

-- 辅助引理：数乘向量可消去非零系数。
lemma ex3_3 (A B C D : Point) (a : ℝ) :
    a ≠ 0 → a *. vector A B = a *. vector C D → vector A B = vector C D := by
  intro hne h
  ext <;> simp only [vector, point_minus, point_mult, Point.mk.injEq] at h ⊢
  · exact mul_left_cancel₀ hne h.1
  · exact mul_left_cancel₀ hne h.2

-- 辅助引理：向量等式两端同时反向。
lemma ex3_4 (A B C D : Point) (a b : ℝ) :
    a *. vector A B = b *. vector C D → a *. vector B A = b *. vector D C := by
  intro h
  ext <;> simp [vector, point_minus, point_mult] at h ⊢
  · linear_combination (-1 : ℝ) * h.1
  · linear_combination (-1 : ℝ) * h.2

lemma ex3_5 (A B : Point) (a : ℝ) : (-a) *. vector A B = a *. vector B A := by
  unfold vector
  rw [pmult_minus_opp']

lemma ex3_5' (A B : Point) : (-1 : ℝ) *. vector A B = vector B A := by
  unfold vector
  rw [pmult_minus_opp]

-- 例3 已知 C = 3*.P（P 在 OC 上）、5*.Q = 3*.B（Q 在 OB 上），
-- D = CQ ∩ PB，T = BC ∩ QP。求证：D 为 PB 中点（PD/BD = 1）、
-- 5·QD = DC（QD/DC = 1/5）、3·BT = CT（BT/CT = 1/3）、3·PQ = 2·QT（PQ/QT = 2/3）。
-- 证明思路（与 Coq 一致）：由 C +. 5Q = 3P +. 3B 对 Inter_p C Q P B D 取
-- u=1, v=5, r=3, s=3 得 C +. 5Q = 6D，即 3P +. 3B = 6D，用 linear_com1'
-- 与 ex3_3/ex3_4 得结论 1、2；由 3B -. C = 5Q -. 3P（即 5Q -. 3P）与
-- Inter_p B C Q P T 取 u=3, v=-1, r=5, s=-3 得 3B -. C = 2T，用 linear_com1'
-- 与 ex3_5' 得结论 3，用 linear_com1 得结论 4。
theorem example_3 (B C D P Q T : Point) :
    C = 3 *. P ∧ 5 *. Q = 3 *. B →
    Inter_p C Q P B D → Inter_p B C Q P T →
    vector P D = vector D B ∧ 5 *. vector Q D = vector D C ∧
      3 *. vector B T = vector C T ∧ 3 *. vector P Q = 2 *. vector Q T := by
  rintro ⟨hCeq, hQeq⟩ hInter1 hInter2
  -- 基础加权等式：C +. 5Q = 3P +. 3B
  have h3 : C +. 5 *. Q = 3 *. P +. 3 *. B := by rw [hCeq, hQeq]
  -- 对 Inter_p C Q P B D 取 u=1, v=5, r=3, s=3：C +. 5Q = 6D
  have h4 : C +. 5 *. Q = 6 *. D := by
    have h4' := hInter1 1 5 3 3 ⟨by simp only [pmult_1_p]; exact h3, by ring, by norm_num⟩
    rw [pmult_1_p] at h4'
    rw [(by norm_num : (1 + 5 : ℝ) = 6)] at h4'
    exact h4'
  have h5key : 3 *. P +. 3 *. B = 6 *. D := by rw [← h3]; exact h4
  -- 3B = C +. 5Q -. 3P
  have h6 : 3 *. B = C +. 5 *. Q -. 3 *. P := by
    rw [h3, pplus_comm (3 *. P), pplus_minus_assoc, pminus_eq_O, pplus_O_p']
  -- 3B -. C = 5Q -. 3P
  have h7 : 3 *. B -. C = 5 *. Q -. 3 *. P := by
    rw [h6]
    ext <;> simp [point_minus, point_plus, point_mult] <;> ring
  -- 对 Inter_p B C Q P T 取 u=3, v=-1, r=5, s=-3：3B -. C = 2T
  have h8full : 3 *. B +. (-1) *. C = (3 + (-1)) *. T := by
    refine hInter2 3 (-1) 5 (-3) ⟨?_, by ring, by norm_num⟩
    simp only [pmult_opp_p', pmult_1_p, pplus_minus_tran]
    rw [← h7]
  have h8s : 3 *. B -. C = 2 *. T := by
    have h8' := h8full
    rw [pmult_opp_p, pplus_minus_tran] at h8'
    rw [(by norm_num : (3 + (-1) : ℝ) = 2)] at h8'
    exact h8'
  have h9 : 5 *. Q -. 3 *. P = 2 *. T := h7.symm.trans h8s
  have h10 : 5 *. Q +. (-3) *. P = (5 + (-3)) *. T := by
    rw [(by norm_num : (5 + (-3) : ℝ) = 2), pmult_opp_p', pplus_minus_tran]
    exact h9
  -- 结论 1：3P +. 3B = 6D 经 linear_com1' 与 ex3_3 得 vector P D = vector D B
  have c1 : vector P D = vector D B := by
    have h5' : 3 *. P +. 3 *. B = (3 + 3) *. D := by
      rw [(by norm_num : (3 + 3 : ℝ) = 6)]
      exact h5key
    have step1 := linear_com1' P B D 3 3 h5'
    -- step1 : 3 *. vector P D = 3 *. vector D B
    exact ex3_3 P D D B 3 (by norm_num) step1
  -- 结论 2：1·C +. 5Q = 6D 经 linear_com1' 与 ex3_4 得 5·QD = DC
  have c2 : 5 *. vector Q D = vector D C := by
    have h4'' : (1 : ℝ) *. C +. 5 *. Q = (1 + 5) *. D := by
      rw [pmult_1_p, (by norm_num : (1 + 5 : ℝ) = 6)]
      exact h4
    have step2 := ex3_4 C D D Q 1 5 (linear_com1' C Q D 1 5 h4'')
    -- step2 : (1:ℝ) *. vector D C = 5 *. vector Q D
    rw [pmult_1_p] at step2
    exact step2.symm
  -- 结论 3：linear_com1' 与 ex3_5' 得 3·BT = CT
  have c3 : 3 *. vector B T = vector C T := by
    have step3 := linear_com1' B C T 3 (-1) h8full
    -- step3 : 3 *. vector B T = (-1 : ℝ) *. vector T C
    rw [ex3_5'] at step3
    exact step3
  -- 结论 4：linear_com1 得 5·(Q-T) = -3·(T-P)，坐标线性推理得 3·PQ = 2·QT
  have c4 : 3 *. vector P Q = 2 *. vector Q T := by
    have step4 := linear_com1 Q P T 5 (-3) h10
    -- step4 : 5 *. (Q -. T) = (-3) *. (T -. P)
    unfold vector
    ext <;> simp [point_minus, point_mult] at step4 ⊢ <;> linarith
  exact ⟨c1, c2, c3, c4⟩

-- ============================================================
--  例 4 及其辅助引理
-- ============================================================

-- 辅助引理：数量积差为零则两积相等（Coq 用 induction + ring，此处为纯实数线性推理）。
lemma e4 (A B C D : Point) : A ·. B - C ·. D = 0 → A ·. B = C ·. D := by
  intro h
  linarith

-- 例4 三角形 ABC 的三条高线 AD、BE、CF 共点。
-- 设 O 为两高线 AD、BE 的交点（原点），由 AO⊥BC 得 A·(B-.C) = 0，
-- 由 BO⊥AC 得 B·(A-.C) = 0，即 A·.B = A·.C 且 A·.B = B·.C；
-- 于是 C·(A-.B) = A·.C - B·.C = A·.B - A·.B = 0，即 CO⊥AB。
-- （注：假设 Triangle A B C、Perp A D B C 等在代数证明中未被用到，与 Coq 一致。）
theorem example_4 (A B C D E F : Point) :
    Triangle A B C → Perp A D B C → Perp B E A C → Perp C F A B →
    Inter_p A D B E O → Perp A O B C → Perp B O A C → Perp C O A B := by
  intro _hTri _hAD _hBE _hCF _hInter h5 h6
  -- 展开垂直定义并化去原点（O 为原点）
  unfold Perp at h5 h6 ⊢
  simp only [pminus_O] at h5 h6 ⊢
  -- h5 : A ·. B - A ·. C = 0，h6 : B ·. A - B ·. C = 0
  rw [Pmagn_minus_distr] at h5 h6
  rw [Pmagn_comm B A] at h6
  -- 数量积等式：A·.B = A·.C，A·.B = B·.C
  have h5' : A ·. B = A ·. C := e4 A B A C h5
  have h6' : A ·. B = B ·. C := e4 A B B C h6
  -- 目标：C·(A-.B) = 0 → A·.C - B·.C = 0
  rw [Pmagn_minus_distr, Pmagn_comm C A, Pmagn_comm C B]
  -- 用 h5'、h6' 改写：A·.B - A·.B = 0
  rw [← h5', ← h6']
  ring

-- ============================================================
--  例 5 及其辅助引理（中线长与分角线长公式）
-- ============================================================

-- 极化恒等式：point_sqr(A + B) = point_sqr A + point_sqr B + 2·(A·B)。
lemma e5_1 (A B : Point) :
    point_sqr (A +. B) = point_sqr A + point_sqr B + 2 * (A ·. B) := by
  simp only [point_sqr, point_magn, point_plus]
  ring

-- 数乘的平方：point_sqr(λ·A) = λ²·point_sqr A（Coq 的 Rsqr λ 即 λ²）。
lemma e5_2 (a : ℝ) (A : Point) : point_sqr (a *. A) = a ^ 2 * point_sqr A := by
  simp only [point_sqr, point_magn, point_mult]
  ring

lemma e5_3 (A B : Point) : A = B → point_sqr A = point_sqr B := by
  intro h
  rw [h]

-- 平行四边形恒等式：point_sqr(A+B) - point_sqr(A-B) = 4·(A·B)。
lemma e5_4''' (A B : Point) :
    point_sqr (A +. B) - point_sqr (A -. B) = 4 * (A ·. B) := by
  simp only [point_sqr, point_magn, point_plus, point_minus]
  ring

lemma e5_4 (A B : Point) :
    2 * (A ·. B) = (point_sqr (A +. B) - point_sqr (A -. B)) / 2 := by
  rw [e5_4''', eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma div_distr (r r1 r2 : ℝ) (h : r2 ≠ 0) :
    (r - r1) / r2 = r / r2 - r1 / r2 := by
  rw [sub_div]

lemma minus_same (a b c : ℝ) : a = b ↔ a - c = b - c := by
  constructor
  · intro h; rw [h]
  · intro h; linarith

lemma div_same (a b c : ℝ) (h : a = b) : a / c = b / c := by
  rw [h]

-- 例5 (1) 中线长公式：D 为 BC 中点，|OB| = c、|OC| = b、|BC| = a，则
-- |OD|² = (b² + c² - a²/2)/2（Parallelogram 公式）。
-- 证明思路（与 Coq 一致）：B +. C = 2·D ⟹ point_sqr(B+C) = 4·point_sqr D；
-- 由 e5_1、e5_4 与 point_sqr(B-C) = a² 得
-- c² + b² + (4·point_sqr D - a²)/2 = 4·point_sqr D，解出 point_sqr D 即可。
-- （Coq 证明末段的 div_distr/minus_same/div_same 坐标运算，
--   此处由 field_simp + linarith 一次性完成。）
theorem example_5_1 (B C D : Point) (a b c : ℝ) :
    Triangle O B C → gap_sqr B O = c ^ 2 → gap_sqr C O = b ^ 2 →
    gap_sqr B C = a ^ 2 → Midpoint D B C →
    gap_sqr D O = ((c ^ 2 + b ^ 2) - a ^ 2 / 2) / 2 := by
  intro _hTri h0 h1 h2 h3
  -- 中点条件：B +. C = 2 *. D
  have hBCmid : B +. C = 2 *. D := (locate_P_2 B C D).mpr h3
  have h4a : point_sqr (B +. C) = 4 * point_sqr D := by
    calc point_sqr (B +. C) = point_sqr (2 *. D) := e5_3 _ _ hBCmid
      _ = 2 ^ 2 * point_sqr D := e5_2 2 D
      _ = 4 * point_sqr D := by norm_num
  have hB : point_sqr B = c ^ 2 := (gap_sqr_O B).symm.trans h0
  have hC : point_sqr C = b ^ 2 := (gap_sqr_O C).symm.trans h1
  have hBCm : point_sqr (B -. C) = a ^ 2 := h2
  have h4 : point_sqr B + point_sqr C + 2 * (B ·. C) = 4 * point_sqr D := by
    rw [← h4a]
    exact (e5_1 B C).symm
  rw [hB, hC, e5_4, ← h4a, hBCm] at h4
  -- h4 : c² + b² + (point_sqr (B +. C) - a²)/2 = point_sqr (B +. C)
  have hmain : 2 * (c ^ 2 + b ^ 2) - a ^ 2 = 4 * point_sqr D := by
    field_simp at h4
    linarith
  rw [gap_sqr_O]
  field_simp
  linarith

-- 分角线向量式的平方（Coq 的 e5_5）。
lemma e5_5 (B C E : Point) :
    gap C O *. B +. gap B O *. C = (gap B O + gap C O) *. E →
    point_sqr (gap C O *. B +. gap B O *. C)
      = point_sqr ((gap B O + gap C O) *. E) := by
  intro h
  rw [h]

-- 分角线向量式平方的展开（Coq 的 e5_5'；此处直接坐标计算，
-- 不需要 Coq 中展开 gap 的步骤）。
lemma e5_5' (B C : Point) :
    point_sqr (gap C O *. B +. gap B O *. C)
      = (gap C O) ^ 2 * point_sqr B + (gap B O) ^ 2 * point_sqr C
        + 2 * (gap B O) * (gap C O) * (B ·. C) := by
  simp only [point_sqr, point_magn, point_plus, point_mult]
  ring

-- 数乘平方应用于和向量（Coq 的 e5_5''，即 e5_2 的实例）。
lemma e5_5'' (B C E : Point) :
    point_sqr ((gap B O + gap C O) *. E) = (gap B O + gap C O) ^ 2 * point_sqr E := by
  exact e5_2 _ E

-- 以下四个是 Coq 中辅助的纯环运算引理（在 Lean 证明中由 ring 直接处理，保留以对应）。
lemma Rmult_assoc' (r1 r2 r3 : ℝ) : r1 * (r2 * r3) = r1 * r2 * r3 := by ring

lemma Rmult_mix_distr (r r1 r2 r3 : ℝ) :
    r * (r1 + r2 - r3) = r * r1 + r * r2 - r * r3 := by ring

lemma Rmult_4 (a b c d : ℝ) : a * b * c * d = a * (b * c) * d := by ring

lemma div_all (a b c d : ℝ) : (a + b - c) / d = a / d + b / d - c / d := by ring

-- 例5 (2) 分角线长公式：E 在 ∠BOC 的分角线上，满足
-- (gap C O)·B + (gap B O)·C = (gap B O + gap C O)·E，则
-- |OE|² = (2b²c² + bc(b² + c² - a²))/(b + c)²。
-- 证明思路（与 Coq 一致）：对分角线向量式两端取平方（e5_5），
-- 用 e5_5'、e5_5'' 展开并代入 |OB| = c、|OC| = b、point_sqr B = c²、point_sqr C = b²，
-- 再由 e5_4 与例5 (1) 的中线结果得 2·(B·C) = b² + c² - a²，
-- 最后解出 point_sqr E。
theorem example_5_2 (B C D E : Point) (a b c : ℝ) :
    Triangle O B C → gap B O = c → gap C O = b → gap B C = a →
    Midpoint D B C → Angle_div E O B C →
    gap_sqr D O = (b ^ 2 + c ^ 2 - a ^ 2 / 2) / 2 → (c + b) ≠ 0 →
    gap_sqr E O =
      (2 * b ^ 2 * c ^ 2 + b * c * (b ^ 2 + c ^ 2 - a ^ 2)) / (c + b) ^ 2 := by
  intro _hTri hBO hCO hBCa _hMid hDiv hD hcb
  -- 分角线向量式两端取平方
  have h4 : (gap C O) *. B +. (gap B O) *. C = (gap B O + gap C O) *. E := hDiv
  have hsq := e5_5 B C E h4
  rw [e5_5', e5_5''] at hsq
  -- 代入 gap B O = c、gap C O = b、point_sqr B = c²、point_sqr C = b²
  have hB : point_sqr B = c ^ 2 := by rw [← gap_to_sqr_O B, hBO]
  have hC : point_sqr C = b ^ 2 := by rw [← gap_to_sqr_O C, hCO]
  rw [hBO, hCO, hB, hC] at hsq
  -- hsq : b²c² + c²b² + 2·c·b·(B·.C) = (c + b)²·point_sqr E
  -- 中点条件给出 point_sqr(B +. C) = 4·point_sqr D 与 point_sqr(B -. C) = a²
  have hBCmid : B +. C = 2 *. D := (locate_P_2 B C D).mpr _hMid
  have h4a : point_sqr (B +. C) = 4 * point_sqr D := by
    calc point_sqr (B +. C) = point_sqr (2 *. D) := e5_3 _ _ hBCmid
      _ = 2 ^ 2 * point_sqr D := e5_2 2 D
      _ = 4 * point_sqr D := by norm_num
  have hBCm : point_sqr (B -. C) = a ^ 2 := by
    have hg : gap_sqr B C = a ^ 2 := by rw [← gap_to_sqr, hBCa]
    exact hg
  -- 2·(B·.C) = (4·point_sqr D - a²)/2
  have hdot : 2 * (B ·. C) = (4 * point_sqr D - a ^ 2) / 2 := by
    rw [e5_4, h4a, hBCm]
  -- point_sqr D = (b² + c² - a²/2)/2（即假设 hD，换为 point_sqr 形式）
  have hDp : point_sqr D = (b ^ 2 + c ^ 2 - a ^ 2 / 2) / 2 := (gap_sqr_O D).symm.trans hD
  -- 倍乘去分母：4·point_sqr D = 2·(b² + c²) - a²
  have hD4 : 4 * point_sqr D = 2 * (b ^ 2 + c ^ 2) - a ^ 2 := by
    rw [hDp]
    field_simp
    ring
  -- 于是 2·(B·.C) = b² + c² - a²
  have hkey : 2 * (B ·. C) = b ^ 2 + c ^ 2 - a ^ 2 := by
    rw [hdot, hD4, div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- 代入 hsq 解出 point_sqr E
  have hfinal : (c + b) ^ 2 * point_sqr E
      = 2 * b ^ 2 * c ^ 2 + b * c * (b ^ 2 + c ^ 2 - a ^ 2) := by
    linear_combination (b * c) * hkey - hsq
  rw [gap_sqr_O E, eq_div_iff (pow_ne_zero 2 hcb)]
  linear_combination hfinal

-- ============================================================
--  例 6 及其辅助引理（欧拉线垂直）
-- ============================================================

lemma f1_1 (r r1 r2 r3 : ℝ) (h : r1 - r + (r2 - r) + (r3 - r) = 0) :
    r1 + r2 + r3 = 3 * r := by linarith

-- 重心条件转为坐标和：A +. B +. C = 3 *. G。
lemma focus_1 (A B C G : Point) (h : focus G A B C) : A +. B +. C = 3 *. G := by
  have h1 := congrArg Point.x h
  have h2 := congrArg Point.y h
  simp only [focus, v0, vector, point_minus, point_plus, O, sub_self] at h1 h2
  ext <;> simp only [point_plus, point_mult]
  · exact f1_1 _ _ _ _ h1
  · exact f1_1 _ _ _ _ h2

lemma Rmult_plus_distr_l' (a b c : ℝ) : (a + b) * c = a * c + b * c := by ring

lemma Rdiv_simpl_l (r1 r2 : ℝ) (h : r1 ≠ 0) : r2 / r1 * r1 = r2 := by field_simp

-- 乘 1/2 的点积为零则乘 1 的点积为零（Coq 的 e6_1，此处用数乘分配恒等式）。
lemma e6_1 (A B C : Point) (u : ℝ) :
    (A -. C -. u *.(B -. C)) ·. ((B +. C) /. 2) = 0 →
    (A -. C -. u *.(B -. C)) ·. (B +. C) = 0 := by
  intro h
  have hdiv : (B +. C) /. 2 = (1 / 2) *. (B +. C) := by
    ext <;> simp only [point_divR, point_mult, point_plus] <;> ring
  rw [hdiv, Pmagn_mult_assoc'] at h
  have h12 : (1 : ℝ) / 2 ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h12

lemma e6_2 (r r1 r2 : ℝ) : r + r1 + r2 - r = r1 + r2 := by ring

lemma e6_2' (r r1 r2 : ℝ) : r + r1 + r2 - r1 = r + r2 := by ring

lemma e6_3 (u : ℝ) (A B : Point) : u *. A ·. B = u * (A ·. B) := by
  simp only [point_mult, point_magn]; ring

lemma e6_4 (u : ℝ) (A B : Point) : u *. A ·. B = A ·. (u *. B) := by
  simp only [point_mult, point_magn]; ring

lemma e6_5 (r1 r2 r3 : ℝ) : r1 - (r2 - r3) = r1 - r2 + r3 := by ring

-- 垂心在原点时的基本正交关系：A·(B-C) = B·(A-C) = C·(A-B) = 0。
lemma oc_1 (A B C : Point) (h : orthocenter O A B C) :
    A ·. (B -. C) = B ·. (A -. C) ∧ B ·. (A -. C) = C ·. (A -. B) ∧ B ·. (A -. C) = 0 := by
  unfold orthocenter at h
  simp only [vector, pminus_O] at h
  obtain ⟨h1, h2⟩ := h
  -- h1 : A ·. B = B ·. C，h2 : B ·. C = C ·. A
  have hab : A ·. B = A ·. C := by linarith [h1, h2, Pmagn_comm C A]
  constructor
  · rw [Pmagn_minus_distr, Pmagn_minus_distr]
    linarith [Pmagn_comm B A, h1, hab]
  · constructor
    · rw [Pmagn_minus_distr, Pmagn_minus_distr]
      linarith [Pmagn_comm B A, Pmagn_comm C A, Pmagn_comm C B, h1, hab]
    · rw [Pmagn_minus_distr]
      linarith [Pmagn_comm B A, h1]

-- 例6 过三角形三顶点且垂直于对边中点与垂心连线的直线，与对边的交点 L、M 满足
-- ML ⊥ OG（欧拉线）。
-- 证明思路（与 Coq 一致）：oc_1 给出 A·.B = A·.C = B·.C；重心给出 3·(A-C)·G = A·.A - C·.C、
-- 3·(B-C)·G = B·.B - C·.C；把 L = u·B + (1-u)·C、M = v·A + (1-v)·C 代入两条垂直条件
-- （用 e6_1 去掉中点的 /2）得 u·(B·.B - C·.C) = A·.C - C·.C、v·(A·.A - C·.C) = B·.C - C·.C；
-- 于是 3·(M-L)·G = v(A·.A - C·.C) - u(B·.B - C·.C) = (B·.C - C·.C) - (A·.C - C·.C) = 0。
theorem example6 (A B C D E F L G M : Point) :
    ¬ col A B C → orthocenter O A B C → focus G A B C →
    Midpoint D B C → Midpoint E C A → Midpoint F A B →
    col L C B → Perp A L D O → col M C A → Perp B M E O →
    3 *. (M -. L) ·. G = 0 := by
  intro hncol hOrth hFocus hD hE _hF hLcol hAL hMcol hBM
  obtain ⟨hO1, hO2, hO3⟩ := oc_1 A B C hOrth
  have hA0 : A ·. (B -. C) = 0 := hO1.trans hO3
  have hC0 : C ·. (A -. B) = 0 := hO2.symm.trans hO3
  have hdA : A ·. B - A ·. C = 0 := by rw [← Pmagn_minus_distr]; exact hA0
  have hdB : B ·. A - B ·. C = 0 := by rw [← Pmagn_minus_distr]; exact hO3
  have hdC : C ·. A - C ·. B = 0 := by rw [← Pmagn_minus_distr]; exact hC0
  have hab : A ·. B = A ·. C := by linarith
  have hBA : B ·. A = A ·. B := Pmagn_comm B A
  have hCA : C ·. A = A ·. C := Pmagn_comm C A
  have hCB : C ·. B = B ·. C := Pmagn_comm C B
  have hbc : B ·. C = A ·. C := by linarith [hdB, hBA, hab]
  -- 重心与中点
  have hGsum : A +. B +. C = 3 *. G := focus_1 A B C G hFocus
  have hBC2 : B +. C = 2 *. D := (locate_P_2 B C D).mpr hD
  have hAC2 : A +. C = 2 *. E := by
    have h := (locate_P_2 C A E).mpr hE
    rw [pplus_comm] at h
    exact h
  have hD2 : (B +. C) /. 2 = D := (Midpoint_tran B C D).mp hBC2
  have hE2 : (A +. C) /. 2 = E := (Midpoint_tran A C E).mp hAC2
  -- L、M 的参数化（linear_com2''）
  have hCBne : C ≠ B := by
    intro h; apply hncol; exact Or.inr (Or.inr (Or.inr h.symm))
  have hCAne : C ≠ A := by
    intro h; apply hncol; exact Or.inr (Or.inr (Or.inl h.symm))
  obtain ⟨u, hLv⟩ := linear_com2'' L C B hLcol hCBne
  obtain ⟨v, hMv⟩ := linear_com2'' M C A hMcol hCAne
  -- 垂直条件转写（去原点、代中点坐标、代 L/M 参数式）
  unfold Perp at hAL hBM
  simp only [pminus_O] at hAL hBM
  rw [← hD2, hLv] at hAL
  rw [← hE2, hMv] at hBM
  have hALid : A -. (u *. B +. (1 - u) *. C) = A -. C -. u *.(B -. C) := by
    ext <;> simp [point_minus, point_plus, point_mult] <;> ring
  have hBMid : B -. (v *. A +. (1 - v) *. C) = B -. C -. v *.(A -. C) := by
    ext <;> simp [point_minus, point_plus, point_mult] <;> ring
  rw [hALid] at hAL
  rw [hBMid] at hBM
  have h7 : (A -. C -. u *.(B -. C)) ·. (B +. C) = 0 := e6_1 A B C u hAL
  have h9 : (B -. C -. v *.(A -. C)) ·. (A +. C) = 0 := e6_1 B A C v hBM
  -- 数量积展开
  have hABC : (A -. C) ·. (B +. C) = A ·. C - C ·. C := by
    rw [Pmagn_minus_distr', Pmagn_plus_distr, Pmagn_plus_distr, hab, hCB, hbc]
    ring
  have hBBC : (B -. C) ·. (B +. C) = B ·. B - C ·. C := by
    rw [Pmagn_minus_distr', Pmagn_plus_distr, Pmagn_plus_distr, hCB]
    ring
  have hBAC : (B -. C) ·. (A +. C) = B ·. C - C ·. C := by
    rw [Pmagn_minus_distr', Pmagn_plus_distr, Pmagn_plus_distr, hBA, hab, hCA]
    ring
  have hAAC : (A -. C) ·. (A +. C) = A ·. A - C ·. C := by
    rw [Pmagn_minus_distr', Pmagn_plus_distr, Pmagn_plus_distr, hCA]
    ring
  -- 垂直条件的参数方程
  have hiL : A ·. C - C ·. C = u * (B ·. B - C ·. C) := by
    have h7' := h7
    rw [Pmagn_minus_distr', Pmagn_mult_assoc, hABC, hBBC] at h7'
    linear_combination h7'
  have hiM : B ·. C - C ·. C = v * (A ·. A - C ·. C) := by
    have h9' := h9
    rw [Pmagn_minus_distr', Pmagn_mult_assoc, hBAC, hAAC] at h9'
    linear_combination h9'
  -- 重心关系
  have hAG3 : 3 * ((A -. C) ·. G) = A ·. A - C ·. C := by
    rw [(Pmagn_mult_assoc' 3 (A -. C) G).symm, ← hGsum,
        Pmagn_plus_distr, Pmagn_plus_distr,
        Pmagn_minus_distr', Pmagn_minus_distr', Pmagn_minus_distr']
    linarith
  have hBG3 : 3 * ((B -. C) ·. G) = B ·. B - C ·. C := by
    rw [(Pmagn_mult_assoc' 3 (B -. C) G).symm, ← hGsum,
        Pmagn_plus_distr, Pmagn_plus_distr,
        Pmagn_minus_distr', Pmagn_minus_distr', Pmagn_minus_distr']
    linarith
  -- 结论
  have hML : M -. L = v *.(A -. C) -. u *.(B -. C) := by
    rw [hMv, hLv]
    ext <;> simp [point_minus, point_plus, point_mult] <;> ring
  have hBAC0 : B ·. C - A ·. C = 0 := by linarith
  rw [hML, Pmagn_mult_assoc, Pmagn_minus_distr', Pmagn_mult_assoc, Pmagn_mult_assoc]
  linear_combination v * hAG3 - u * hBG3 - hiM + hiL + hBAC0

-- ============================================================
--  例 7 及其辅助引理（平行四边形的向量表示）
-- ============================================================

-- 辅助引理：由 PA +. PC = PD -. P 得 PD = PA +. PC -. PO。
-- （P/pO = O -. P = -P，故减去 P/pO 即加上 P。）
lemma E7_1 (A C D P : Point) (h : P /p A +. P /p C = P /p D -. P) :
    P /p D = P /p A +. P /p C -. P /p O := by
  have hO : P /p O = -P := pminus_O_A P
  have hnn : -(-P) = P := by
    ext
    · show -(-P.x) = P.x
      ring
    · show -(-P.y) = P.y
      ring
  have h1 : P /p A +. P /p C +. P = P /p D := by
    rw [h, pplus_minus_assoc', pminus_eq_O, pminus_O]
  rw [hO, ← pplus_minus_tran, hnn]
  exact h1.symm

-- 辅助引理：由 PA +. PC = 2·PE 得 PE = 1/2·(PA +. PC)。
lemma E7_2 (A C E P : Point) (h : P /p A +. P /p C = 2 *. (P /p E)) :
    P /p E = 1 / 2 *. (P /p A +. P /p C) := by
  rw [h, pmult_l_l_p]
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, pmult_1_p]

-- 例7 平行四边形（顶点 O、A、C、D）对角线交点 E，P 为任意一点，则
-- PD = PA +. PC -. PO 且 PE = 1/2·(PA +. PC)。
-- 证明思路（与 Coq 一致）：Plg 给出 E 为 AC 与 OD 的公共中点，
-- 故 A +. C = 2·E 且 A +. C = D；用 Oprod_plus_distr_ex'（配平项 (1+1-1)·O 消去）
-- 与 Oprod_plus_distr 把点积等式化为 P 的向量式，再由 E7_1、E7_2 收尾。
-- （注：假设 Parallelogram A O C D 在代数证明中未被用到，与 Coq 一致。）
theorem example_7 (A C D E P : Point) :
    Parallelogram A O C D → Plg E A O C D →
    P /p D = P /p A +. P /p C -. P /p O ∧
    P /p E = 1 / 2 *. (P /p A +. P /p C) := by
  intro _hPlg hPlgE
  obtain ⟨_, hE1, hE2⟩ := hPlgE
  -- E 为对角线 AC 与 OD 的公共中点
  have hAC2 : A +. C = 2 *. E := (locate_P_2 A C E).mpr hE1
  have hOD2 : O +. D = 2 *. E := (locate_P_2 O D E).mpr hE2
  have hD2E : D = 2 *. E := by rw [pplus_O_p] at hOD2; exact hOD2
  have hACD : A +. C = D := by rw [hAC2, hD2E]
  -- E7_1 的前提：1·A +. 1·C = 1·D = 1·D +. 1·O
  have h1 : (1 : ℝ) *. A +. (1 : ℝ) *. C = (1 : ℝ) *. D := by
    rw [pmult_1_p, pmult_1_p, pmult_1_p]
    exact hACD
  have h2 : (1 : ℝ) *. A +. (1 : ℝ) *. C
      = (1 : ℝ) *. D +. (1 + 1 - 1) *. O := by
    rw [show (1 + 1 - 1 : ℝ) = 1 by norm_num, pmult_1_p, pmult_1_p, pmult_1_p, pmult_1_p,
        pplus_O_p']
    exact hACD
  have hE71 := Oprod_plus_distr_ex' A C D P 1 1 1 h1 h2
  rw [show (1 + 1 - 1 : ℝ) = 1 by norm_num] at hE71
  simp only [pmult_1_p] at hE71
  -- hE71 : P /p A +. P /p C = P /p D -. P
  -- E7_2 的前提：1·A +. 1·C = 2·E
  have h3 : (1 : ℝ) *. A +. (1 : ℝ) *. C = (1 + 1) *. E := by
    rw [pmult_1_p, pmult_1_p, show (1 + 1 : ℝ) = 2 by norm_num]
    exact hAC2
  have hE72 := Oprod_plus_distr A C E P 1 1 h3
  rw [show (1 + 1 : ℝ) = 2 by norm_num] at hE72
  simp only [pmult_1_p] at hE72
  -- hE72 : P /p A +. P /p C = 2 *. P /p E
  exact ⟨E7_1 A C D P hE71, E7_2 A C E P hE72⟩

-- ============================================================
--  例 8 及其辅助引理（三角形面积比 25 : 252）
-- ============================================================

lemma e8_1 (A B C : Point) (u v : ℝ) (h : A +. B = u *. C) :
    v *. (A +. B) = (v * u) *. C := by
  rw [h, pmult_l_l_p]

-- 例8 在 ▲OBC 中：P 为 BC 中点，C = 3·Q（OQ:QC = 1:2），3·B = 4·S（OS:SB = 3:1）。
-- 三线 AP、BQ、CS 两两相交：N = OP∩BQ、M = OP∩SC、L = CS∩QB，则
-- 252·[LMN] = 25·[OBC]（点三重积表示有向面积）。
-- 证明思路（与 Coq 一致）：对三个 Inter_p 取特定 (u,v,r,s) 得向量式
-- 9·L = 2·O +. 6·B +. C、7·M = O +. 3·B +. 3·C、4·N = 2·O +. B +. C，
-- 化为分量等式后代入三重积的坐标公式，field_simp + ring 完成有理恒等式。
theorem example_8 (B C P Q S L M N : Point) :
    Triangle O B C → Midpoint P B C → C = 3 *. Q → 3 *. B = 4 *. S →
    Inter_p O P B Q N → Inter_p O P S C M → Inter_p C S Q B L →
    252 * point_3prod L M N = 25 * point_3prod O B C := by
  intro _hTri hP2 hQ hS hN4 hM4 hL4
  -- 中点条件化为向量式
  have hP2v : B +. C = 2 *. P := (locate_P_2 B C P).mpr hP2
  -- 关键向量等式：B +. 3Q = 2·O +. 2·P（即 B +. C = 2·P 的变形）
  have hBQ : (2 : ℝ) *. O +. (2 : ℝ) *. P = (1 : ℝ) *. B +. (3 : ℝ) *. Q := by
    rw [pmult_0_l, pplus_O_p, ← hP2v, pmult_1_p, ← hQ]
  -- 3·B +. 3·C = 6·P（e8_1 + 数乘分配）
  have h6P : (3 : ℝ) *. B +. (3 : ℝ) *. C = (6 : ℝ) *. P := by
    have h := e8_1 B C P 2 3 hP2v
    rw [pmult_plus_distr_l, show (3 * 2 : ℝ) = 6 by norm_num] at h
    exact h
  have h4S3C : (4 : ℝ) *. S +. (3 : ℝ) *. C = (6 : ℝ) *. P := by
    rw [← hS]
    exact h6P
  have h6B8S : (6 : ℝ) *. B = (8 : ℝ) *. S := by
    have h1 : (2 : ℝ) *. (3 *. B) = (2 : ℝ) *. (4 *. S) := by rw [hS]
    rw [pmult_l_l_p, pmult_l_l_p, show (2 * 3 : ℝ) = 6 by norm_num,
      show (2 * 4 : ℝ) = 8 by norm_num] at h1
    exact h1
  -- N：OP ∩ BQ，取 (u,v,r,s) = (2,2,1,3)
  have h4N : (4 : ℝ) *. N = (2 : ℝ) *. O +. B +. C := by
    have h1 := hN4 2 2 1 3 ⟨hBQ, by ring, by norm_num⟩
    rw [show (2 + 2 : ℝ) = 4 by norm_num, ← hP2v, ← pplus_assoc] at h1
    exact h1.symm
  -- M：OP ∩ SC，取 (u,v,r,s) = (1,6,4,3)
  have h7M : (7 : ℝ) *. M = O +. (3 : ℝ) *. B +. (3 : ℝ) *. C := by
    have sideM : (1 : ℝ) *. O +. (6 : ℝ) *. P = (4 : ℝ) *. S +. (3 : ℝ) *. C := by
      rw [pmult_1_p, pplus_O_p]
      exact h4S3C.symm
    have h1 := hM4 1 6 4 3 ⟨sideM, by ring, by norm_num⟩
    rw [show (1 + 6 : ℝ) = 7 by norm_num, pmult_1_p, pplus_O_p, ← h6P] at h1
    rw [pplus_O_p]
    exact h1.symm
  -- L：CS ∩ QB，取 (u,v,r,s) = (1,8,3,6)
  have h9L : (9 : ℝ) *. L = (2 : ℝ) *. O +. (6 : ℝ) *. B +. C := by
    have sideL : (1 : ℝ) *. C +. (8 : ℝ) *. S = (3 : ℝ) *. Q +. (6 : ℝ) *. B := by
      rw [pmult_1_p, ← hQ, ← h6B8S]
    have h1 := hL4 1 8 3 6 ⟨sideL, by ring, by norm_num⟩
    rw [show (1 + 8 : ℝ) = 9 by norm_num, pmult_1_p, ← h6B8S] at h1
    rw [← h1, pplus_comm, pmult_0_l, pplus_O_p]
  -- 分量等式
  have hLx : L.x = (2 * O.x + 6 * B.x + C.x) / 9 := by
    have h := congrArg Point.x h9L
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (9 : ℝ) ≠ 0)]
    linear_combination h
  have hLy : L.y = (2 * O.y + 6 * B.y + C.y) / 9 := by
    have h := congrArg Point.y h9L
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (9 : ℝ) ≠ 0)]
    linear_combination h
  have hMx : M.x = (O.x + 3 * B.x + 3 * C.x) / 7 := by
    have h := congrArg Point.x h7M
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (7 : ℝ) ≠ 0)]
    linear_combination h
  have hMy : M.y = (O.y + 3 * B.y + 3 * C.y) / 7 := by
    have h := congrArg Point.y h7M
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (7 : ℝ) ≠ 0)]
    linear_combination h
  have hNx : N.x = (2 * O.x + B.x + C.x) / 4 := by
    have h := congrArg Point.x h4N
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
    linear_combination h
  have hNy : N.y = (2 * O.y + B.y + C.y) / 4 := by
    have h := congrArg Point.y h4N
    simp only [point_mult, point_plus] at h
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
    linear_combination h
  -- 代入三重积坐标公式
  unfold point_3prod
  rw [hLx, hLy, hMx, hMy, hNx, hNy]
  field_simp
  ring

-- ============================================================
--  例 9 及其辅助引理（Pappus 定理）
-- ============================================================

lemma neq0_1 (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hv1 : v ≠ 1) :
    u * v * v - u * v ≠ 0 ∧ u - u * v ≠ 0 := by
  constructor
  · have h : u * v * v - u * v = u * v * (v - 1) := by ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero hu hv) (sub_ne_zero_of_ne hv1)
  · have h : u - u * v = u * (1 - v) := by ring
    rw [h]
    exact mul_ne_zero hu (sub_ne_zero_of_ne (Ne.symm hv1))

lemma neq0_2 (r m u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : r * v - r * m - m * u ≠ 0)
    (h2 : r + u - u * v + v - m - 1 ≠ 0) :
    (r * v - r * m - m * u) / (u * v * (r + u - u * v + v - m - 1)) ≠ 0 := by
  exact div_ne_zero h1 (mul_ne_zero (mul_ne_zero hu hv) h2)

-- 例9（Pappus 定理）设 A、B、C 共线，D、E、F 共线（共线性由加权等式 h6、h7 编码），
-- E = u·A、B = v·D（故 AE、BD 两线过原点 O，其交点即 O），Q = AF∩CD、R' = CE∩BF，
-- 则 Q、O、R' 共线。
-- 证明思路（与 Coq 一致）：由 Inter_p' 的实例化得 Q 的方程
-- κ·Q = (r+u-uv)·A + (v-m-1)·F（κ = r+u-uv+v-m-1）；由 h7 解出
-- A = ((m+1-v)/(u-uv))·F + (m/(uv²-uv))·B 并代入，得 κ·Q = c'·B + d'·F；
-- 而 R' 的方程给出 (c'+d')·R' = c'·B + d'·F，且标量恒等式 uv·(c'+d') = ρ
-- （ρ = rv-rm-mu），故 (uvκ)·Q = ρ·R'，即 Q = λ·R'（λ = ρ/(uvκ) ≠ 0），
-- 由 col 的定义（第一析取支 vector O Q = λ·vector O R'）完成。
-- （Coq 中的 H13、H14 及改写后的 H6 在证明中未被使用，此处省略；
--   Coq 语句中多余的数量积标量 a b c d 亦省略。）
theorem Pappus (A B C D E F P Q R' : Point) (u v r m : ℝ) :
    col A B C → col D E F → Inter_p' A E B D O → Inter_p' A F C D Q →
    Inter_p' C E B F R' → E = u *. A → B = v *. D →
    r *. A +. (u - 1) *. B = (r + u - 1) *. C →
    m *. D +. (1 - v) *. E = (m + 1 - v) *. F →
    u ≠ 0 → v ≠ 0 → v ≠ 1 →
    r * v - r * m - m * u ≠ 0 →
    r + u - u * v + v - m - 1 ≠ 0 →
    col Q O R' := by
  intro _hcol1 _hcol2 _hO4 hQ4 hR4 hE hB _h6 h7 hu hv hv1 hρ hκ
  obtain ⟨hd1, hd2⟩ := neq0_1 u v hu hv hv1
  -- hd1 : u*v² - uv ≠ 0，hd2 : u - uv ≠ 0
  -- Q 的交点方程（Inter_p' A F C D Q 实例化，对应 Coq 的 H2_eq1）
  obtain ⟨_, _, hQ1, _⟩ := hQ4 (r + u - u*v) (v - m - 1) (r + u - 1) (v - u*v - m)
  rw [show (((r + u - u*v) + (v - m - 1) : ℝ)) = (r + u - u*v + v - m - 1) by ring] at hQ1
  -- hQ1 : κ·Q = (r+u-uv)·A + (v-m-1)·F
  -- D = (1/v)·B（Coq 的 H16）
  have hD : D = (1 / v) *. B := by
    rw [hB, pmult_l_l_p, show ((1 / v) * v : ℝ) = 1 by field_simp, pmult_1_p]
  -- m·D + (1-v)·u·A = (m+1-v)·F（Coq 中改写后的 H7）
  have h7a : m *. D +. (1 - v) *. (u *. A) = (m + 1 - v) *. F := by
    rw [← h7, hE]
  -- (m/v)·B + (u-uv)·A = (m+1-v)·F
  have h7b : (m / v) *. B +. (u - u*v) *. A = (m + 1 - v) *. F := by
    rw [← h7a, hD, pmult_l_l_p, show (m * (1 / v) : ℝ) = m / v by ring,
      pmult_l_l_p, show ((1 - v) * u : ℝ) = u - u*v by ring]
  -- A 的表达式（Coq 的 H20）：A = ((m+1-v)/(u-uv))·F + (m/(uv²-uv))·B
  have hA : A = ((m + 1 - v) / (u - u*v)) *. F +. (m / (u*v*v - u*v)) *. B := by
    have h1 : (m + 1 - v) *. F -. (m / v) *. B = (u - u*v) *. A :=
      (pplus_minus ((m + 1 - v) *. F) ((m / v) *. B) ((u - u*v) *. A)).mpr h7b.symm
    -- 乘 1/(u-uv) 解出 A
    have h2 : A = (1 / (u - u*v)) *. ((m + 1 - v) *. F -. (m / v) *. B) := by
      have h3 := congrArg (fun X : Point => (1 / (u - u*v)) *. X) h1.symm
      rw [pmult_l_l_p, show ((1 / (u - u*v)) * (u - u*v) : ℝ) = 1 by field_simp [hd2],
        pmult_1_p] at h3
      exact h3
    rw [h2, pmult_minus_distr, pmult_l_l_p, pmult_l_l_p,
      show ((1 / (u - u*v)) * (m + 1 - v) : ℝ) = (m + 1 - v) / (u - u*v) by ring,
      show ((1 / (u - u*v)) * (m / v) : ℝ) = m / (v * (u - u*v)) by
        field_simp [hv, hd2],
      ← pplus_minus_tran, ← pmult_opp_p, pmult_l_l_p,
      show ((-1 : ℝ) * (m / (v * (u - u*v))) = m / (u*v*v - u*v)) by
        field_simp [hv, hd1, hd2]
        all_goals ring]
  -- R' 的交点方程（Inter_p' C E B F R' 实例化，对应 Coq 的 H3_eq2）
  obtain ⟨_, _, _, hR2⟩ := hR4 ((r*m + u*m - m) / (v - u*v))
    ((r*v*u - r*v + m*r) / (u*u*v - u*v))
    ((r*m + u*m - u*v*m) / (u*v*v - u*v)) ((r*m + r - r*v) / (u - u*v))
  -- 标量恒等式（系数合并，纯标量 field_simp）
  have hFd : (r + u - u*v) * ((m + 1 - v) / (u - u*v)) + (v - m - 1)
      = (r*m + r - r*v) / (u - u*v) := by
    field_simp [hd2]
    ring
  have hBd : (r + u - u*v) * (m / (u*v*v - u*v))
      = (r*m + u*m - u*v*m) / (u*v*v - u*v) := by ring
  -- 关键方程：κ·Q = c'·B + d'·F = (c'+d')·R'（Coq 的 H21 + H3_eq2 合并）
  have hκQ : (r + u - u*v + v - m - 1) *. Q
      = ((r*m + u*m - u*v*m) / (u*v*v - u*v)
        + (r*m + r - r*v) / (u - u*v)) *. R' := by
    have hQ1' := hQ1
    rw [hA, pmult_plus_distr_l, pmult_l_l_p, pmult_l_l_p] at hQ1'
    rw [pplus_assoc, pplus_comm
      (((r + u - u*v) * (m / (u*v*v - u*v))) *. B) ((v - m - 1) *. F),
      ← pplus_assoc, ← pmult_plus_distr_l', hFd, hBd,
      pplus_comm ((r*m + r - r*v) / (u - u*v) *. F)
        ((r*m + u*m - u*v*m) / (u*v*v - u*v) *. B), ← hR2] at hQ1'
    exact hQ1'
  -- 标量恒等式：uv·(c'+d') = ρ（Coq 的 H22）
  have hscale : u*v*(((r*m + u*m - u*v*m) / (u*v*v - u*v))
      + (r*m + r - r*v) / (u - u*v)) = r*v - r*m - m*u := by
    field_simp [hd1, hd2]
    ring
  -- (uvκ)·Q = ρ·R'
  have hkey : (u*v*(r + u - u*v + v - m - 1)) *. Q = (r*v - r*m - m*u) *. R' := by
    rw [← pmult_l_l_p, hκQ, pmult_l_l_p, hscale]
  -- Q = λ·R'，λ = ρ/(uvκ)
  have hQeq : Q = (r*v - r*m - m*u) / (u*v*(r + u - u*v + v - m - 1)) *. R' := by
    have h1 := congrArg
      (fun X : Point => (1 / (u*v*(r + u - u*v + v - m - 1))) *. X) hkey
    rw [pmult_l_l_p, pmult_l_l_p,
      show ((1 / (u*v*(r + u - u*v + v - m - 1)))
        * (u*v*(r + u - u*v + v - m - 1)) : ℝ) = 1 by field_simp,
      pmult_1_p,
      show ((1 / (u*v*(r + u - u*v + v - m - 1))) * (r*v - r*m - m*u) : ℝ)
        = (r*v - r*m - m*u) / (u*v*(r + u - u*v + v - m - 1)) by ring] at h1
    exact h1
  -- 结论：col Q O R'（第一析取支）
  refine Or.inl ⟨(r*v - r*m - m*u) / (u*v*(r + u - u*v + v - m - 1)), ?_, ?_⟩
  · exact neq0_2 r m u v hu hv hρ hκ
  · simp only [vector, pminus_O]
    exact hQeq

end PG
