import Mathlib

/-!
# JSP-000733 / Erdős Problem 882: subset sums forming a primitive set

For `A ⊆ {1,…,n}` whose nonempty subset sums are pairwise incomparable under
divisibility, let `R n` be the largest possible `A.card`. Erdős–Lev–Rauzy–
Sándor–Sárközy (Discrete Math. 200 (1999), Thm 5) proved

    log₂ n − 1 < R n < log₂ n + log₂ log₂ n / (2 log 2) + c,

i.e. `R n = log₂ n + O(log log n)`. We formalize the two-sided bound.

* Lower bound: the witness `{2^m − 2^i | i < m}` for `m = ⌊log₂ n⌋` has
  `m` elements and primitive subset sums (binary-weight argument).
* Upper bound: primitivity forces all subset sums to be distinct (equal
  sums `Σ S = Σ T` with `S ≠ T` give disjoint `S ∖ T`, `T ∖ S` with equal
  sums `s`, and then `s` and `2s` are comparable subset sums); then
  `2^k ≤ k·n` by pigeonhole, whence `k ≤ log₂ n + O(log log n)`.
-/

open Finset

namespace Jsp000733

/-- The set of distinct values of nonempty subset sums of `A`. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter fun S ↦ S.Nonempty).image fun S ↦ ∑ a ∈ S, a

/-- `A` is admissible for `n`: it lies in `{1,…,n}` and its distinct nonempty
subset sums form a primitive set under divisibility. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧
    ∀ x ∈ subsetSums A, ∀ y ∈ subsetSums A, x ∣ y → x = y

/-- `R n`: the largest cardinality of an admissible set. -/
noncomputable def R (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A ↦
    ∀ x ∈ subsetSums A, ∀ y ∈ subsetSums A, x ∣ y → x = y).sup Finset.card

lemma admissible_card_le {n : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    A.card ≤ R n := by
  classical
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA.2⟩

lemma R_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = R n := by
  classical
  have hempty : ∅ ∈ (Finset.Icc 1 n).powerset.filter (fun A ↦
      ∀ x ∈ subsetSums A, ∀ y ∈ subsetSums A, x ∣ y → x = y) := by
    simp [subsetSums]
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_mem_eq_sup _ ⟨∅, hempty⟩ Finset.card
  refine ⟨A, ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2⟩, hmax.symm⟩

/-! ## Lower bound: the Erdős–Sárközy construction

### Binary-weight lemmas

`bitWeight n` counts the ones in the binary expansion of `n`; `bitDefect n`
counts the carries `n − bitWeight n`. The key estimate: if a divisor `d ≥ 2`
satisfies `d * σ = c * 2 ^ m + τ` with `σ, τ` sums of distinct powers of two
below `m`, then `|T| + bitWeight c ≤ |S| * bitWeight d`, which forces
`|S| = 1` and `d = c + 1`, after which the size constraints clash. -/

/-- The number of ones in the binary expansion of `n`. -/
def bitWeight (n : ℕ) : ℕ := n.bitIndices.length

@[simp] lemma bitWeight_zero : bitWeight 0 = 0 := rfl
@[simp] lemma bitWeight_one : bitWeight 1 = 1 := rfl
@[simp] lemma bitWeight_two_mul (n : ℕ) : bitWeight (2 * n) = bitWeight n := by
  simp [bitWeight]
@[simp] lemma bitWeight_two_mul_add_one (n : ℕ) :
    bitWeight (2 * n + 1) = bitWeight n + 1 := by
  simp [bitWeight]
@[simp] lemma bitWeight_two_pow_mul (k n : ℕ) :
    bitWeight (2 ^ k * n) = bitWeight n := by
  simp [bitWeight]
@[simp] lemma bitWeight_two_pow (k : ℕ) : bitWeight (2 ^ k) = 1 := by
  simp [bitWeight]

lemma bitWeight_le (n : ℕ) : bitWeight n ≤ n := by
  have h := List.length_le_sum_of_one_le (n.bitIndices.map fun i ↦ 2 ^ i) (by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    have : 0 < 2 ^ i := Nat.pow_pos (by omega)
    omega)
  simpa [bitWeight] using h

lemma bitWeight_succ_le (n : ℕ) : bitWeight (n + 1) ≤ bitWeight n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
      · simp
      · have hi := ih q (by omega)
        rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega,
          bitWeight_two_mul, bitWeight_two_mul_add_one]
        omega

lemma bitWeight_add_pow_le (n k : ℕ) :
    bitWeight (n + 2 ^ k) ≤ bitWeight n + 1 := by
  induction k generalizing n with
  | zero => simpa using bitWeight_succ_le n
  | succ k ih =>
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [pow_succ, show 2 * q + 2 ^ k * 2 = 2 * (q + 2 ^ k) by omega,
          bitWeight_two_mul]
        simpa using ih q
      · have hi := ih q
        rw [pow_succ,
          show 2 * q + 1 + 2 ^ k * 2 = 2 * (q + 2 ^ k) + 1 by omega,
          bitWeight_two_mul_add_one, bitWeight_two_mul_add_one]
        omega

lemma bitWeight_add_geomSum_le (n : ℕ) (s : Finset ℕ) :
    bitWeight (n + ∑ i ∈ s, 2 ^ i) ≤ bitWeight n + s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      calc
        bitWeight (n + (2 ^ i + ∑ j ∈ s, 2 ^ j))
            = bitWeight ((n + ∑ j ∈ s, 2 ^ j) + 2 ^ i) := by
            congr 1; omega
        _ ≤ bitWeight (n + ∑ j ∈ s, 2 ^ j) + 1 := bitWeight_add_pow_le _ _
        _ ≤ bitWeight n + (insert i s).card := by
            rw [Finset.card_insert_of_notMem hi]; omega

lemma bitWeight_add_le (n r : ℕ) :
    bitWeight (n + r) ≤ bitWeight n + bitWeight r := by
  have h := bitWeight_add_geomSum_le n r.bitIndices.toFinset
  rw [Finset.sum_toFinset_bitIndices_two_pow] at h
  simpa [bitWeight, List.toFinset_card_of_nodup Nat.bitIndices_nodup] using h

lemma bitWeight_sum_le {α : Type*} (s : Finset α) (f : α → ℕ) :
    bitWeight (∑ i ∈ s, f i) ≤ ∑ i ∈ s, bitWeight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (bitWeight_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma bitWeight_mul_le (n r : ℕ) :
    bitWeight (n * r) ≤ bitWeight n * bitWeight r := by
  let s := r.bitIndices.toFinset
  have hr : ∑ i ∈ s, 2 ^ i = r := Finset.sum_toFinset_bitIndices_two_pow r
  calc
    bitWeight (n * r) = bitWeight (∑ i ∈ s, 2 ^ i * n) := by
      rw [← Finset.sum_mul, hr, Nat.mul_comm]
    _ ≤ ∑ i ∈ s, bitWeight (2 ^ i * n) := bitWeight_sum_le s _
    _ = s.card * bitWeight n := by simp
    _ = bitWeight n * bitWeight r := by
        simp [s, bitWeight, List.toFinset_card_of_nodup Nat.bitIndices_nodup,
          Nat.mul_comm]

lemma bitWeight_eq_digits_sum (n : ℕ) :
    bitWeight n = (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
      · by_cases hq : q = 0
        · subst q; simp
        · rw [Nat.digits_base_mul (b := 2) (m := q) (by omega)
            (Nat.pos_of_ne_zero hq)]
          simp only [List.sum_cons, zero_add, bitWeight_two_mul]
          exact ih q (by omega)
      · rw [Nat.digits_def' (b := 2) (by omega) (by omega)]
        have hmod : (2 * q + 1) % 2 = 1 := by omega
        have hdiv : (2 * q + 1) / 2 = q := by omega
        rw [hmod, hdiv, List.sum_cons, bitWeight_two_mul_add_one,
          ih q (by omega)]
        omega

/-- Digits below `2 ^ m` and above it occupy disjoint blocks. -/
lemma bitWeight_block (r c m : ℕ) (hr : r < 2 ^ m) :
    bitWeight (c * 2 ^ m + r) = bitWeight c + bitWeight r := by
  by_cases hc : c = 0
  · subst c; simp
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  have hlen : (Nat.digits 2 r).length ≤ m :=
    (Nat.digits_length_le_iff (by omega) r).2 hr
  have hd := Nat.digits_append_zeroes_append_digits
    (b := 2) (k := m - (Nat.digits 2 r).length) (m := c) (n := r)
    (by omega) hcpos
  rw [Nat.add_sub_of_le hlen] at hd
  have hsum := congrArg List.sum hd
  simp only [List.sum_append_nat, List.sum_replicate, nsmul_zero, add_zero]
    at hsum
  rw [bitWeight_eq_digits_sum, bitWeight_eq_digits_sum,
    bitWeight_eq_digits_sum]
  rw [show c * 2 ^ m + r = r + 2 ^ m * c by ac_rfl]
  exact hsum.symm.trans (Nat.add_comm _ _)

/-- `n − bitWeight n`: the number of binary carries below `n`. -/
def bitDefect (n : ℕ) : ℕ := n - bitWeight n

lemma bitDefect_succ_mono (n : ℕ) : bitDefect n ≤ bitDefect (n + 1) := by
  have hn := bitWeight_le n
  have hn1 := bitWeight_le (n + 1)
  have hs := bitWeight_succ_le n
  simp only [bitDefect]; omega

lemma bitDefect_mono : Monotone bitDefect :=
  monotone_nat_of_le_succ bitDefect_succ_mono

lemma bitDefect_lt_add_two (n : ℕ) :
    bitDefect n < bitDefect (n + 2) := by
  have hn := bitWeight_le n
  have hn2 := bitWeight_le (n + 2)
  have hs := bitWeight_add_pow_le n 1
  norm_num at hs
  simp only [bitDefect]; omega

lemma eq_add_one_of_bitDefect_eq {c d : ℕ} (hcd : c < d)
    (hdef : bitDefect c = bitDefect d) : d = c + 1 := by
  by_contra h
  have hc2 : c + 2 ≤ d := by omega
  have hle := bitDefect_mono hc2
  have hlt := bitDefect_lt_add_two c
  omega

lemma bitDefect_pos {d : ℕ} (hd : 2 ≤ d) : 0 < bitDefect d := by
  have hle := bitDefect_mono hd
  have : bitDefect 2 = 1 := rfl
  omega

/-- Sum of the binary place values indexed by `S`. -/
def bitSum (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

lemma bitWeight_bitSum (S : Finset ℕ) : bitWeight (bitSum S) = S.card := by
  unfold bitSum bitWeight
  rw [← List.toFinset_card_of_nodup Nat.bitIndices_nodup,
    Finset.toFinset_bitIndices_sum_two_pow]

lemma bitSum_lt_pow {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    bitSum S < 2 ^ m := by
  apply Nat.geomSum_lt (m := 2) (by omega)
  intro i hi
  exact Finset.mem_range.mp (hS hi)

lemma bitSum_pos {S : Finset ℕ} (hS : S.Nonempty) : 0 < bitSum S := by
  obtain ⟨i, hi⟩ := hS
  have hpow : 0 < 2 ^ i := Nat.pow_pos (by omega)
  exact hpow.trans_le (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi)

/-- A subset sum of the construction indexed by `S ⊆ {0,…,m−1}`. -/
def indexedSum (m : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ i ∈ S, (2 ^ m - 2 ^ i)

lemma indexedSum_eq (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    indexedSum m S = S.card * 2 ^ m - bitSum S := by
  induction S using Finset.induction_on with
  | empty => simp [indexedSum, bitSum]
  | @insert i S hi ih =>
      have him : i < m := Finset.mem_range.mp (hS (by simp))
      have hSi : S ⊆ Finset.range m := fun j hj ↦ hS (by simp [hj])
      have hqle : bitSum S ≤ S.card * 2 ^ m := by
        calc
          bitSum S = ∑ j ∈ S, 2 ^ j := rfl
          _ ≤ ∑ _j ∈ S, 2 ^ m := Finset.sum_le_sum fun j hj ↦
            pow_le_pow_right₀ (by omega) (Finset.mem_range.mp (hSi hj)).le
          _ = S.card * 2 ^ m := by simp
      unfold bitSum at hqle
      simp only [indexedSum, bitSum, Finset.sum_insert hi,
        Finset.card_insert_of_notMem hi]
      rw [show ∑ j ∈ S, (2 ^ m - 2 ^ j) =
          S.card * 2 ^ m - ∑ j ∈ S, 2 ^ j by
        simpa [indexedSum, bitSum] using ih hSi]
      have hcard : (S.card + 1) * 2 ^ m = S.card * 2 ^ m + 2 ^ m := by ring
      rw [hcard]
      have hiM : 2 ^ i ≤ 2 ^ m := pow_le_pow_right₀ (by omega) him.le
      omega

/-- The divisor obstruction: `x | y` with `x ≠ y` is impossible. -/
theorem indexedSum_dvd_indexedSum
    {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hT : T ⊆ Finset.range m)
    (hneS : S.Nonempty) (hneT : T.Nonempty)
    (hdiv : indexedSum m S ∣ indexedSum m T) :
    indexedSum m S = indexedSum m T := by
  have hk : 0 < S.card := Finset.card_pos.mpr hneS
  have hl : 0 < T.card := Finset.card_pos.mpr hneT
  have hq : 0 < bitSum S := bitSum_pos hneS
  have hr : 0 < bitSum T := bitSum_pos hneT
  have hqM : bitSum S < 2 ^ m := bitSum_lt_pow hS
  have hrM : bitSum T < 2 ^ m := bitSum_lt_pow hT
  have hMpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hxq : indexedSum m S + bitSum S = S.card * 2 ^ m := by
    rw [indexedSum_eq m S hS]
    exact Nat.sub_add_cancel (hqM.le.trans (Nat.le_mul_of_pos_left _ hk))
  have hyr : indexedSum m T + bitSum T = T.card * 2 ^ m := by
    rw [indexedSum_eq m T hT]
    exact Nat.sub_add_cancel (hrM.le.trans (Nat.le_mul_of_pos_left _ hl))
  obtain ⟨d, hd⟩ := hdiv
  have hle2S : 2 ^ m ≤ S.card * 2 ^ m := Nat.le_mul_of_pos_left _ hk
  have hle2T : 2 ^ m ≤ T.card * 2 ^ m := Nat.le_mul_of_pos_left _ hl
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      simp only [mul_zero] at hd
      omega
    · exact h0
  by_cases hd1 : d = 1
  · subst d; rw [mul_one] at hd; exact hd.symm
  have hd2 : 2 ≤ d := by omega
  exfalso
  -- localize `y = d*x` inside the `2^m`-blocks around `S.card` and `T.card`
  have hxlt : indexedSum m S < S.card * 2 ^ m := by omega
  have hylt : indexedSum m T < T.card * 2 ^ m := by omega
  have hxlow : (S.card - 1) * 2 ^ m < indexedSum m S := by
    have e : (S.card - 1) * 2 ^ m = S.card * 2 ^ m - 2 ^ m := by
      rw [Nat.sub_mul, one_mul]
    omega
  have hylow : (T.card - 1) * 2 ^ m < indexedSum m T := by
    have e : (T.card - 1) * 2 ^ m = T.card * 2 ^ m - 2 ^ m := by
      rw [Nat.sub_mul, one_mul]
    omega
  have hdup : indexedSum m T < (d * S.card) * 2 ^ m := by
    have hh := Nat.mul_lt_mul_of_pos_right hxlt hdpos
    rw [hd]; convert hh using 1; ring
  have hlcoef : T.card - 1 < d * S.card :=
    (Nat.mul_lt_mul_right hMpos).mp (hylow.trans hdup)
  have hldk : T.card ≤ d * S.card := by omega
  have hdlow : (d * (S.card - 1)) * 2 ^ m < indexedSum m T := by
    have hh := Nat.mul_lt_mul_of_pos_right hxlow hdpos
    rw [hd]; convert hh using 1; ring
  have hcoef : d * (S.card - 1) < T.card :=
    (Nat.mul_lt_mul_right hMpos).mp (hdlow.trans hylt)
  -- the carry `c = d·|S| − |T|` satisfies `d·σ = c·2^m + τ`
  set c := d * S.card - T.card with hcdef
  have hcl : c + T.card = d * S.card := Nat.sub_add_cancel hldk
  have hdsplit : d * S.card = d * (S.card - 1) + d := by
    nth_rewrite 1 [← Nat.sub_add_cancel hk]; ring
  have hcd : c < d := by omega
  have hdc_eq : c * 2 ^ m + T.card * 2 ^ m = d * (S.card * 2 ^ m) := by
    calc c * 2 ^ m + T.card * 2 ^ m = (c + T.card) * 2 ^ m := by ring
      _ = d * S.card * 2 ^ m := by rw [hcl]
      _ = d * (S.card * 2 ^ m) := by ring
  have hxq' : bitSum S + indexedSum m S = S.card * 2 ^ m := by
    rw [Nat.add_comm]; exact hxq
  have heq : d * bitSum S = c * 2 ^ m + bitSum T := by
    have e3 : d * bitSum S + d * indexedSum m S = d * (S.card * 2 ^ m) := by
      rw [← Nat.mul_add, hxq']
    have hdx : d * indexedSum m S = indexedSum m T := by
      rw [Nat.mul_comm]; exact hd.symm
    have e4 : d * indexedSum m S + bitSum T = T.card * 2 ^ m := by
      rw [hdx]; exact hyr
    omega
  -- binary-weight count: `|T| + bitWeight c ≤ |S| · bitWeight d`
  have hblock : bitWeight (d * bitSum S) = bitWeight c + T.card := by
    rw [heq, bitWeight_block _ c m hrM, bitWeight_bitSum T]
  have hmul : bitWeight (d * bitSum S) ≤ S.card * bitWeight d := by
    have h := bitWeight_mul_le d (bitSum S)
    rw [bitWeight_bitSum S, Nat.mul_comm (bitWeight d) S.card] at h
    exact h
  have hwgt : bitWeight c + T.card ≤ S.card * bitWeight d := by
    rw [← hblock]; exact hmul
  -- squeeze `k · defect d ≤ defect c ≤ defect d`
  have hdpos2 : 0 < bitDefect d := bitDefect_pos hd2
  have hwc : bitWeight c ≤ c := bitWeight_le c
  have hwd : bitWeight d ≤ d := bitWeight_le d
  have hprod1 : S.card * d = c + T.card := by
    rw [Nat.mul_comm S.card d]; exact hcl.symm
  have hdef : S.card * bitDefect d ≤ bitDefect c := by
    simp only [bitDefect]
    rw [Nat.mul_sub, hprod1]
    omega
  have hmono : bitDefect c ≤ bitDefect d := bitDefect_mono hcd.le
  have hk1 : S.card = 1 := by
    by_contra _hne
    have hge2 : 2 ≤ S.card := by omega
    have h2 : 2 * bitDefect d ≤ S.card * bitDefect d :=
      Nat.mul_le_mul_right _ hge2
    omega
  have hdefeq : bitDefect c = bitDefect d := by
    rw [hk1] at hdef
    omega
  have hdc : d = c + 1 := eq_add_one_of_bitDefect_eq hcd hdefeq
  -- now `S = {i}` forces `d * 2^i = (d-1)·2^m + τ`, impossible for `d ≥ 2`
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hk1
  have him : i < m := Finset.mem_range.mp (hS (Finset.mem_singleton_self i))
  have hi2 : 2 * 2 ^ i ≤ 2 ^ m := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hbS : bitSum ({i} : Finset ℕ) = 2 ^ i := by simp [bitSum]
  rw [hbS] at heq
  have hsc : 2 ^ m ≤ c * 2 ^ m :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hdq : d * 2 ^ m = c * 2 ^ m + 2 ^ m := by
    rw [hdc]; ring
  have hdmul : 2 * (d * 2 ^ i) ≤ d * 2 ^ m := by
    calc 2 * (d * 2 ^ i) = d * (2 * 2 ^ i) := by ring
      _ ≤ d * 2 ^ m := Nat.mul_le_mul_left d hi2
  omega

/-- The construction `{2^m − 2^i | i < m}`. -/
def construction (m : ℕ) : Finset ℕ :=
  (Finset.range m).image fun i ↦ 2 ^ m - 2 ^ i

private lemma construction_inj {m : ℕ} :
    Set.InjOn (fun i ↦ 2 ^ m - 2 ^ i) (Finset.range m) := by
  intro i hi j hj hij
  dsimp only at hij
  have hi2 : 2 ^ i ≤ 2 ^ m :=
    pow_le_pow_right₀ (by omega) (Finset.mem_range.mp hi).le
  have hj2 : 2 ^ j ≤ 2 ^ m :=
    pow_le_pow_right₀ (by omega) (Finset.mem_range.mp hj).le
  have : 2 ^ i = 2 ^ j := by omega
  exact Nat.pow_right_injective (by omega) this

lemma construction_card (m : ℕ) : (construction m).card = m := by
  rw [construction, Finset.card_image_of_injOn construction_inj,
    Finset.card_range]

lemma construction_mem_iff {m a : ℕ} :
    a ∈ construction m ↔ ∃ i < m, a = 2 ^ m - 2 ^ i := by
  constructor
  · intro ha
    rw [construction, Finset.mem_image] at ha
    obtain ⟨i, hi, hiq⟩ := ha
    exact ⟨i, Finset.mem_range.mp hi, hiq.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

lemma construction_pos {m a : ℕ} (ha : a ∈ construction m) : 0 < a := by
  rw [construction_mem_iff] at ha
  obtain ⟨i, him, rfl⟩ := ha
  have : 2 ^ i < 2 ^ m :=
    (Nat.pow_lt_pow_iff_right (by omega : (1:ℕ) < 2)).mpr him
  omega

lemma construction_le_pow {m a : ℕ} (ha : a ∈ construction m) : a ≤ 2 ^ m := by
  rw [construction_mem_iff] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact Nat.sub_le _ _

lemma construction_subset_Icc {m n : ℕ} (hmn : 2 ^ m ≤ n) :
    construction m ⊆ Finset.Icc 1 n := by
  intro a ha
  exact Finset.mem_Icc.mpr ⟨construction_pos ha,
    (construction_le_pow ha).trans hmn⟩

/-- Every subset of `construction m` reindexes to `S ⊆ {0,…,m−1}`. -/
lemma recover_indices {m : ℕ} {U : Finset ℕ} (hU : U ⊆ construction m) :
    ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ U.card = S.card ∧
      (∑ a ∈ U, a) = indexedSum m S := by
  classical
  obtain ⟨P, hP, rfl⟩ : ∃ P ⊆ Finset.range m,
      U = P.image (fun i ↦ 2 ^ m - 2 ^ i) := by
    refine ⟨(Finset.range m).filter (fun i ↦ 2 ^ m - 2 ^ i ∈ U), ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · ext a
      constructor
      · intro ha
        have ha' := hU ha
        rw [construction, Finset.mem_image] at ha'
        obtain ⟨i, hi, rfl⟩ := ha'
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩, rfl⟩
      · intro ha
        rw [Finset.mem_image] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        exact (Finset.mem_filter.mp hi).2
  refine ⟨P, hP, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (construction_inj.mono hP)]
  · rw [Finset.sum_image (fun x hx y hy h ↦
      construction_inj (hP hx) (hP hy) h)]
    rfl

/-- Subset sums of the construction are pairwise incomparable. -/
theorem construction_primitive (m : ℕ) :
    ∀ x ∈ subsetSums (construction m), ∀ y ∈ subsetSums (construction m),
      x ∣ y → x = y := by
  intro x hx y hy hdiv
  rw [subsetSums, Finset.mem_image] at hx hy
  obtain ⟨U, hUf, rfl⟩ := hx
  obtain ⟨V, hVf, rfl⟩ := hy
  have hU' := Finset.mem_filter.mp hUf
  have hV' := Finset.mem_filter.mp hVf
  have hUsub : U ⊆ construction m := Finset.mem_powerset.mp hU'.1
  have hVsub : V ⊆ construction m := Finset.mem_powerset.mp hV'.1
  obtain ⟨S, hS, hcardS, hsumS⟩ := recover_indices hUsub
  obtain ⟨T, hT, hcardT, hsumT⟩ := recover_indices hVsub
  have hneS : S.Nonempty := Finset.card_pos.mp (hcardS ▸ hU'.2.card_pos)
  have hneT : T.Nonempty := Finset.card_pos.mp (hcardT ▸ hV'.2.card_pos)
  have hdiv' : indexedSum m S ∣ indexedSum m T := by
    rwa [← hsumS, ← hsumT]
  exact hsumS.trans ((indexedSum_dvd_indexedSum hS hT hneS hneT hdiv').trans
    hsumT.symm)

theorem R_lower (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n : ℝ) - 1 < (R n : ℝ) := by
  let m := Nat.log 2 n
  have h2m : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hA : Admissible n (construction m) :=
    ⟨construction_subset_Icc h2m, construction_primitive m⟩
  have hcard : (construction m).card ≤ R n := admissible_card_le hA
  rw [construction_card] at hcard
  have hlog : Real.logb 2 (n : ℝ) - 1 < (Nat.log 2 n : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))
    have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log 2 n := by
      simpa using Real.natFloor_logb_natCast 2 n
    rw [hf] at h
    have h' : Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1 := by exact_mod_cast h
    linarith
  calc Real.logb 2 (n : ℝ) - 1 < (Nat.log 2 n : ℝ) := hlog
    _ ≤ (R n : ℝ) := by exact_mod_cast hcard

/-! ## Upper bound -/

/-- If subset sums of `A` are primitive and all elements of `A` are positive,
then all nonempty subset sums are distinct: equal sums `Σ S = Σ T` with
`S ≠ T` would produce comparable sums `s` and `2s`. -/
lemma sums_injective_of_primitive {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a)
    (hprim : ∀ x ∈ subsetSums A, ∀ y ∈ subsetSums A, x ∣ y → x = y)
    {S T : Finset ℕ} (hS : S ⊆ A) (hT : T ⊆ A) (_hSn : S.Nonempty) (_hTn : T.Nonempty)
    (h : ∑ a ∈ S, a = ∑ a ∈ T, a) : S = T := by
  classical
  by_contra hne
  have hdiff : ∑ a ∈ S \ T, a = ∑ a ∈ T \ S, a := by
    have e1 := Finset.sum_sdiff (Finset.inter_subset_left : S ∩ T ⊆ S)
      (f := fun a : ℕ ↦ a)
    have e2 := Finset.sum_sdiff (Finset.inter_subset_right : S ∩ T ⊆ T)
      (f := fun a : ℕ ↦ a)
    rw [show S \ (S ∩ T) = S \ T by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]; tauto] at e1
    rw [show T \ (S ∩ T) = T \ S by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]; tauto] at e2
    omega
  by_cases hST : (S \ T).Nonempty
  · by_cases hTS : (T \ S).Nonempty
    · have spos : 0 < ∑ a ∈ S \ T, a :=
        Finset.sum_pos (fun a ha ↦ hpos a (hS (Finset.mem_sdiff.mp ha).1)) hST
      have hsub1 : S \ T ⊆ A := Finset.sdiff_subset.trans hS
      have hsub2 : (S \ T) ∪ (T \ S) ⊆ A :=
        Finset.union_subset hsub1 (Finset.sdiff_subset.trans hT)
      have hne2 : ((S \ T) ∪ (T \ S)).Nonempty :=
        hST.mono Finset.subset_union_left
      have hmem1 : ∑ a ∈ S \ T, a ∈ subsetSums A :=
        Finset.mem_image.mpr ⟨S \ T, Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr hsub1, hST⟩, rfl⟩
      have hmem2 : ∑ a ∈ (S \ T) ∪ (T \ S), a ∈ subsetSums A :=
        Finset.mem_image.mpr ⟨(S \ T) ∪ (T \ S), Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr hsub2, hne2⟩, rfl⟩
      have hdj : Disjoint (S \ T) (T \ S) :=
        Finset.disjoint_left.mpr (fun a ha hb ↦
          (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp ha).1)
      have h2s : ∑ a ∈ (S \ T) ∪ (T \ S), a = 2 * ∑ a ∈ S \ T, a := by
        rw [Finset.sum_union hdj, hdiff]; ring
      have heq := hprim _ hmem1 _ hmem2 ⟨2, by rw [h2s]; ring⟩
      omega
    · have hsub : T ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hTS)
      have e := Finset.sum_sdiff hsub (f := fun a : ℕ ↦ a)
      have spos : 0 < ∑ a ∈ S \ T, a :=
        Finset.sum_pos (fun a ha ↦ hpos a (hS (Finset.mem_sdiff.mp ha).1)) hST
      omega
  · have hsubS : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hST)
    by_cases hTS : (T \ S).Nonempty
    · have e := Finset.sum_sdiff hsubS (f := fun a : ℕ ↦ a)
      have spos : 0 < ∑ a ∈ T \ S, a :=
        Finset.sum_pos (fun a ha ↦ hpos a (hT (Finset.mem_sdiff.mp ha).1)) hTS
      omega
    · exact hne (Finset.Subset.antisymm hsubS
        (Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp hTS)))

/-- Nonempty subsets of `A` number `2^|A| − 1`. -/
lemma card_nonempty_subsets (A : Finset ℕ) :
    (A.powerset.filter fun S ↦ S.Nonempty).card = 2 ^ A.card - 1 := by
  have h1 : (A.powerset.filter fun S ↦ S.Nonempty) = A.powerset.erase ∅ := by
    ext S
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  rw [h1, Finset.card_erase_of_mem
    (Finset.mem_powerset.mpr (Finset.empty_subset A)), Finset.card_powerset]

/-- Pigeonhole: an admissible `A` has `2^A.card ≤ A.card * n + 1`. -/
lemma pow_card_le {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (_hne : A.Nonempty) :
    2 ^ A.card ≤ A.card * n + 1 := by
  classical
  have hpos : ∀ a ∈ A, 0 < a := fun a ha ↦ (Finset.mem_Icc.mp (hA.1 ha)).1
  have hle : ∀ a ∈ A, a ≤ n := fun a ha ↦ (Finset.mem_Icc.mp (hA.1 ha)).2
  have hinj : ∀ S ∈ A.powerset.filter (·.Nonempty),
      ∀ T ∈ A.powerset.filter (·.Nonempty),
      (∑ a ∈ S, a) = (∑ a ∈ T, a) → S = T := by
    intro S hSf T hTf h
    have hS' := Finset.mem_filter.mp hSf
    have hT' := Finset.mem_filter.mp hTf
    exact sums_injective_of_primitive hpos hA.2
      (Finset.mem_powerset.mp hS'.1) (Finset.mem_powerset.mp hT'.1) hS'.2 hT'.2 h
  have hcard : (subsetSums A).card = 2 ^ A.card - 1 := by
    rw [subsetSums, Finset.card_image_of_injOn hinj, card_nonempty_subsets]
  have hbounds : subsetSums A ⊆ Finset.Icc 1 (A.card * n) := by
    intro x hx
    rw [subsetSums, Finset.mem_image] at hx
    obtain ⟨S, hSf, rfl⟩ := hx
    have hS' := Finset.mem_filter.mp hSf
    have hSA : S ⊆ A := Finset.mem_powerset.mp hS'.1
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Finset.sum_pos (fun a ha ↦ hpos a (hSA ha)) hS'.2
    · calc ∑ a ∈ S, a ≤ ∑ _a ∈ S, n :=
            Finset.sum_le_sum fun a ha ↦ hle a (hSA ha)
          _ = S.card * n := by simp
          _ ≤ A.card * n := Nat.mul_le_mul_right _ (Finset.card_le_card hSA)
  have hcnt : (subsetSums A).card ≤ A.card * n := by
    have hcc := Finset.card_le_card hbounds
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hcc
  omega

/-- `R n ≤ n` since admissible sets live inside `{1,…,n}`. -/
lemma R_le (n : ℕ) : R n ≤ n := by
  obtain ⟨A, hA, hcard⟩ := R_attained n
  rw [← hcard]
  exact (Finset.card_le_card hA.1).trans (by simp)

lemma one_le_R {n : ℕ} (hn : 1 ≤ n) : 1 ≤ R n := by
  have hA : Admissible n {1} := by
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩
    · intro x hx y hy hdiv
      rw [subsetSums] at hx hy
      obtain ⟨S, hSf, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨T, hTf, rfl⟩ := Finset.mem_image.mp hy
      have hS' := Finset.mem_filter.mp hSf
      have hT' := Finset.mem_filter.mp hTf
      have hSeq : S = {1} := by
        rcases Finset.subset_singleton_iff.mp (Finset.mem_powerset.mp hS'.1)
          with rfl | rfl
        · exact absurd hS'.2 (by simp)
        · rfl
      have hTeq : T = {1} := by
        rcases Finset.subset_singleton_iff.mp (Finset.mem_powerset.mp hT'.1)
          with rfl | rfl
        · exact absurd hT'.2 (by simp)
        · rfl
      rw [hSeq, hTeq]
  have := admissible_card_le hA
  simpa using this

theorem R_upper :
    ∃ C : ℝ, ∀ n ≥ 3,
      (R n : ℝ) ≤ Real.logb 2 n + Real.logb 2 (Real.logb 2 n) + C := by
  refine ⟨3, fun n hn ↦ ?_⟩
  obtain ⟨A, hA, hcardA⟩ := R_attained n
  set k := A.card with hkeq
  have hL1 : (1:ℝ) ≤ Real.logb 2 n := by
    have h22 : Real.logb 2 (2 : ℝ) = 1 :=
      Real.logb_self_eq_one (b := 2) (by norm_num)
    rw [← h22]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by
      exact_mod_cast (by omega : 0 < n))).mpr (by exact_mod_cast (by omega : 2 ≤ n))
  by_cases hk0 : k = 0
  · have hR : R n = 0 := by rw [← hcardA, hk0]
    rw [hR]
    simp only [Nat.cast_zero]
    have h2 : 0 ≤ Real.logb 2 (Real.logb 2 n) :=
      Real.logb_nonneg (by norm_num) hL1
    linarith [hL1]
  have hk : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hneA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hkn : 1 ≤ k * n := Nat.mul_pos hk (by omega)
  have hpow : (2:ℝ) ^ k ≤ 2 * k * n := by
    have h := pow_card_le hA hneA
    have h2 : (2:ℝ) ^ k ≤ k * n + 1 := by exact_mod_cast h
    have h3 : (k:ℝ) * n + 1 ≤ 2 * k * n := by
      have : (1:ℝ) ≤ k * n := by exact_mod_cast hkn
      linarith
    linarith
  have hklog : (k:ℝ) = Real.logb 2 ((2:ℝ) ^ k) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogle : Real.logb 2 ((2:ℝ) ^ k) ≤ Real.logb 2 (2 * k * n) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by
      positivity)).mpr hpow
  have hexpand : Real.logb 2 (2 * k * n) =
      1 + Real.logb 2 k + Real.logb 2 n := by
    rw [show (2:ℝ) * k * n = 2 * (k * n) by ring,
      Real.logb_mul (by norm_num) (mul_ne_zero (ne_of_gt hkR) (ne_of_gt hnR)),
      Real.logb_mul (ne_of_gt hkR) (ne_of_gt hnR),
      Real.logb_self_eq_one (b := 2) (by norm_num)]
    ring
  -- crude bound: `k ≤ n` gives `2^k ≤ 2n²`, hence `k ≤ 1 + 2·log₂ n`
  have hklen : k ≤ n := by rw [hcardA]; exact R_le n
  have hcrude : (k:ℝ) ≤ 1 + 2 * Real.logb 2 n := by
    have hkn2 : (k:ℝ) * n ≤ n * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hklen)
        (Nat.cast_nonneg n)
    have h2 : (2:ℝ) ^ k ≤ 2 * n * n := by nlinarith [hpow, hkn2]
    have hlog2 : Real.logb 2 (2 * n * n) = 1 + 2 * Real.logb 2 n := by
      rw [show (2:ℝ) * n * n = 2 * (n * n) by ring,
        Real.logb_mul (by norm_num)
          (mul_ne_zero (ne_of_gt hnR) (ne_of_gt hnR)),
        Real.logb_mul (ne_of_gt hnR) (ne_of_gt hnR),
        Real.logb_self_eq_one (b := 2) (by norm_num)]
      ring
    have hll : Real.logb 2 ((2:ℝ) ^ k) ≤ Real.logb 2 (2 * n * n) :=
      (Real.logb_le_logb (by norm_num) (by positivity) (by
        positivity)).mpr h2
    rw [← hklog] at hll
    linarith [hlog2]
  -- `k ≤ 3·log₂ n` (since `log₂ n ≥ 1`), so `log₂ k ≤ log₂(3 log₂ n)`
  have hk3 : (k:ℝ) ≤ 3 * Real.logb 2 n := by linarith [hL1]
  have hlogk : Real.logb 2 k ≤ 2 + Real.logb 2 (Real.logb 2 n) := by
    have hl3 : Real.logb 2 3 ≤ 2 := by
      have h24 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (b := 2) (by norm_num)]; ring
      exact (Real.logb_le_logb_of_le (b := 2) (x := 3) (y := 4)
        (by norm_num) (by norm_num) (by norm_num)).trans_eq h24
    have hLpos : (0:ℝ) < Real.logb 2 n := by linarith [hL1]
    calc Real.logb 2 k ≤ Real.logb 2 (3 * Real.logb 2 n) :=
          (Real.logb_le_logb (by norm_num) hkR (by positivity)).mpr hk3
      _ = Real.logb 2 3 + Real.logb 2 (Real.logb 2 n) :=
          Real.logb_mul (by norm_num) (ne_of_gt hLpos)
      _ ≤ 2 + Real.logb 2 (Real.logb 2 n) := by linarith [hl3]
  -- assemble: `k ≤ 1 + log₂ k + log₂ n ≤ log₂ n + log₂ log₂ n + 3`
  have hmain : (k:ℝ) ≤ Real.logb 2 n + Real.logb 2 (Real.logb 2 n) + 3 := by
    have h1 : (k:ℝ) ≤ 1 + Real.logb 2 k + Real.logb 2 n := by
      rw [← hklog] at hlogle
      linarith [hexpand]
    linarith [hlogk]
  rwa [hcardA] at hmain

/-! ## Main theorem -/

theorem jsp_000733 :
    ∃ C : ℝ, ∀ n ≥ 3,
      |(R n : ℝ) - Real.logb 2 n| ≤ Real.logb 2 (Real.logb 2 n) + C := by
  obtain ⟨C, hC⟩ := R_upper
  refine ⟨max C 2, fun n hn ↦ ?_⟩
  have hlow : -1 ≤ (R n : ℝ) - Real.logb 2 n := by
    have h := R_lower n (by omega)
    linarith
  have hup : (R n : ℝ) - Real.logb 2 n ≤
      Real.logb 2 (Real.logb 2 n) + max C 2 := by
    have h := hC n hn
    have : C ≤ max C 2 := le_max_left _ _
    linarith
  rw [abs_le]
  constructor
  · have h2 : (1:ℝ) ≤ Real.logb 2 (Real.logb 2 n) + max C 2 := by
      have hL1 : (1:ℝ) ≤ Real.logb 2 n := by
        have h22 : Real.logb 2 (2 : ℝ) = 1 :=
          Real.logb_self_eq_one (b := 2) (by norm_num)
        rw [← h22]
        exact (Real.logb_le_logb (by norm_num) (by norm_num) (by
          exact_mod_cast (by omega : 0 < n))).mpr
          (by exact_mod_cast (by omega : 2 ≤ n))
      have hnn : 0 ≤ Real.logb 2 (Real.logb 2 n) :=
        Real.logb_nonneg (by norm_num) hL1
      have : (2:ℝ) ≤ max C 2 := le_max_right _ _
      linarith
    linarith [hlow]
  · exact hup

end Jsp000733
