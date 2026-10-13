# JSP-000733: primitive sets of subset sums have size log₂n + O(log log n) — Lean formalization

Lean 4 + Mathlib formalization of the answer to JSP-000733
(Erdős Problem #882; answered in [ELRSS99]):

> Let `R(n)` be the largest size of `A ⊆ {1,…,n}` such that the
> distinct nonempty subset sums of `A` form a primitive set — no sum
> divides a different sum. Then `R(n) = log₂ n + O(log log n)`.

The main theorem is

```lean
theorem jsp_000733 :
    ∃ C : ℝ, ∀ n ≥ 3,
      |(R n : ℝ) - Real.logb 2 n| ≤ Real.logb 2 (Real.logb 2 n) + C
```

where `R n` is the maximum cardinality of an *admissible* set — a
`Finset ℕ` inside `{1,…,n}` whose subset sums are pairwise
incomparable under divisibility:

```lean
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter fun S ↦ S.Nonempty).image fun S ↦ ∑ a ∈ S, a

def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧
    ∀ x ∈ subsetSums A, ∀ y ∈ subsetSums A, x ∣ y → x = y

noncomputable def R (n : ℕ) : ℕ :=
  (Finset.univ.image Finset.card).filter ... -- max card over admissible A
```

(`R n` is realized as a `sup` over admissible sets; see `R_attained`.)

## Proof idea

**Lower bound** (`R_lower`). Take `m = ⌊log₂ n⌋` and the set
`{2^m − 2^i | i < m} ⊆ {1,…,2^m} ⊆ {1,…,n}`. A subset indexed by
`S ⊆ {0,…,m−1}` has sum `indexedSum m S = |S|·2^m − bitSum S`, where
`bitSum S = ∑_{i ∈ S} 2^i` is the number with binary digits exactly
`S`. If `indexedSum m S ∣ indexedSum m T`, say with quotient
`d ≥ 2`, then block inequalities force a carry
`c = d|S| − |T| < d` satisfying `d·bitSum S = c·2^m + bitSum T`.
Counting binary digit weights (`bitWeight`) on both sides and using
the monotonicity of `bitDefect n = n − bitWeight n` gives
`|S| = 1` and `d = c + 1`, which contradicts
`d·2^i = (d−1)·2^m + bitSum T` for `i < m`
(`indexedSum_dvd_indexedSum`). Hence the subset sums are primitive
(`construction_primitive`) and `R n ≥ ⌊log₂ n⌋ > log₂ n − 1`.

**Upper bound** (`R_upper`). Primitive subset sums must be distinct:
if `Σ S = Σ T` for `S ≠ T`, the sums over the symmetric difference
produce two comparable sums `s` and `2s`
(`sums_injective_of_primitive`). The `2^{|A|} − 1` nonempty subset
sums all lie in `{1,…,|A|·n}`, so `2^{|A|} ≤ |A|·n + 1 ≤ 2|A|n`
(`pow_card_le`). Since `|A| ≤ n` this gives `|A| ≤ 1 + 2 log₂ n`,
hence `log₂ |A| ≤ 2 + log₂ log₂ n`, and therefore
`|A| ≤ log₂ n + log₂ log₂ n + 3`.

The stated `O(log log n)` error term is thus achieved with constant
`C = 3` for all `n ≥ 3`; the sharper Erdős–Moser `½ log log n + O(1)`
bound for distinct subset sums is *not* needed for the leading-order
statement.

## Verification

- `lake build` compiles `Jsp000733.lean` with no errors and no warnings.
- `#print axioms jsp_000733` (and `R_lower`, `R_upper`,
  `indexedSum_dvd_indexedSum`, `construction_primitive`) reports only
  `propext`, `Classical.choice`, `Quot.sound` — see `Audit.lean`.
- No `sorry`, `admit`, or `native_decide` anywhere in the file.

Toolchain: Lean `v4.34.0`, Mathlib `v4.34.0` (pinned via
`lake-manifest.json`). Build with `lake build`.

## Prior art

The lower-bound construction alone was previously formalized in
`plby/lean-proofs` (`src/latest/ErdosProblems/Erdos882.lean`, proving
`R(n) > log₂ n − 1`); that development does not contain the upper
bound. This repository is an independent formalization of the full
two-sided result `R(n) = log₂ n + O(log log n)`, sharing only the
standard construction `{2^m − 2^i}`.
