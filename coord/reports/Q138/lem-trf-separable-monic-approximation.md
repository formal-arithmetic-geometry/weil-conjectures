## Worker report

The module `Sheaf.FieldTheory.SeparableMonicApproximation` states
`Polynomial.exists_monic_separable_natDegree_eq_coeff_sub_lt`, with `sorry` as its entire
proof. It introduces no definitions and leaves the natural-language statement unchanged.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field F | `{F : Type u} [Field F]`, with explicitly declared universe `u` |
| Real-valued absolute value, multiplicative and zero exactly at zero | `v : AbsoluteValue F ℝ`; Mathlib's structure includes multiplicativity, nonnegativity, positive definiteness, and the triangle inequality |
| Nontrivial | `hv : v.IsNontrivial`, meaning `∃ x ≠ 0, v x ≠ 1` |
| Nonarchimedean | `hna : ∀ x y : F, v (x + y) ≤ max (v x) (v y)` |
| Every polynomial f in F[T] | `f : F[X]` |
| f monic | `hf : f.Monic` |
| Degree d at least one | `(d : ℕ) (hd : 1 ≤ d) (hfd : f.natDegree = d)` |
| Every real ε > 0 | `(ε : ℝ) (hε : 0 < ε)` |
| There exists g in F[T] | `∃ g : F[X]` |
| g monic | `g.Monic` |
| g separable | `g.Separable` |
| g has degree d | `g.natDegree = d` |
| Every coefficient with 0 ≤ i < d has the stated strict bound | `∀ i : ℕ, i < d → v (g.coeff i - f.coeff i) < ε`; nonnegativity of i is built into ℕ |
| No completeness or perfectness assumption | Neither structure appears among the binders |

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Polynomial` and `Polynomial.coeff` in
  `Mathlib.Algebra.Polynomial.Basic`; `Polynomial.natDegree` and `Polynomial.Monic` in
  `Mathlib.Algebra.Polynomial.Degree.Defs`. These are publicly available through the
  `Mathlib.FieldTheory.Separable` import.
- `def-pc-separable-polynomial`: the recorded Mathlib match `Polynomial.Separable` in
  `Mathlib.FieldTheory.Separable`, defined as coprimality with the formal derivative;
  `separable_def'` identifies it with the displayed Bezout identity. This dependency is
  a Mathlib leaf and needs no new Lean record or module.
- The absolute value structure and `AbsoluteValue.IsNontrivial` come from
  `Mathlib.Algebra.Order.AbsoluteValue.Basic`; ℝ comes from `Mathlib.Data.Real.Basic`.

The proof docstring reproduces all five proof steps: degree one; small distinct powers
avoiding a finite set; a small linear perturbation making the derivative nonzero; a
small constant shift avoiding the exceptional finite set; and the degree and coefficient
calculations. The proof-only node `lem-trf-polynomial-constant-shifts-finite-exceptions`
has no recorded declaration or Mathlib match in the current DAG. It is named in the
proof plan; no import is possible yet. It is not needed to state this theorem. Both
currently stated definition dependencies are imported through their Mathlib modules.

Edge cases checked before writing:

- Degree one: `f = X + C c` is already separable; `g = f` gives zero differences.
- Degree zero and the zero polynomial: excluded exactly by positive degree and monicity;
  natural degree therefore agrees with the ordinary degree in every permitted case.
- Arbitrary positive characteristic, including inseparable `X^p`: the small linear term
  makes the derivative nonzero, and the constant perturbation handles the remaining
  repeated factors without assuming perfectness.
- Trivial absolute value: correctly excluded. In characteristic two, `f = X^2` and
  `ε ≤ 1` would otherwise force all lower coefficients unchanged, preventing separability.
- Arbitrarily small positive ε, incomplete fields, and imperfect fields: no lower bound
  on ε or additional field structure is present. Nontriviality supplies the needed small
  elements; finite fields cannot satisfy this absolute-value hypothesis.
- Every coefficient below d is included, including i = 0 and i = d - 1. The common monic
  degree fixes the leading term and all higher terms as required.

Searches made with the prescribed `msearch.py` wrapper:

- LeanFinder: "Separable monic polynomials of fixed degree are dense among monic
  polynomials over a nontrivially valued nonarchimedean field". Eight hits, including
  `IsSepClosed.of_exists_root`, `Polynomial.HasSeparableContraction`, and
  `Polynomial.Separable`; none asserts this approximation.
- Loogle: `Polynomial.Separable, Polynomial.Monic`. One hit,
  `IsSepClosed.of_exists_root`, which is a separable-closedness criterion, not density.
- LeanSearch: "separable monic polynomials are dense among monic polynomials over a
  nontrivially valued field". Eight hits, including separability definitions and
  unrelated topological separability; no exact match.
- Mathlib grep: `approximat.*separable|separable.*approximat|exists_monic_and_natDegree`
  in `Analysis/Normed/Field`. Five hits in `Dense.lean` and `Approximation.lean`.
  Read `Dense.lean`'s TODO explicitly requesting approximation by separable polynomials.
  Read `exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` in
  `Approximation.lean`: it approximates coefficients from a dense subfield without
  asserting separability, and is therefore not this statement.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` trees for
  `separable.*approx|approx.*separable|separable-monic-approximation`: no matches.
  A further exact-name search in those trees and Mathlib found no declaration named
  `exists_monic_separable_natDegree_eq_coeff_sub_lt`.

Source check: read Stacks `fields.tex`, Tags 09H0/09H1, around lines 1145–1178, for
the derivative and coprimality convention. The node explicitly records that this is
an agent-supplied auxiliary lemma contextual to Temkin, not a quotation of a separately
numbered result; its Temkin PDF is unavailable locally. No statement correction,
dispute, additional node, or dependency repair was needed.

The earlier worker stopped before creating any sandbox node. The Q71 `reviewed` record
is the stage-1 split review; this item has no `lean` or `reviewed_lean` record and thus
does require this stage-2 statement. This packet supplies the previously missing node
copy and module rather than repeating a stage-1 delivery.

## Second reading by Q138

No second worker was started, as the dispatcher's instructions prohibit other agents.
The maintainer performs the independent review. A fresh self-reading against the node
and completed file confirmed each correspondence in the table: the same field and
absolute value occur in every coefficient bound, monicity and positive degree are
explicit, the existential polynomial is separable of exactly d, and the bound covers
all natural indices below d. No hypothesis or conclusion was changed on this reading.
