## Worker report

The module `Sheaf.RingTheory.PowerTorsionCokernelLength` states
`Module.length_quotSMulTop_le_of_power_torsion` with its single proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`.

Source checked: Stacks Project, `literature/stacks-project/divisors.tex`, Tag 0BCR,
`lemma-affine-punctured-spec`, converse proof, lines 3383–3399. The source calculates
lengths of the scalar kernels and bounds the images in Q/fQ, then uses their increasing
union. The docstring gives all three steps of the accepted DAG proof: finite lengths
of K_n, cancellation in the two exact sequences, and the finite strict-chain argument
for the union. No Noetherian or local-ring hypothesis is needed for this extracted
module-theoretic argument.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| R is a commutative ring | `(R : Type u) [CommRing R]` |
| Q is an R-module | `(Q : Type v) [AddCommGroup Q] [Module R Q]` |
| f is an element of R | `(f : R)` |
| Every q is killed by some f^n with n ≥ 1 | `h_torsion : ∀ q : Q, ∃ n : ℕ, 1 ≤ n ∧ f ^ n • q = 0` |
| Q[f] is the scalar kernel | `Submodule.torsionBy R Q f`, defined as `(DistribSMul.toLinearMap R Q f).ker` |
| fQ is the scalar image, and C = Q/fQ | `QuotSMulTop f Q`, Mathlib's abbreviation for `Q ⧸ f • (⊤ : Submodule R Q)` |
| Q[f] has finite length l | `h_length : Module.length R (Submodule.torsionBy R Q f) < ⊤`; l is this length, substituted directly rather than given a separate binder |
| length(C) ≤ l | First conjunct `Module.length R (QuotSMulTop f Q) ≤ Module.length R (Submodule.torsionBy R Q f)` |
| In particular C has finite length | Second conjunct `Module.length R (QuotSMulTop f Q) < ⊤` |

Both universes `u v` and all variables are explicit. No instance excludes the zero
module, the zero ring, or a module larger than its scalar ring. No finite generation
or global nilpotence assumption is imposed on Q.

Dependency declarations read and used:

- `def-weil-pbc-module-length` is a Mathlib leaf whose `mathlib_match` is
  `Module.length`, in `Mathlib.RingTheory.Length`. I read its definition and docstring:
  it is the Krull dimension of the submodule lattice, valued in ℕ∞, hence the
  supremum of strict-chain lengths. `Module.length_ne_top_iff` identifies finite
  length with `IsFiniteLength`. No absent `lean` record needs repair.
- The proof dependency `lem-weil-pbc-length-additive-short-exact` is the Mathlib leaf
  `Module.length_eq_add_of_exact`, in the same publicly imported module. Its full
  signature takes linear maps f : N →ₗ[R] M and g : M →ₗ[R] P, injectivity of f,
  surjectivity of g, and `Function.Exact f g`, and concludes length(M) = length(N)
  + length(P). Its docstring says length is additive in exact sequences.
- The existing `Submodule.torsionBy` and its membership theorem `mem_torsionBy_iff`
  are in `Mathlib.Algebra.Module.Torsion.Basic`; the definition and docstring give
  precisely the kernel of scalar multiplication.
- `QuotSMulTop` is in `Mathlib.RingTheory.QuotSMulTop`; its abbreviation and
  docstring specify Q/fQ. Thus neither the kernel nor quotient is a private copy.

Edge cases checked mathematically before writing:

- Q = 0, including modules over the zero ring: both lengths are zero.
- f = 0: n = 1 supplies power torsion, Q[f] = Q and Q/fQ = Q, so the bound is equality.
- f is a unit (including f = 1): power torsion forces Q = 0.
- l = 0: the scalar kernel is zero, so repeated cancellation using power torsion
  forces Q = 0 and gives a zero quotient.
- Q = k[t]/(t^a), f = t, a ≥ 1: the kernel and quotient both have length one.
- Q = k[t,t⁻¹]/k[t], f = t: every element is killed by a positive power, the kernel
  has length one, the quotient is zero, and Q itself has infinite length. This
  checks that the statement permits strict inequality and unbounded torsion powers.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder` with “An f power torsion module with finite length
  scalar kernel has cokernel length at most kernel length” returned eight hits:
  `Module.length_le_of_surjective`, `Module.length_le_of_injective`,
  `Module.length_eq_add_of_exact`, `IsFiniteLength.of_injective`, `IsFiniteLength`,
  `Module.supportDim_le_supportDim_quotSMulTop_succ`, `Module.length_quotient`, and
  `Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson`. These are
  monotonicity, additivity, finite length, or support dimension, not the desired bound.
- `msearch.py ... loogle "Module.length, Submodule.torsionBy"`: zero hits.
- `msearch.py ... grep "length.*torsionBy|torsionBy.*length|length.*quotSMul"
  RingTheory`: zero hits.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for length/torsion combinations, the item id, and
  the proposed theorem name found no existing statement. The parent module
  `Sheaf.AlgebraicGeometry.AffinePuncturedLocalDimension` mentions this item only
  as the needed input in its proof docstring. Other hits concern unrelated
  torsion-free resolutions and Riemann–Roch degree definitions.
- Direct Mathlib `rg` located and subsequent source reads verified `Module.length`,
  `Submodule.torsionBy`, and `QuotSMulTop`; the theorem name is unused throughout
  Mathlib, WeilConjectures, Sheaf, and the upstream declaration index.

Validation: the prescribed `scompile.py NZ lem-sfb-power-torsion-cokernel-length`
compiled both its sandbox module and actual library module successfully, with no
errors or unexpected warnings. All delivered Lean lines have at most 100 characters.
No statement dispute or node fault was found. The example CompactObject module is
currently withdrawn; this delivery follows the current module-mode instructions
and the landed LengthOfSupportAtMaximalIdeal module's header conventions instead.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
