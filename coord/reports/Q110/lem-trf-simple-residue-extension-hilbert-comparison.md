## Worker report

### Statement

The module `Sheaf.RingTheory.SimpleResidueExtensionHilbertComparison` states
`Hironaka.simpleResidueExtensionHilbertComparison` and defines the four canonical
objects used by the statement:

- `simpleResidueTensor k R α` is the actual tensor product
  `(IntermediateField.adjoin k {α}) ⊗[k] R`, so `k(α)` is the simple subfield of the
  residue field, including the case `α ∈ k`.
- `simpleResidueEvaluation k R α` is the canonical algebra map taking
  `a ⊗ r` to `a * residue(r)`, built with `Algebra.TensorProduct.productMap`.
- `simpleResidueExtension k R α` is the canonical localization at the prime kernel of
  that evaluation map.  The target is a field, so primality is supplied by
  `RingHom.ker_isPrime`.
- `simpleResidueExtensionMap k R α` is the canonical map from `R` through the right
  tensor factor and the localization map.

The theorem binds a field `k`, a commutative ring `R` with `[IsLocalRing R]`,
`[Algebra k R]`, and `[IsNoetherianRing R]`; a residue element `α`; and an ideal
`I ≤ maximalIdeal R`.  Its first conjunction asserts that `R'` is Noetherian and
local.  Its second and third assertions assert that `A' = R'/IR'` is Noetherian and
local.  The existential `ρ` is a surjective residue map `R' → L` whose restriction
along the localization map agrees with evaluation, whose kernel is the maximal ideal;
`σ` is the induced surjective residue map from `A'`, with kernel the mapped maximal
ideal.  The next clause gives, for every `n`, the inequality
`(Λ^e h_A)(n) ≤ h_A'(n)`, with exponent `0` when `α` is algebraic over `k` and `1`
otherwise.  The final implication assumes regularity of `R` and equality of the two
Hilbert functions, and concludes regularity of `R'` and
`nuStar I = nuStar (I.map simpleResidueExtensionMap)`.  This is the node's
`ν*(R,I)=ν*(R',I')`, using the published `Hironaka.nuStar` definition.

The `sorry` proof docstring records all nine proof clauses from the DAG: quotient and
polynomial local structure; the transcendental and algebraic presentations; local and
Noetherian descent; graded length summation; the algebraic multiplication kernel; the
regularity criterion; cotangent parameters and the linear-section equality; and the
associated-graded polynomial calculation.  It includes the `n=0`, `I=0`, transcendental,
algebraic, separable, and purely inseparable edge cases.

### Dependencies used

- `Mathlib.Algebra.Algebra.Defs.Algebra` for the scalar action and `algebraMap`.
- `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic.Algebra.trdeg` through the existing
  Hilbert--Samuel infrastructure.
- `Mathlib.LinearAlgebra.TensorProduct.Defs.TensorProduct` and
  `Mathlib.RingTheory.TensorProduct.Maps.Algebra.TensorProduct.productMap`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic.Localization.AtPrime` and
  `Ideal.ResidueField` infrastructure.
- `Mathlib.RingTheory.Length.Module.length`.
- `Mathlib.RingTheory.RegularLocalRing.Defs.IsRegularLocalRing`.
- `WeilConjectures.RingTheory.AssociatedGradedRing.Ideal.associatedGraded`.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant.AlgebraicGeometry.HilbertSamuel.summation`.
- `Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees.Hironaka.nuStar` and
  `Hironaka.quotientHilbertFunction`.

The node's recorded statement dependencies are reused: `IsNoetherianRing`, `Algebra`,
`Algebra.trdeg`, `TensorProduct`, `Localization.AtPrime`, `Module.length`,
`IsRegularLocalRing` (the regular-ring clause of `def-weil-regular-scheme`
provided by its `mathlib_match`), and `Ideal.associatedGraded`.  The two additional
statement dependencies are the existing ownership node
`def-trf-adic-initial-ideal-generator-degrees` (the six published Hironaka definitions)
and `def-trf-hilbert-samuel-invariant` (the published summation), plus the new
`def-trf-local-quotient-hilbert-function` ownership node described below.

### Edge cases and searches

The construction handles `α ∈ k` because `IntermediateField.adjoin k {α}` then has the
base field as its canonical subfield.  It handles transcendental, separable algebraic,
and purely inseparable α through the `if IsAlgebraic k α` exponent and makes no
separability assumption.  `I = 0` is permitted by `hI`; `n = 0` is included by
`n + 1`; and the local rings are nonzero because `IsLocalRing` includes `Nontrivial`.
The quotient Hilbert function deliberately uses `toNat`, exactly as the existing
construction does; the theorem's Noetherian-local hypotheses supply the finiteness
needed in its application.

Searches were run with `msearch.py` and recorded in `searches.jsonl`: LeanFinder for
“Hilbert Samuel function comparison for localization of a local algebra after extension
to a simple subfield of its residue field” (no exact match); Loogle for
`Algebra.TensorProduct.lift, Localization.AtPrime, IntermediateField.adjoin` (no match);
LeanSearch for “Local quotient Hilbert Samuel sequence length of quotient by powers of
image of maximal ideal” (standard quotient/length lemmas only); LeanFinder for “Hilbert
Samuel sequence of local ring quotient by ideal using module length of truncations”
(generic adic lemmas only); and grep for `hilbertSamuel|nuStar|simpleResidue` in
Mathlib/RingTheory (no match). Repository searches found no competing simple-residue
comparison declaration. The Hironaka PDF was opened at pp.162–168; its Cases 1–3 and
(9.6) match the theorem's exponent and localization construction.

No `STATEMENT-DISPUTED` flag is needed.

## New nodes

`def-trf-local-quotient-hilbert-function` is a definition-only ownership node for the
existing real-data declaration `Hironaka.quotientHilbertFunction` in
`Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees`.  It states the quotient length
function for arbitrary commutative `W`, ideals `l,c`, and natural `n`, with `toNat` of
`Module.length`; its local Noetherian interpretation is explanatory only and asserts no
finiteness theorem.  Mathlib, project, and DAG searches found no other owner, while the
existing module contains the exact construction, so the node records `existing: true`
and adds no copied module.

## Second reading by Q110

Self-check only; the dispatcher requires this worker to use no other agents. The
maintainer supplies the independent review. I reread the node, this module, and every recorded dependency.  The Lean binders match
`k`, nonzero commutative Noetherian local `k`-algebra `R`, residue element `α`, ideal
`I ⊆ m`, and all clauses of the comparison.  The canonical evaluation and localization
are explicit, and the residue-field maps are required to agree with evaluation and have
the stated kernels.  The exponent is exactly the algebraic/transcendental dichotomy;
no separability hypothesis is added.  The regularity and `ν*` equality implication is
present.  Compilation through `scompile.py` is clean with no warnings.
