## What changed

Proved `AlgebraicGeometry.Scheme.relativeFrobenius_integral_universalHomeomorphism`
in `Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism`, without
changing its signature or public imports. Constructed the characteristic witness,
proved Frobenius naturality on sections, and constructed the relative Frobenius by
`pullback.lift`, including both projection equations and uniqueness.

Specialized the existing absolute-Frobenius theorem to the concrete datum with
`a = 1`, prime field `ULift (ZMod p)`, and its constructed `AlgebraicClosure`.
The structure morphism comes from `T.toSpecΓ` and `ZMod.castHom` using
`ringChar Γ(T, ⊤) ∣ p`; this includes zero global-section rings and empty schemes.
Then used universal-homeomorphism base change and the existing theorem
`IsUniversalHomeomorphism.of_comp`. That theorem packages separated integral
cancellation, the field-point criterion for universal injectivity, and point-set
surjectivity cancellation. The existing Tag 04DF theorem gives the quantified
topological conclusion.

Updated the existing node's proof, proof dependencies and proof origin to this
argument and withdrew the obsolete `pqf-lem-integral-univclosed` and
`lem-weil-pbc-affine-morphism-permanence` tool approvals.
Added proof-only imports `Mathlib.Algebra.Field.ULift` and
`Mathlib.Algebra.Field.ZMod` for the concrete lifted prime field. No definition, statement, visibility, or consumer changed.
The fixed unit has no realized step replaced by this simplification.

Search: `msearch.py` LeanFinder for relative Frobenius and universal-homeomorphism
cancellation, Loogle for `"frobenius", "integral"`, and grep for relative Frobenius
or Frobenius/homeomorphism. Also searched both library roots directly and read
`AbsoluteFrobenius.lean`, `Morphisms/Frobenius.lean`, and
`Morphisms/UniversalHomeomorphism.lean`. The existing APIs supply the geometric
input and every permanence step; no new statement is necessary.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.relativeFrobenius_integral_universalHomeomorphism`
(node `lem-trf-relative-frobenius-universal-homeomorphism`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The proof uses the already stated dependency
`WeilConjectures.FiniteFieldDatum.absoluteFrobenius_isUniversalHomeomorphism`
(node `lem-pur-absolute-frobenius-universal-homeomorphism`), which currently has
its own existing sorry and remains a subsequent item. This delivery does not
claim to close that dependency or the whole target axiom closure.

Validation: remote per-file compilation passed without errors or warnings.
The final delivery checks also compile the file with the axiom probe.
The required delivery dry run checks the final snapshot separately.

## No longer needed

Removed direct proof imports:

- `Mathlib.FieldTheory.Finite.GaloisField` (the datum uses `ZMod p` directly).
- `Mathlib.AlgebraicGeometry.Over` (already exposed by the absolute-Frobenius input).
- `Mathlib.CategoryTheory.MorphismProperty.Limits` (already exposed by existing imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine` (already exposed by the statement imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` (no properness argument).
- `Mathlib.AlgebraicGeometry.Morphisms.Separated` (already exposed by Integral).
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective` (exposed by UniversalHomeomorphism).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (exposed by existing imports).

Removed direct DAG proof dependencies:

- `def-weil-finite-field-q-elements`: no `GaloisField` construction or classification;
  the explicitly constructed prime field uses `ZMod.card`.
- `lem-trf-closed-embedding-affine`: the absolute Frobenius already has an affine
  instance, and its pullback is affine.
- `def-weil-proper-morphism`: no separate universally-closed argument.
- `lem-weil-pbc-affine-morphism-permanence`: the existing cancellation theorem
  obtains separatedness from injectivity, so no affine permanence argument is used.
- `pqf-lem-integral-univclosed`: integrality is already part of the
  absolute-Frobenius theorem's `IsUniversalHomeomorphism` conclusion.

Removed the obsolete `pqf-lem-integral-univclosed` and
`lem-weil-pbc-affine-morphism-permanence` entries from `tool_uses`.
Retained the explicit `Sheaf.Paper.FiniteFieldFiber` import required by the unit-route check.
No library module is withdrawn. Some removed direct imports remain transitively
available, as required by the statements of the retained dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned detour from topological universal homeomorphism through
closed-embedding affineness and universal closedness is unnecessary in Lean:
the declared absolute-Frobenius input concludes the stronger bundled class,
which already includes integrality. The prime-field structure morphism also
needs no affine-chart gluing: the global-sections/spectrum adjunction gives it
directly, including the zero ring case.

The server initially gave no answer within its retry window; retrying restored
compilation. No tool, repository file, target statement, or claimed module was
modified to work around this transient service failure.

Preflight also exposed an unused cancellation-node draft already present in the sandbox;
it was removed from the delivery, since this proof uses no such new node.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
