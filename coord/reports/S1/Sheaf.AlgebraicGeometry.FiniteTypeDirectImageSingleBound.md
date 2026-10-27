## What changed

Replaced the hole in `finiteTypeDirectImage_single_boundedAbove` by a case analysis on
`IsFinitenessCoefficient`. The finite discrete torsion case is proved using the existing
finite-discrete encoding, the classical etale finite-type direct-image theorem, the
bounded-below unbounded comparison, and derived conjugation of pushforward by the encoding
equivalence. This proof covers exponent one and the zero ring as well.

The remaining cases reduce to three new statements: the integral sheaf upper bound, an
integral SHEAF scalar-change model of a rational sheaf direct image, and a finite-field
SHEAF scalar-change model of an algebraic-closure sheaf direct image. The assembly applies
the integral bound and exact scalar extension, then transfers IsLE along the model
isomorphisms. Embedded integer rings and closed unit balls are identified by equality of
subrings for the induced norm. The original declaration signature and public imports stay
unchanged. All added imports of the item are proof imports. No adopted source module,
definition, existing public signature, target or unit route changed.

Validation: all three new modules compile individually in the import-ordered compiler
run, and the assembled item compiles. The original item signature and public imports
were checked byte-for-byte; the only existing node fields changed are proof, proof_deps
and proof_origin. Every new node reference exists and proof_deps is the union of uses.
Each of the four Lean files meets the 100-character line limit.

## Proved and sorry left

The item originally had one hole. Its theorem
`AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`
now has a complete proof from named declarations, and its finite torsion case is fully
assembled without a new torsion hole. The item contains zero sorries.

Three new holes remain, one in each new module:

- `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeIntegralHeart_boundedAbove`
  (`lem-sfb-finite-type-integral-heart-bound`): the integral-only upper bound for one sheaf.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeRationalHeart_integralImage`
  (`lem-sfb-finite-type-rational-heart-integral-image`): a constructible integral SHEAF
  model and scalar-change isomorphism, with no bound in the conclusion.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeAlgClHeart_finiteImage`
  (`lem-sfb-finite-type-alg-cl-heart-finite-image`): a constructible finite-field SHEAF
  model and scalar-change isomorphism, with no bound in the conclusion.

This is a decomposition: one original hole removed, three holes added, net minus two
closed holes before any closure pruning. It is not a claim that the full theorem is
axiom-free. Every new hole is exactly a public theorem body `:= by sorry`, with its source,
proof in words and node. No data definition or private theorem contains a hole.

## No longer needed

The original item had no proof imports to remove. Its direct proof dependencies no longer
include the following original planned nodes/modules:

- `def-sfb-rationalization-equivalence` and `sk-def-sfb-rationalization`
  (`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` and
  `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`):
  the rational case uses an integral SHEAF model directly, with exact scalar extension.
- `lem-sfb-extend-scalars-bounded-constructible`
  (`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`) and
  `lem-sfb-extend-to-qlbar-constructible`
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`): only preservation of an upper
  t-structure bound by exact scalar extension is required, supplied by the generic API.
- `lem-sfb-finite-discrete-constructible-model`
  (`Sheaf.Paper.FiniteDiscreteConstructibleModel`) and
  `lem-weil-pbc-finite-discrete-derived-coefficient-data`
  (`Sheaf.Paper.FiniteDiscreteDerivedCoefficientData`): the finite torsion proof builds
  the needed derived conjugation from the existing heart encoding and restriction API.
- `lem-weil-pbc-qcqs-over-affine` and `lem-weil-pbc-qcqs-morphism-permanence`: the finite
  torsion proof obtains compactness and quasi-separatedness from the structural maps
  and infers qcqs for f using the existing instance API.
- `sk-def-sfb-dc-setting`: geometry is already in the fixed theorem binders; its extra
  module is not a proof import.

The old integral comparison, integral finiteness, normed realization, rational direct-image
comparison, and finite-stage descent nodes are not imported by the item itself. They remain
in the proof plans of the new coefficient-specific nodes, so this delivery does NOT claim
they are globally pruned. In particular `lem-kun-dimension-finite-type`,
`lem-weil-pbc-finite-type-over-noetherian`, `lem-sf-integral-direct-image-constructible`,
`lem-sfb-integral-ambient-tower-comparison`,
`lem-sfb-integral-constructible-completion-bridge`,
`lem-sfb-localized-direct-image-comparison`, `lem-sfb-normed-coefficient-realization`,
`lem-sfb-qlbar-direct-image-comparison`, and `sk-thm-sfb-qlbar-two-colimit` remain needed
below those nodes. No module is withdrawn and no adopted declaration is removed.

## Where the brief, the DAG or earlier work was wrong

Several stated dependencies cannot be imported at this item because their modules import
its consumer `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
and therefore this item. For example normed realization reaches the item through
`ProfiniteCondensedRing`, `ContinuousCoefficientCommRing`, and `MorphismDefs`; the integral
comparison, rational comparison and finite discrete model interfaces have analogous paths.
The import-direction tool confirmed these cycles. Their existence as declarations does
not make them acyclic proof imports here. No tool was patched and no declaration was
removed to avoid those cycles.

The new statements keep the integral/rational/finite-field reduction but specialize to
SHEAVES rather than arbitrary bounded complexes. This matters: the rational and algebraic
closure reductions give input sheaves in degree zero, to which the integral bound applies
directly. The finite discrete branch avoids the cyclic model wrapper through its smaller
acyclic heart and bounded-below APIs. The unit `sk-prop-open-coefficients` has empty realized
step lists; its coefficient route is preserved.

## New nodes

`lem-sfb-finite-type-integral-heart-bound`, in
`Sheaf.AlgebraicGeometry.FiniteTypeIntegralHeartBound`, is the integral single-sheaf bound.
Its proof uses integral completeness, perfect finite reduction, finite-coefficient
finiteness and the complete Nakayama criterion. This is a proper coefficient subcase of
the original theorem.

`lem-sfb-finite-type-rational-heart-integral-image`, in
`Sheaf.AlgebraicGeometry.FiniteTypeRationalHeartIntegralImage`, constructs an integral
sheaf model and compares its direct image after localization. This isolates lattice
gluing and scalar comparison; it asserts no finiteness bound.

`lem-sfb-finite-type-alg-cl-heart-finite-image`, in
`Sheaf.AlgebraicGeometry.FiniteTypeAlgClHeartFiniteImage`, descends a sheaf to finite
coefficients and compares direct image after extension to the algebraic closure. It
asserts no finiteness bound. These are not new data definitions, and their existence
witnesses are used only inside proofs. All three node files are in
`dag/nodes/sec-six-functors-basics/`. No change record is needed: no existing statement
or definition was changed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
