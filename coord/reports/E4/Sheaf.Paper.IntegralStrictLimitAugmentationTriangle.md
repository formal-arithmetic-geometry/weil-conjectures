## What changed

Specialized the existing proved
`CategoryTheory.exists_augmentedDerivedTowerUnit` in the new module
`Sheaf.Paper.IntegralStrictAugmentation`. The simultaneous quotient projections give
one explicit strict tower map. The generic theorem supplies the universal natural
lifts and their complete ordinary-unit normalization; the proved specialization is
`AlgebraicGeometry.ProEtale.exists_integralStrictAugmentation`. This uses the
existing generic result rather than reproducing its proof. The ordinary augmentation
is a real construction from the strict quotient map and the supplied comparison.

In `Sheaf.Paper.IntegralStrictLimitAugmentationTriangle`, the private
`counit_isIso_on_regular` proves computation on regular complexes for the arbitrary
input `I`, using the existing resolving-class construction and uniqueness of left
derived functors. The theorem then uses the ordinary computation on such a complex,
cancels the counit, and uses naturality along a flat-term resolution to cover every
derived object. The triangulated reduction functor and the proved source
`DerivedCategory.isIso_smul_id_of_isZero_reductionModIdeal` finish the cone argument.
The original theorem signature and public imports are preserved.

The one uncompleted calculation is stated in the new module
`Sheaf.Paper.IntegralOrdinaryAugmentationReduction`. Its input is an ordinary quotient
presentation and a complex with monic prime-power multiplications. It has no derived
reduction `I`, no arbitrary derived input, no natural transformation to construct,
and no cone to choose. Its particular augmentation is already constructed, not an
existentially chosen map. Its docstring gives the normalized Koszul/Roos calculation.
This is a reduction to a proper step of the original argument, rather than another
name for its conclusion.

Validation: all three delivered Lean modules compile cleanly through `lcompile.py`
in import order, with reported times 53.9 s, 48.1 s, and 53.4 s, each below 60 s.
The original theorem signature is byte-identical to the current source. Node ids,
dependency unions, and Lean line lengths were checked. The delivery tool performs
the final compile and axiom/preflight checks after the docstring-only clarifications.

## Proved and sorry left

Original holes closed: the body of
`AlgebraicGeometry.ProEtale.integral_strict_limit_augmentation_triangle`
(`lem-sfb-integral-strict-limit-augmentation-triangle`) is a complete proof from the
new ordinary-complex calculation and existing declarations.

New holes added: exactly one,
`AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_reduction`
(`lem-sfb-integral-ordinary-augmentation-reduction`). It is the entire proof of one
public theorem in its own module. There are zero holes in the item module and zero
in `IntegralStrictAugmentation`.

This is one decomposition, not a net hole reduction: one original hole is replaced
by one strictly narrower calculation. The natural augmentation, its normalization,
the computation of an arbitrary derived counit on regular complexes, the passage
to all derived objects, and the final cone deduction have complete Lean proofs.
No data is selected from the new unproved theorem.

## No longer needed

The original proof dependency `lem-sfb-source-principal-completion-orthogonal`
(`DerivedCategory.derivedComplete_iff_rightOrthogonal`) is not used as a proof step.
The argument uses the more direct, already proved source criterion that zero
reduction implies invertible scalar action. The old node remains a statement
dependency, and the original public import of `Complete.Principal` is retained.
No original import is removed. No existing module is withdrawn, and no source
declaration is removed. The remaining calculation cites the precise source successor-lift, product, and
Milnor pro-isomorphism declarations, and the existing exact-product and normalized
Roos comparison nodes; they are not claimed as pruned.

The particular public existence theorem
`AlgebraicGeometry.ProEtale.exists_diagonalDerivedReduction` is not applied.
Its module remains imported with `import all` for its proved generic resolving-class,
quotient-quasi-isomorphism, and flat-multiplication helpers. Its module and those
helpers are needed, and are not pruned. The DAG names the generic resolving-class
and flat-resolution statements used by the argument.

The generic categorical tool
`lem-weil-pbc-augmented-derived-tower-unit` is used as a black box in its full
published generality. It is already proved. The diagonal unit does not have another
stated universal-lift theorem supplying this ordinary-map normalization.

The naturality construction needs neither a Roos model nor a comparison with a
completion reflector. Those constructions are not imported for the derived descent.
The remaining ordinary-complex computation still needs its normalized Koszul/Roos
argument; this delivery does not claim that its underlying mathematics is pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was mathematically sound but bundled construction and
naturality, independence of the chosen left-derived reduction, and the ordinary
regular-complex calculation into one hole. The first two admit direct Lean proofs
from universal properties. The input `I` is arbitrary, whereas the existing public
existence theorem only computes the particular reductions it constructs; applying
that theorem alone would not justify the arbitrary input's counit. The delivery
instead reuses its proved resolving-class helpers and the unique comparison of
universal left-derived functors.

Matching all level projections would not identify an augmentation into a derived
limit. The normalization equation here identifies the actual map using the given
right-derived comparison, and the remaining calculation explicitly retains the
zero shifted-product coordinate. Zero complexes and the empty scheme introduce no
extra hypotheses. No disputed statement or definition repair was needed.

## New nodes

`lem-sfb-integral-strict-augmentation` records the explicit strict augmentation and ordinary map, and the proved
specialization of the generic augmentation theorem with its normalization equation. Its Lean module
is `Sheaf.Paper.IntegralStrictAugmentation`.

`lem-sfb-integral-ordinary-augmentation-reduction` is the single remaining ordinary
regular-complex calculation, with its source and complete mathematical proof plan.
Its Lean module is `Sheaf.Paper.IntegralOrdinaryAugmentationReduction`.

`lem-sfb-source-reduction-detects-invertibility` attaches the existing, fully proved
source theorem `DerivedCategory.isIso_smul_id_of_isZero_reductionModIdeal`; it adds
no Lean declaration or hole. It records the exact criterion used in the last step
instead of citing an unrelated orthogonality conclusion from the same source tree.

`lem-sfb-source-reduced-koszul-successor-lifts` attaches the existing source
`DerivedCategory.exists_lift_whiskerRight_derivedCompletionCone`, including both
successor factorization equations. `lem-sfb-source-milnor-proisomorphism-invertibility`
attaches `CategoryTheory.Pretriangulated.isIso_of_proIso`, including the boundary
compatibility. `def-sfb-source-principal-reduction-product` attaches the existing
actual limit comparison `DerivedCategory.isLimit_fan_whiskerRight_quot`. These
three source attachments add no Lean declaration or hole. They let the remaining
calculation cite the precise tools it needs instead of using the proof of an
orthogonality theorem as though it were that theorem's statement.

There are no change records because no existing statement, definition, public
import, or module other than the assigned item is changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
