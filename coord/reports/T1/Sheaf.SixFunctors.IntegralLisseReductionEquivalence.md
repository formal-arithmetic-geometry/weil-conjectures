## What changed

Moved the original coefficient, module, tower and equivalence-data definitions verbatim to
`Sheaf.SixFunctors.IntegralLisseReductionData`; the original module publicly imports it.
All existing public names, statements and definition bodies are preserved. This avoids an
import cycle when intermediate theorems refer to the existing data. The definition node's
Lean attachment follows the move. The change record is
`coord/changes/integral-lisse-reduction-data-module.md`.

Constructed actual scalar cokernel towers and their maps in
`IntegralLisseReductionConstruction`. Proved functoriality, quotient universal properties,
full faithfulness from completeness, and essential surjectivity from effectivity. The
original theorem builds the equivalence with this fixed quotient functor, transports the
limit cone along its counit, proves completion naturality, and proves the unit projection
formula from quotient naturality and the equivalence triangle identity. The counit
projection formula is definitional.

Proved `integralLisseCoefficient_isLimit` by using the existing normalized profinite integer
tower. Its continuous discrete projections identify the quotient topology with the discrete
one; compatible continuous residue functions assemble into a continuous integral function.
Evaluation functors and the ring forgetful functor reflect the resulting limit.
The normalized ring equivalence is determined uniquely by all its projections; no arbitrary
object is chosen from a mere existence assertion. Likewise the finite constant comparison
is uniquely determined on sheafified constant sections.

The resumed completeness check exposed expensive definitional comparison between two
recursive tower presentations. The private finite-unit tower now takes every map directly
from the coefficient diagram. Its scalar compatibility follows from coefficient-cone
naturality; the evaluated limit proof therefore uses the coefficient limit directly.
This changes no public definition or statement and removes the separate comparison
transformation. The complete module compiled in 24.7 seconds under the fixed limit.
Explicit local slice-sheafification instances in the effectivity proof also avoid
repeated synthesis of these instances; effectivity compiled cleanly in 29.9 seconds.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.ProEtale.integral_lisse_reduction_equivalence`.
Its proof and every intermediate theorem in this delivery are complete.
One original hole closed, zero holes added, zero holes left in the delivered Lean files.
No theorem is split off with an unfinished proof.

Proved in this delivery:

- `integral_lisse_reduction_equivalence`: the canonical quotient equivalence and all coherence data.
- `integralLisseFiniteConstant_exists`: normalized finite constant comparison.
- `integralLisseCoefficient_isLimit`: continuous coefficient inverse limit.
- `integralLisseCoefficient_sectionwise` and `integralLisseCoefficient_quotients`:
  coefficient reduction is sectionwise exact and gives the scalar cokernel.
- `integralLisseLocalization_isColimit`: fraction cocone colimit.
- `integralLisseCokernelTransition_quotient`: normalization of adjacent scalar cokernels.
- `integralLisseCoefficientKernel_annihilates`: the coefficient-kernel action vanishes;
  the finite coefficient action is constructed explicitly by scalar descent.
- `integralLisseUnitCokernel_complete`, `integralLisseCokernel_isLimit`:
  completeness of the unit and all finite locally free integral module sheaves.
- `integralLisseFiniteCokernel_isFiniteLocallyFree`, `integralLisseCokernel_complete`:
  the actual scalar cokernels have finite coefficient actions, finite free local charts,
  normalized transitions and the original module as their limit.
- `integralLisseTower_localBases`: compatible local bases for the entire normalized tower.
  Private helpers prove exactness of evaluation on weakly contractible objects, projectivity
  of evaluated finite free modules, recursive compatible section lifts, and invertibility
  of the lifted maps by square-zero correction with projective presentations.
  Local isomorphisms on weakly contractible refinements descend to sheaf isomorphisms.
- `integralLisseTower_effective`: the actual limit is finite locally free and its projections
  are scalar cokernels, from compatible local bases. This includes the limit-comparison
  equations, preservation of cokernels on slices and descent of the quotient universal property.

The retained completeness, effectivity and compatible-basis holes have all been closed.
Three additional DAG attachments record the already-proved construction, module
completeness and coefficient-kernel-action results; they add no holes.
The compatible-basis proof treats rank zero, varying local ranks and empty objects without
requiring a global rank comparison. There are no remaining `sorry` declarations to list.

No remaining obligation asks for an equivalence, limit local freeness, quotient descent,
normalization of a lisse module's tower, or coherence data. There are no holes inside
any definition or anonymous proof fragment. The scalar action is a construction using
surjectivity of coefficient reduction, whose proof is complete. All module-sheaf objects
and cokernels are genuine constructions. The unchanged consumer
`Sheaf.Paper.LisseCompletedSystemComparison` compiled against the moved public API.

## No longer needed

Removed the original direct proof imports
`Sheaf.NumberTheory.Padics.AdicLimitFiniteModules` and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful` from the data module.
The coefficient limit uses `Sheaf.NumberTheory.Padics.IntegersProfiniteTower` directly;
it does not require the broader finite-module adic reconstruction theorem or the
profinite-test-object comparison in `ProEtaleIntegralCoefficientLimit`.
Removed the unused private import of `IntegralLisseFiniteConstants` from
`IntegralLisseCoefficientLimit`: the limit proof uses continuous quotients directly.

The separate planned node `lem-sfb-integral-tensor-quotient-epimorphism` and its module
`Sheaf.SixFunctors.IntegralTensorQuotientEpimorphism` are unnecessary for this route:
normalization is already expressed as a scalar cokernel, whose projection is epic.
No tensor-unit epimorphism bridge is needed.

The main node is now the categorical assembly of the six precise intermediate results.
Its former five top-level tool-use approvals are removed there: the old general
comparison, finite-module adic reconstruction, module-sheaf colimit theorem,
weakly contractible cover and exact-section results are not used in this assembly.
The geometric cover is supplied by the proved upstream
`Scheme.ProEt.exists_isWeaklyContractible_cover`; evaluation exactness is proved directly
from weak contractibility and the forgetful-colimit theorem. Slice restriction uses
`ringedOverFunctor_exactGeneral`. A private abelian-category square-zero correction lemma
replaces matrix lifting; no rank-comparison assertion is assumed. Ordinary recursion on
natural numbers supplies the compatible lifts. Thus the original proof imports
`Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`,
`Sheaf.AlgebraicGeometry.WContractibleAffineCover`, and
`Sheaf.SixFunctors.IntegralSquareZeroMatrixLift` are removed, and the planned nodes
`det-pe-wc-sections-exact`, `det-pe-wcb-cover`,
`lem-sfb-integral-square-zero-matrix-lift`, and
`lem-coef-well-ordered-inverse-system-section` are not needed by this proof.
The original private import `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
is also removed; the coefficient limit is proved from the normalized profinite tower.
The direct public import of `CoefficientExtensionFinite` is retained because it is
a unit-route module; the unchanged data module also imports it.
No global module-pruning claim is made. The unit has no realized statement/step nodes bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox left general normalization/completeness and effectivity as two
named holes, alongside unfinished finite-sum and local-descent drafts. Integrated and
completed those drafts, built the missing finite coefficient action on actual cokernels,
and closed normalization/completeness. Completed the compatible local basis construction
and the effectivity theorem built from it. The retained packaging omitted DAG attachments
for three new support modules; these are now supplied for their existing proved results.
The old top-level docstring described dependencies the actual proof no longer uses; it now describes the implemented route. The original theorem
statement and definition bodies are unchanged. On resumption, compared the moved definition
block against the current shared source byte for byte: identical. The current downstream
scan has 407 transitive importers and the same six modules with textual uses of the
equivalence-data name; no consumer adaptation is required.

The listed dependencies supply algebraic and geometric ingredients, but do not themselves
state the coefficient-sheaf quotient/localization calculations or local normalized-tower
effectivity. The new proved lemmas implement those parts of the documented proof. Edge cases
in their plans include the empty object/base, rank zero and varying local rank.

## New nodes

`lem-sfb-integral-lisse-finite-constant` records the now-proved uniquely normalized finite
constant comparison. Its module is `IntegralLisseFiniteConstants`.

`lem-sfb-integral-lisse-coefficient-limit` records the now-proved canonical continuous
coefficient limit. Its module is `IntegralLisseCoefficientLimit`.

`lem-sfb-integral-lisse-coefficient-quotients` records the proved coefficient scalar-cokernel
calculation. Its module is `IntegralLisseCoefficientQuotients`.

`lem-sfb-integral-lisse-localization-colimit` records the proved fraction cocone universal
property. Its module is `IntegralLisseLocalization`.

`lem-sfb-integral-lisse-cokernel-complete` isolates normalization and completeness of the
actual quotient tower of a lisse module. Its proved declaration is in
`IntegralLisseReductionNormalized`; its completeness and scalar descent dependencies
have their own nodes below.

`lem-sfb-integral-lisse-tower-effective` records the proved reduction from compatible
local bases to local freeness of the actual tower limit and its scalar quotient projections. Its module is `IntegralLisseTowerEffective`.

`lem-sfb-integral-lisse-tower-local-bases` records the proved natural isomorphism of
restricted diagrams with finite free scalar-cokernel towers on a covering. The basis
construction, projective lifting and square-zero correction are proved in
`IntegralLisseTowerLocalBases`; limit identification, quotient universal properties and
categorical assembly are proved separately.

All nodes use the original Bhatt--Scholze source and include natural-language proofs.
The data relocation change record is
`coord/changes/integral-lisse-reduction-data-module.md`.

`lem-sfb-integral-lisse-cokernel-transition-quotient` records the proved normalization
of adjacent actual scalar quotients in `IntegralLisseReductionConstruction`, together
with the canonical quotient-tower construction and its categorical API.

`lem-sfb-integral-lisse-module-complete` records the proved completeness of finite
locally free integral modules in `IntegralLisseReductionComplete`.

`lem-sfb-integral-lisse-coefficient-kernel-action` records the proved triviality of
coefficient-kernel actions on actual scalar cokernels and the resulting constructed
finite coefficient action in `IntegralLisseReductionScalarDescent`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
