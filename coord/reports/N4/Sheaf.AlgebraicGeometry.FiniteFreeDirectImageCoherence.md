## What changed

Proved the complete, unchanged theorem
`AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageCoherence`
from two separate source calculations and the existing normalized scalar-extension
family. Its proof now constructs scalar models, proves their counit-compatible
shifts and triangulatedness, proves comparison invertibility using basis columns,
and derives the precise identity and tower equations by mate pasting.

The original auxiliary definitions moved verbatim to
`Sheaf.AlgebraicGeometry.FiniteFreeDirectImageData`, publicly reexported by the
original module. Definition bodies and the theorem signature were checked against
the original copy; no semantic change. Automatic SizeOf generation for ScalarModel
is disabled: profiling isolated its generated bookkeeping as the compile-time cost,
and the data file then compiled in 15.3 seconds. The record fields, constructor and
projections are unchanged; no consumer uses the generated SizeOf instance. The separate lemma modules can consequently
import the data without an import cycle. See
`coord/changes/N4-finite-free-direct-image-data.md`.

New proved results:

- `finiteFreeDirectImageScalarModels`: lift the normalized restriction factorizations,
  transport the adjunctions, and construct the ordinary/derived multiplication units.
- `finiteFreeDirectImageScalarShift`: identify the universal counit with an inverse
  mate on flat-term K-flat representatives, extend by a resolving quasi-isomorphism,
  then use Mathlib's triangulated-left-adjoint theorem.
- `CategoryTheory.canonicalRightDerivedAdjunctionShift`: prove compatibility for the
  actual K-injective right-derived shift using its normalized unit and the right Kan
  universal property. This is the unbounded generic result, unlike the existing
  bounded-below etale specialization.
- `finiteFreeDirectImageShift`: the restriction/direct-image comparison is the mate
  of the termwise restriction/pullback isomorphism; inverse conjugation and taking
  the geometric mate preserve shift compatibility.

The original module also contains proved private helpers for invertibility, the
identity equation and the tower equation. The tower proof explicitly uses
`mateEquiv_whiskerTop_whiskerBottom` and `mateEquiv_vcomp`, with the inverse target
associator first and the direct image of the source associator last.

All eight modules compile together through lcompile.py, without warnings. An axiom
probe verifies that Presentation, ScalarModel, balancing, comparison, both shift
results and the generic canonical derived-adjunction result use only propext,
Classical.choice and Quot.sound. The model-existence theorem and the main theorem
also depend on sorryAx through the explicitly retained statements. No hollow data,
new axiom, unsafe declaration or arbitrary choice from a mere existence theorem
was introduced. Ordinary and derived unit isomorphisms are constructed from the
specified adjunction and universal factorization.

## Proved and sorry left

Original item: one explicit hole, in
`AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageCoherence`.
That body is now a complete Lean proof and the item module has zero explicit holes.
Four additional public theorems above and all private helpers are proved.

Added two explicit holes, each in its own module with a full source proof in the
docstring and matching DAG node:

- `AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImage_columns`
  in FiniteFreeDirectImageColumns, node
  `lem-sp-finite-free-direct-image-columns`.
- `AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageBalancingCoherence`
  in FiniteFreeDirectImageBalancingCoherence, node
  `lem-sp-finite-free-balancing-coherence`.

This is a decomposition: one upper hole closed and two smaller source-calculation
holes added (packet net -1 before the ledger accounts for import pruning), not a
claim that the whole mathematical dependency chain is proved. The preexisting
`successive_derived_quotient_normalization` is used as the stage-3 brief authorizes;
its existing hole is neither added nor moved here.

The first retained lemma supplies finite-biproduct coordinates and the individual
columns, without asserting comparison invertibility, triangulatedness, shift or
coherence. The main proof supplies the real deduction from those columns using
biproduct extensionality, mapBiproduct and conservative restriction. The second
retained lemma concerns only the left scalar/pullback balancing squares and their
ordinary tensor associators, with no finite-free hypothesis or direct-image result.
The main proof supplies the real mate-pasting deductions. Neither is the original
statement renamed or repackaged as an assumption.

Edge cases checked mathematically: d=0 gives the empty biproduct and zero scalar
extension; the biproduct extensionality proof has no basis indices and still works.
Identity coefficients give multiplication and the mate of the unitor square.
A two-step tower has exactly the displayed associator directions. Arbitrary q,
empty sites, zero coefficient rings and zero input complexes require no additional
hypothesis. The balancing equations are valid even without finite freeness.

## No longer needed

The direct proof no longer needs
`lem-weil-pbc-right-adjoint-preserves-limits`: additivity supplies preservation of
finite biproducts and the inverse mapBiproduct comparison. The module is not deleted.

The specialized `lem-weil-pbc-derived-adjunction-shift` and its import
`Sheaf.Paper.DerivedAdjunctionShift` are no longer used: the fixed canonical
K-injective shift is handled by the new fully proved generic result. Its obsolete
entry is removed from the original node's tool_uses, preserving all other entries.

Removed unused original imports:

- Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory (already reexported by required interfaces)
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
- Sheaf.CategoryTheory.RingedSiteModules (already reexported by normalization)
- Sheaf.Paper.EtaleDerivedScalarTensor
- Sheaf.Paper.PbcActualScalarPullback
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Mathlib.Algebra.Homology.DerivedCategory.Basic (already reexported)
- Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.Paper.DerivedAdjunctionShift
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

KFlatResolutionIndependentCoefficients moved to the proof modules that use it.
The retained public imports for statements moved to Data and remain available
through the original module. The same two restriction exactness instance attributes
formerly imported indirectly are preserved explicitly.

The nodes for ordinary tensor construction, exact derived computation, localization,
K-flat resolutions and tensor/pullback comparison remain needed in the two retained
source calculations. They are not claimed pruned merely because the main proof
now refers to those calculations through smaller nodes. No upstream declaration,
quarantine attachment or module is withdrawn. The blueprint unit route is retained:
finite-free scalar compatibility for the proper direct-image factor, with its
coherent identities, supplies the same parent step.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target was changed. The DAG's planned use of
right-adjoint finite-product preservation can be shortened to additive preservation
of finite biproducts. The previously imported derived-adjunction theorem has a
ringed-site/resolving-model interface; it does not directly supply the exact generic
CommShift instance for the existing canonical K-injective functor, so its normalized
unit argument was generalized and completely proved here.

The two missing calculations are specific, genuine source steps. The current
library has finite-basis results for constant coefficients and specialized finite
etale/pro-etale categories, but none states the required arbitrary identified
ring-sheaf column calculation. The same-site normalization supplies scalar
associators, not their across-sites compatibility with this canonical conjugate.
These gaps are isolated explicitly rather than inferred from unproved faithfulness
of restriction on derived Hom sets. Searches and source readings are recorded.

## New nodes

`def-sp-finite-free-direct-image-data`: the unchanged auxiliary definitions moved
from the original theorem module, with the actual conjugate and mate constructions.

`lem-sp-finite-free-scalar-models`: fully proved construction of both normalized
scalar adjunctions and multiplication units.

`lem-sp-finite-free-scalar-shift`: fully proved scalar counit-shift compatibility and
triangulatedness for the prescribed induced shifts.

`lem-sp-canonical-right-derived-adjunction-shift`: fully proved generic compatibility
of the canonical unbounded derived adjunction with its canonical shifts.

`lem-sp-finite-free-direct-image-shift`: fully proved shift compatibility for the
actual canonical coefficient mate.

`lem-sp-finite-free-direct-image-columns`: retained finite-basis coordinate and
column calculation, Steps 1, 2, 4 and 5 of the original source argument.

`lem-sp-finite-free-balancing-coherence`: retained left-balancing unit and tower
calculation, Step 3 of the original source argument.

Change record: `coord/changes/N4-finite-free-direct-image-data.md`.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
