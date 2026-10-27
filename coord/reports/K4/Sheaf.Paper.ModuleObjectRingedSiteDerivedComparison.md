## What changed

The original comparison theorem is reduced to normalized tensor localization.
The complete Hom argument constructs the native closed structure with Hom first,
uses the closed scalar Hom comparison, and cancels the equivalence unit and counit
to prove the displayed evaluation equation. On each slice it constructs the local
Hom comparison and uses full faithfulness to lift the normalized ringed restriction
isomorphism; cancellation proves exactly the required restriction square.

`Sheaf.Paper.InternalSectionTensorLocalization` states the separate tensor result:
existence of the fixed-total-normalized tensor comparisons globally and on slices.
It contains neither Hom comparison nor evaluation or restriction compatibility.
The original module's public signatures, public imports and `internalBraiding` body
are unchanged. All helper declarations in that module are private and proved.
The parent node and new tensor node record this division of the argument.
Local irreducibility attributes keep the native internal-Hom and adjunction
implementations behind their APIs during elaboration; they do not change public data.
The full sandbox compiled through lcompile.py: 1.1 seconds for the tensor statement
and 34.5 seconds for the item, with no compiler errors. Delivery checks recompile
the final files after removing the temporary profiler settings.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`
(node `lem-sfb-module-object-ringed-site-derived-comparison`) is closed by a complete
proof from the tensor-localization lemma and existing library results. The item
module has zero remaining holes.

One hole is added, in the named public theorem
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalSection_tensorLocalization`
(node `lem-sfb-internal-section-tensor-localization`), in its own module. Its docstring
and node give the complete tensor argument. This is a decomposition: one original
hole closed, one strictly narrower tensor result split off, net zero holes closed.
No definition, instance or private theorem contains `sorry`.

The tensor construction was attempted through the ordinary pure-tensor comparison,
strong monoidal coherence, preservation of total K-flatness, and inverse localization
tensorators. The abstract transport helpers typechecked, but the concrete native/site
specialization did not finish: comparing the fixed summand equations unfolds nested
sheaf/derived monoidal instances. Those unfinished private drafts are not delivered.
The residual lemma is the tensor portion of the source argument, independent of the
Hom uniqueness and restriction proofs completed here. It is split along that
mathematical boundary, not by dividing a slow file or proof into compile units.

## No longer needed

The proof does not need a separate derived-braiding theorem: both closed structures
use Hom-first evaluation, and uniqueness of right adjoints gives its equation directly.
It also does not need slice evaluation coherence: the conclusion asks for normalized
slice data and the single-slice Hom restriction square, which full faithfulness supplies.
The tensor lemma uses the existing module-object flat-resolution instances rather
than asking for fresh flat covers or resolutions. The exact derived equivalence
supplies its own unit and counit. Accordingly the unused planned proof dependencies are
`def-weil-exact-derived-adjunction`, `lem-pc-kflat-resolution`,
`lem-pc-sites-modules-functorial-flat-cover`,
`lem-sfb-exact-tensor-functor-derived-braiding`,
`lem-pur-site-restriction-module-adjunction-exact`, and
`lem-weil-pbc-ringed-slice-evaluation-coherence`.
The old tool-use of `lem-weil-pbc-ringed-internal-hom-exact-restriction` is also unused.
This does not withdraw any declaration or claim global unreachability for those modules.

Removed private imports:

- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The public imports remain because they define the fixed interfaces appearing in the
statement. No Lean module is withdrawn. The tensor prerequisites remain needed by
the new tensor-localization node; moving them there is not pruning them.

## Where the brief, the DAG or earlier work was wrong

The older docstring describes a successive-slice cocycle, but the actual theorem and
current DAG assert only one slice at a time. The proof follows the current statement.
A fresh derived braiding calculation and a fresh flat-cover construction are unnecessary.
The DAG proof and proof dependencies are updated to the actual route.

## New nodes

`lem-sfb-internal-section-tensor-localization` is the tensor-only part of the parent's
Steps 1–3 and the tensor part of Step 5. It uses the existing ordinary section tensor,
exact tensor normalization, K-flat transport and ringed tensor-Hom model declarations.
The statement includes the actual global and local native tensor comparisons and their
specified total-complex normalizations, so no chosen tensor is substituted for them.
Identity equivalences give identity comparisons; zero coefficient rings and empty
sites give the zero-category case, and the proof uses arbitrary signed direct-sum
totals, hence introduces no boundedness or perfectness hypothesis. The parent retains
the Hom and restriction argument. No change to an existing definition or statement
is made, so no change record or forced consumer adaptation is needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
