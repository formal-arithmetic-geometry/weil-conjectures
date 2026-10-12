## What changed

Proved `CategoryTheory.derivedInternalHom_single_comparison` without changing its signature.
The Lean proof installs the Grothendieck instance, uses the concrete functorial K-injective
replacement, proves that termwise additive Hom followed by Q is derived by the K-injective
localizer, and obtains invertibility of δ on the replacement from Mathlib's
`LocalizerMorphism.Derives.isIso_of_isRightDerivedFunctor`. Naturality of Q(η) gives
`Q ⋙ S ≅ I ⋙ T_M^bullet ⋙ Q`.

The proof specializes `derivedInternalHom_comparison` by currying, composes with the new
single-source natural chain comparison, and descends the composite natural isomorphism
using `Localization.fullyFaithfulWhiskeringLeft` and `preimageIso`.

Added `Sheaf.AlgebraicGeometry.HomComplexSingleNatural` and its node. Added proof imports
of this module, `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, and Mathlib's
`CategoryTheory.Localization.DerivabilityStructure.Derives`. Updated the parent node's
proof, proof dependencies, and origin to match the actual Lean argument. Both delivered
modules compile without warnings with `lcompile.py --all` (approximately 15 and 50 seconds).

## Proved and sorry left

Closed the original hole in `CategoryTheory.derivedInternalHom_single_comparison`
(node `lem-sc-derived-internal-hom-single-comparison`). Added one hole:
`AlgebraicGeometry.homComplex_single_natural_iso`
(node `lem-sc-hom-complex-single-natural`). There are no other holes in the delivered files.
This is a decomposition: one upper hole closed, one strictly smaller underived naturality
hole added, net zero. The naturality statement involves only cochain complexes, not
localization, derived functors, choices of S or δ, or K-injective resolutions.

The attempted projection construction is retained only as local scratch work at
`scratchpad/natural-attempt.txt`, outside the delivery. It copies the explicit objectwise
construction from `homComplex_single_iso` and uses `homComplex_exists`'s map formula for
naturality. Simplifying the identity source map caused expensive unfolding and timed out;
the final delivered statement is a named public theorem with exactly `by sorry`, a source,
and a complete proof in words. Its edge cases are zero source, zero target, empty scheme,
and arbitrary unbounded target; all are covered by the sole-factor product argument.

## No longer needed

Removed direct imports `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` and
`Sheaf.Algebra.Homology.HomComplex`. The latter remains needed transitively through the
real Hom-complex definition, so its module and node are not globally pruned.
The former module and node `prop-pur-kinjective-resolutions-exist` are unnecessary for this
proof: it uses the existing source-library K-injective replacement rather than the broader
packaging of site generators and degreewise injectivity. The needed replacement is recorded
through `lem-pur-kinjective-degreewise-existence` and is already available through the
public imports of `DerivedInternalHom`.

Replaced the direct `Sheaf.AlgebraicGeometry.HomComplexSingle` import with the natural
comparison module. `lem-sc-hom-complex-single` and its module remain needed by the new
module; their objectwise comparison is not pruned. `def-pur-hom-complex` remains needed
through the construction and the new naturality node. None of these removals asserts that
no other target branch imports the removed module.

## Where the brief, the DAG or earlier work was wrong

The parent plan correctly requires naturality, but `homComplex_single_iso` supplies only
objectwise existence. Its node says that no naturality theorem is required by the parent
proof; this parent does require one. The new node isolates precisely that missing interface.
The unit `sk-thm-picard-duality` has empty realized statement and step lists; no realized
unit statement or proof step is bypassed. All existing public signatures and definitions
are unchanged. No arbitrary data are chosen from a mere unproved existence claim.

## New nodes

`lem-sc-hom-complex-single-natural` states the underived natural chain isomorphism, with
its proof given by the product projections, differential formula, and map formula. Its
module is `lean/Sheaf/AlgebraicGeometry/HomComplexSingleNatural.lean`. The node names the
actual Lean signature verbatim and records the searches run for this delivery. LeanSearch returned an Internal Server Error;
LeanFinder, Loogle, and grep results were recorded without treating the service failure
as evidence that no match exists.
There are no interface change records or forced adaptations.

## Second reading by Y2

1. Compared the delivered parent module with the repository version: all existing declaration signatures, including the target, are byte-for-byte unchanged; only proof-local imports and proof text changed. The added naturality module introduces the new split theorem recorded by its node.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The parent target has no `sorry`; the only remaining `sorry` is the named split theorem `AlgebraicGeometry.homComplex_single_natural_iso`. No forbidden declarations or hollow definitions occur.
3. Read the split statement and node: it is the underived chain-level naturality assertion required by the parent, with a product-projection proof and edge cases covered. It is strictly smaller than the target and has no duplicate declaration found in the local library.
4. Checked the proof route and imports. The proof uses the concrete K-injective replacement, the derived comparison, the new naturality theorem, and localization descent. Removed imports and the obsolete K-injective packaging dependency are documented above; the unit route remains unchanged.
5. Checked DAG agreement: parent proof steps and dependencies match the Lean proof, and the new node's statement, source, proof, and Lean record match its module.

Changed during second reading: appended this review record only; no Lean proof or statement required repair.
