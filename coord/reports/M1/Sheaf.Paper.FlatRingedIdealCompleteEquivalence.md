## What changed

Proved `CategoryTheory.siteRestrictScalars_exact` using the unchanged underlying additive
sheaf and reflection of finite limits and colimits by the forgetful functor. Proved derived
conservativity using the exact-functor homology comparison. Added private proofs of invariance
of local completeness under isomorphism and of preservation/reflection of completeness by
the specified derived restriction functor, including the bridge from the restriction lemma's
chosen representative to that functor.

Reduced `CategoryTheory.flat_ringed_ideal_complete_equivalence` along the stated Cech route.
It now constructs both complete-subcategory functors, proves their natural isomorphisms, and
uses `Equivalence.mk`; its ambient restriction comparison is the identity natural isomorphism.
The remaining work is isolated into augmented Cech base change and the coefficient action
and evaluation on derived Hom, in two new modules. The first module explicitly constructs
the sheafified tensor functor, proves its functor laws and additivity, constructs its unit and tensor-adjoint lifts, and proves their unit
and augmentation compatibility. Its augmented-model existence theorem is proved from the
remaining quasi-isomorphism of the specified tensor unit.
All three delivered modules compile together without warnings other than the two declared
sorry obligations. The required dry run passes compilation and preflight (review class
CODEX). Its supplemental axiom probe for the scalar-extension module timed out after
60 seconds; the tool explicitly leaves that probe for the merge to rerun. The actual
module compilation passed. The categorical-helper experiment did not improve compilation
time and is not part of the delivery.

No existing public signature or definition changed. No consumer adaptation or change record
is needed.

## Proved and sorry left

Original holes: two.

- Closed by proof: `CategoryTheory.siteRestrictScalars_exact`.
- Closed by decomposition: `CategoryTheory.flat_ringed_ideal_complete_equivalence`, original
  node `lem-weil-pbc-flat-ringed-ideal-complete-equivalence`.
- Added and still sorry: `CategoryTheory.flat_ringed_cech_base_change_unit_quasiIso`, node
  `lem-weil-pbc-flat-ringed-cech-base-change`. Its termwise sheafified scalar extension, unit,
  and compatible augmentation are constructed and proved. What remains is exactness from
  flatness, the comparison with the specified local localization complexes, and cover
  detection of quasi-isomorphy of that concrete unit. Its existing local flat-comparison and
  slice-flatness inputs are imported. It asserts no equivalence and concerns no complete derived object.
- Added and still sorry: `CategoryTheory.ringed_cech_hom_coefficient_action`, node
  `lem-weil-pbc-ringed-cech-hom-coefficient-action`. It still needs the B-action on the Hom
  complex, its descent through the derived localization, and augmentation evaluation with
  the specified canonical completion unit. It has no flatness, ideal, quotient-isomorphism,
  finite-generation, or completeness hypothesis.

Thus one original hole is proved outright and one is decomposed into two strictly smaller
statements; two holes are closed and two are added, net zero. There is no sorry remaining
inside either original proof and no sorry in a definition or private theorem. All remaining
sorries have source, full proof in words, and matching nodes.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.Paper.SiteRestrictionExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`
- `Sheaf.Paper.FlatExtendedCechComparison`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`

Tensor product, slice restriction, slice flatness and flat Cech comparison remain in the
base-change node and module. Hom invariance remains in the coefficient-action node and
module. The independent-universe tensor and flatness modules are not used directly in this
argument; their specialized versions suffice. They can remain reachable through other
modules, so no whole-library pruning is claimed. The constant-ring restriction-of-scalars
module does not supply the varying-ring-sheaf exactness used here and is unnecessary.
The two former direct `tool_uses` entries of the item are removed because their uses now
belong to the two explicitly recorded lower nodes. None of the unit's realized statements
or proof steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proposed Cech argument is mathematically sound. The existing declarations do not provide
the glue from the local flat Cech comparison to an arbitrary globally augmented model, nor
the B-action and evaluation on the R-internal-Hom complex. These are respectively steps 2
and 3/5 of the existing node, now stated explicitly rather than assumed to follow by a short
application. The restriction-local-completeness declaration uses `Q.objPreimage`; the actual
proof must transport it along the exact-functor localization comparison. This transport is
proved here. Exactness needs no flatness or quotient assumption.

## New nodes

`lem-weil-pbc-flat-ringed-cech-base-change`:
`lean/Sheaf/Paper/FlatRingedCechBaseChange.lean`, declaration
`CategoryTheory.flat_ringed_cech_base_change_unit_quasiIso`. Strictly the quasi-isomorphism
of the concrete tensor unit; `flat_ringed_cech_base_change` is proved from it. This is the
augmented-complex comparison
from Tag 099I, before any complete objects or inverse functors. For the zero ideal, the empty
tensor Cech model is the ring complex and the quotient hypothesis makes the coefficient
map an isomorphism. The unit-ideal case consists of contractible complexes.

`lem-weil-pbc-ringed-cech-hom-coefficient-action`:
`lean/Sheaf/Paper/RingedCechHomCoefficientAction.lean`, declaration
`CategoryTheory.ringed_cech_hom_coefficient_action`. Strictly the generic coefficient-action
and evaluation construction of Tag 099I for arbitrary compatible augmented complexes. The
parent separately supplies the Cech model and proves completeness, conservativity and the
two natural isomorphisms on the complete subcategories. Zero complexes satisfy the same
formulas. Blueprint searches for Cech and coefficient action found no existing blueprint
statement of either assertion. Both nodes serve the completed-pullback coefficient
comparison through the original node; all existing target signatures are retained.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
