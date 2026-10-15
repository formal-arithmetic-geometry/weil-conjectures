## What changed

Repaired the return at head 683fc35eb: removed all ten duplicate transport lemmas from
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero`, including the copied
finite-free constructions and additivity instance. Its existing proof-only import of
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback` now supplies the shared proofs.
Made exactly four existing proved helpers public in the pullback module:
`localFinitePresentation_of_iso`, `localFinitePresentation_of_comap`, `constructible_of_iso`,
and `constructible_comap`. Their signatures and proofs are unchanged. All remaining presentation
helpers stay private. The item also reuses this `constructible_of_iso` instead of duplicating it.
The pullback node records the shared helpers, and the extension node explains their reuse.

Retained the earlier repair removing the unsupported generic tensor and internal-Hom
preservation lemmas, their dependent bounded-constructible restrictions and adjunction,
and the unused public import of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`.
No target statement changes. The second reader additionally shares the already proved
`AlgebraicGeometry.ProEtale.upperStarComp_inv_monoidal` instance and makes the item's
Nagata import proof-only.

Change records: `coord/changes/E4-share-constructibility-transport.md` and
`coord/changes/E4-remove-unrestricted-tensor-hom.md`.

## Proved and sorry left

Two of the original five holed declarations are proved:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_obj`.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_openImmersionLowerShriek_obj`.

Both new node-backed constructibility theorems are fully proved:

- `AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_upperStar`
  (`lem-weil-pbc-module-constructible-pullback`).
- `AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek`
  (`lem-weil-pbc-module-constructible-extension-zero`).

The sole remaining `sorry` is the unchanged, disputed
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`
(in the source module attached to `def-weil-pbc-condensed-e-module-category`). Its arbitrary
coefficient statement has the Artin–Schreier counterexample documented at the declaration.
It is not claimed as proved.

The two false holed declarations `boundedConstructible_derivedTensor_obj` and
`boundedConstructible_derivedHom_obj` are removed, not counted as proofs. No new `sorry` or
split-off obligation is added. The four newly exported transport lemmas and the newly exported monoidal-comparison
instance are completed proofs. `#print axioms` checks of these five supporting declarations,
both helper theorems, and both newly proved item lemmas show only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the ten duplicate lemmas from the extension module:
`finitePresentation_of_iso`, `finitePresentation_map`, `finitePresentation_mapMod`,
`finitePresentation_comap`, `finitePresentation_of_comap`, `localFinitePresentation_of_iso`,
`localFinitePresentation_comap`, `localFinitePresentation_of_comap`, `constructible_of_iso`,
and `constructible_comap`. Also removed its duplicate `finiteFree_mapMod`, `finiteFree_comap`,
and `mapMod_additive`. These facts or constructions remain in the pullback module; their
separate proofs in extension by zero are unnecessary. Removed the item's separate private
`constructible_of_iso` proof as well. No helper module or DAG node is pruned. The second reader also removes the duplicate
`upperStarComp_inv_monoidal` instance from extension by zero, reusing the newly public
instance from pullback, and removes extension by zero's unused
`WeilConjectures.CategoryTheory.Monoidal.Conjugate` proof import.

The removed public import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` is no longer needed.
The seven previously removed declarations are no longer needed:
`boundedConstructible_derivedTensor_obj`, `boundedConstructible_derivedHom_obj`,
`boundedConstructibleTensor`, `boundedConstructibleHom`,
`boundedConstructibleTensorObjCompatibility`, `boundedConstructibleHomObjCompatibility`, and
`boundedConstructibleTensorHomAdjunction`. Their ambient implementations remain in their own
modules. No target or unit realization uses the removed declarations.

## Where the brief, the DAG or earlier work was wrong

The previous second reading made the transport lemmas private and copied them into extension
by zero. Privacy did not justify duplicate mathematical proofs: the landing checker correctly
rejected the ten identical statements. This repair exports only the helpers needed by the other
proofs and imports them. The obsolete second-reading verdict is not a review of this repair and
has been removed from this report for the independent reader to replace.

The earlier generic tensor/Hom assertions fail over arbitrary coefficients (for example Z/4
with Z/2 inputs has nonzero Tor and Ext in unbounded degrees). Their removal remains recorded.
The remaining pushforward assertion is separately marked disputed and unchanged.

## New nodes

The delivery retains the two fully proved helper nodes
`lem-weil-pbc-module-constructible-pullback` and
`lem-weil-pbc-module-constructible-extension-zero`. This repair adds no node or proof obligation.
The former node records the five shared supporting declarations; the latter's proof steps
and `proof_deps` now record their reuse. The unit's route is unchanged.

## Second reading by E4

1. **Interfaces.** Compared every delivered module with the read-only repository. The two
   `Sheaf` modules are new; the item retains 19 existing declarations with unchanged
   statement text and unchanged definition bodies. The seven removed declarations are exactly
   those declared in `E4-remove-unrestricted-tensor-hom.md`. A whole-library search and
   `tools/downstream.py --uses` found no outside caller. The record now includes verbatim
   original declarations and all 19 downstream modules with their holders. No target or
   coefficient definition changes. Both direct importers, `Derived.UpperShriek` and
   `BaseChangeTheorems.MorphismDefs`, compile unchanged against the delivered item.

2. **Proofs and data.** Read all three modules and compiled them through `lcompile.py --all`.
   All compile without warnings. Explicit `#print axioms` checks of the two newly proved
   item lemmas, both constructibility theorems and the five exported supporting declarations
   show only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged disputed
   pushforward theorem additionally has `sorryAx`; it is the only local remaining hole.
   The delivery adds no forbidden declaration or compilation escape, no data from an
   unproved existence statement, and no hole in a definition. The existing compactification
   construction is unchanged. The arbitrary-coefficient tensor/Hom counterexample uses the
   exact periodic free resolution of Z/2 over Z/4, so the removals are mathematically justified.

3. **New results and searches.** There are no new split-off holes. Checked the completed
   pullback theorem by tracing finite-free cokernel presentations through inverse image,
   pulled-back covers, pullback-square equalities and coefficient isomorphisms. Checked the
   extension-by-zero theorem through the invertible open restriction unit, vanishing on the
   closed complement, and concatenation of stratifications. Rank-zero presentations, zero
   modules, the empty scheme, the identity immersion and empty-open cases are valid; the
   quasi-compactness assumption supplies constructibility of the open strata in the ambient
   scheme. Searched with different terminology using Loogle (`IsConstructibleModuleObject`),
   Lean Finder (additive finite-colimit functors and finite presentations), and `rg` in
   Mathlib and both local roots. No existing public theorem proves either module-object
   result. Existing isomorphism-invariance proofs in other modules are private and cannot
   be imported through their public interfaces. The transport lemmas within this delivery
   are now shared, including the previously duplicated monoidal-comparison instance.

4. **Route and pruning.** The two boundedness proofs use the exact-functor comparison and
   homology comparison directly, together with the proved constructibility results; neither
   restates the derived target as a lower hole. The new nodes retain the pulled-back and
   open–closed stratification declarations that their proofs use. Inspected
   `dag/units/sk-thm-properbasechange.json`: its realized statement and all three realized
   steps are unchanged, and none uses the removed tensor/Hom restrictions. The existing
   item's attached definition node has no old `proof_deps` to retire. The report lists the
   removed Hom import, duplicate proofs and proof-only import pruning. Nagata remains a
   necessary proof dependency, now imported without `public`.

5. **DAG correspondence.** Both new node statements match the completed Lean theorem
   signatures. Their proof steps follow the code, and `proof_deps` equals the union of
   step uses. Added the missing pullback-helper dependency to the extension node and
   recorded the shared monoidal instance in the pullback node's supporting declarations.
   The new nodes have source, searches, origin, creation, blueprint ancestry, chapter,
   unit and Lean records. Corrected the extension node's source filename from the
   nonexistent `LowerShriek/OpenImmersion/Defs.lean` to `LowerShriek/Open/Defs.lean`.

Second-reading repairs: shared the duplicate monoidal-comparison proof, removed its redundant
Conjugate import, made Nagata a proof-only import, corrected the node dependency and source
path, and made the change records and report match the final sources. No further hole was
added or closed in this reading. Verdict: the two claimed original proofs are valid; the two
removed false assertions are not counted as proofs, and the disputed pushforward remains open.
