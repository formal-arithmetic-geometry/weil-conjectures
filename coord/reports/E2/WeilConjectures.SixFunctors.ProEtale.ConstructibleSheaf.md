## What changed

Proved the forward implication of
`AlgebraicGeometry.ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`
in `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`. Its signature, definitions,
public imports and existing reverse implication are unchanged. Two ordinary proof imports
supply the counit isomorphism and reflection of finite local constancy. The etale preimage is
specifically `ν_* F`; its constructibility is established on the original global stratification.

Added five proved support modules under `Sheaf.Paper`: finite models in slice sites, finite
geometric stalks, reflection of finite local constancy, gluing of classicality through a
stratification, and the stratified counit. The gluing proof includes the actual strong induction:
restrict to an affine neighborhood, pull back the stratification, erase the empty selected
stratum on the open complement, apply induction there, and use the open-closed sequence and
closure under extensions. Zariski locality follows from the existing derived open-cover theorem
by placing the sheaf in degree zero and taking zeroth homology.

Restored and proved the DAG-attached but absent module
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`. The returned first version duplicated
seven coefficient-independent private declarations from `ProEtaleAbelianClosedCounit`.
This repair removes all seven and the entire copied affine/localization/counit route. It also
removes the local module-valued detection and disjoint-support helpers, since the current
library already proves them. The sequence now imports
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` and directly applies
`isIso_upperStarLowerStarAdjunction_counit`,
`isZero_upperStar_lowerStar_of_disjoint`, and `isIso_of_isIso_upperStar_of_isCompl`.
No source module is modified. The restored module shrinks from 567 to 107 lines.
The sequence uses the actual counit of `j_! ⊣ j^*` and unit of `i^* ⊣ i_*`;
its exactness is reflected by the two exact restriction functors. The obsolete recorded
`Scheme.proEtaleSheafAdjunction` name is replaced with the current
`ProEtale.upperStarLowerStarAdjunction` name. See
`coord/changes/E2-ProEtaleOpenClosedSequence.md`.

After the repair, all seven delivered Lean modules compile through `lcompile.py --all`,
without errors or warnings (4.2 to 12.2 seconds per file).
The finite-stalk proof constructs a site point from geometric lifts and compares its fiber
with the specified pointed-neighborhood colimit; it never invokes conservativity of geometric
stalks on arbitrary pro-etale sheaves. Edge cases include the empty base or strata, the zero
coefficient ring and zero models, and a full-image immersion which need not be an isomorphism.
The induction deletes an empty stratum rather than treating such an immersion as an isomorphism.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`.
Holes closed: 1. Holes added: 0. Split-offs with a remaining hole: 0.
The returned sandbox already had zero holes, and this repair leaves zero holes.
The repaired `exact_openClosedSequence` was checked with `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound`. The duplicate-statement landing gate also passes.

The following added public declarations are fully proved:

- `AlgebraicGeometry.ProEtale.finiteModels_over`.
- `AlgebraicGeometry.ProEtale.finite_geometricStalk_of_finite_models`.
- `AlgebraicGeometry.ProEtale.isFiniteLocallyConstantSheaf_of_comparison_finite_models`.
- `AlgebraicGeometry.ProEtale.comparison_essImage_of_stratification`.
- `AlgebraicGeometry.ProEtale.isIso_comparison_counit_of_finite_stratification`.
- `AlgebraicGeometry.ProEtale.exact_openClosedSequence`.

No delivered declaration contains `sorry`, and no definition or private helper contains a hole.
These proofs use existing stated dependencies, including lisse-origin comparison, weakly etale
localization, geometric-neighborhood cofilteredness, the affine closed-site statements and the
derived comparison results. Those dependencies retain their existing proofs or holes. This is
stage-3 progress on the assigned module, not a claim that the targets are already axiom-free.
The separate ringed-coefficient theorem `Scheme.finiteRing_constructibleSheaf_origin` is unchanged.

## No longer needed

Repair pruning: deleted `sheaf_mate_app`, `restriction_mate_site`,
`counitPullbackMapContinuous`, `counitMapPullbackContinuous`,
`isIso_counitRestrictionBaseChangeMap_of_isPullback`, `isIso_counitRestrictionMate`, and
`isIso_localized_counit` from the restored sequence module. None is renamed or restated.
Also deleted the copied `counitRestrictionBaseChangeMap`, `affine_ff`, `affine_ff_of_affine`,
`module_closed_counit`, `abPreservesColimitsOfShape`, `abLocalVanish`, `abDetectSections`,
`abDetectMaps`, `abZero`, `abJointZero`, and `abDetectIso`; public library declarations now
supply their only needed conclusions.

Removed the restored sequence module's ordinary imports of
`Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction`,
`Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`,
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact`.
Its direct DAG proof dependencies `lem-exc-closed-site-adjunction` and
`lem-weil-pbc-affine-closed-site-functor-properties` are replaced with
`lem-exc-proetale-closed-fully-faithful`, the existing module-valued counit theorem.
These lower results remain needed transitively by the library's closed-immersion API;
this is reuse and pruning of copied work, not a claim that they are globally unnecessary.


No original import of the assigned module was removed: those public imports remain part of its
existing interface. Only the two needed ordinary proof imports were added.

For the restored open-closed sequence, the previous DAG route through
`lem-weil-pbc-proetale-ringed-open-closed`
(`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`) and
`prop-weil-pbc-proetale-constant-ring-map`
(`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`) is unnecessary. The node's `proof_deps`
and `tool_uses` remove that route. This prunes those two nodes from this proof, not globally
where another parent may still need them. The ModuleCat proof works directly and needs no
ringed-coefficient specialization or constant-ring scalar comparison.

During cleanup, removed the unused proof import of
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit` and the unused ordinary import of
`Mathlib.Algebra.Category.Grp.AB` from the restored sequence module. Removed redundant ordinary
imports of the finite-coefficient upper/lower-star definitions and open lower-shriek definitions,
already publicly supplied by its existing compatibility import. Removed the unused private
supported-unit helper copied during adaptation; exactness needs joint detection and the closed
counit, not that helper.

Second-reading cleanup removed the redundant direct public import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` from
`ProEtaleFiniteModelLocalConstancy`, `ProEtaleFiniteModelStalks`, and
`ProEtaleOpenClosedSequence`; each already publicly receives it through its
upper/lower-star definitions. Also removed redundant ordinary imports:

- From `ProEtaleOpenClosedSequence`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`,
  `Mathlib.CategoryTheory.Adjunction.Mates`, and
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback`.
- From `ProEtaleFiniteModelStalks`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` and
  `Mathlib.CategoryTheory.Filtered.Final`.
- From `ProEtaleStratifiedEssentialImage`:
  `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar`,
  `WeilConjectures.ConstructibleSheaf.Pullback`, and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.

For completeness, the other old `proof_deps` removed from the open-closed node are
`def-weil-extension-by-zero`, `def-weil-pbc-constant-sheaf`,
`def-weil-pbc-exact-sequence`, `def-weil-proetale-inverse-image`, and
`def-weil-sheaf-of-modules-category`. These remain its existing statement dependencies;
the new proof does not need their separate ringed-coefficient statements as proof inputs.
The redundant imports remain available transitively, and no whole library module is
claimed globally pruned.

The fixed-module construction uses the library's underived
`lowerStarComparisonUpperStarBaseChange` for closed direct image. It therefore needs no new
standalone degree-zero derived-direct-image comparison lemma. Existing parent-node attachments
for the separate ringed-coefficient theorem were left unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery overlooked that its generic private mate/counit helpers literally
repeat declarations in `ProEtaleAbelianClosedCounit`. The landing check correctly rejected
this. The repair uses the current public module-valued API rather than exposing private
lemmas, duplicating them, or changing their names. It changes neither existing source-library
signatures nor visibility, and needs no adaptations of another group's files.
The prior second reading predates this repair and is removed for the independent reader
to replace after reviewing the repaired module and DAG route.


The node `lem-weil-pbc-finite-ring-constructible-sheaf-origin` lists the assigned source theorem
only in `lean_audit`; its primary `lean` attachment is the different, stronger ringed-coefficient
statement `Scheme.finiteRing_constructibleSheaf_origin`, with a specified additive comparison
and scalar compatibility. This delivery does not claim to prove that other declaration and does
not overwrite its attachment or proof plan. A dedicated fixed-module node records the theorem
actually assigned and proved here, and its proof dependencies follow the completed Lean proof.

The open-closed sequence node attaches an absent source module and uses an obsolete adjunction
name in its Lean record. The restored module, updated Lean attachment and change record repair
this interface. `tools/downstream.py` cannot index a module which has no source; direct searches
confirm there are no existing consumers to adapt. No other group-held module is changed.

The general classicality gluing step is independent of finite stalk hypotheses; the finite-ring
binder matches the restored sequence interface. Finite stalks are supplied separately before
applying lisse-origin comparison. No equivalence between affine-local constructibility and the
source's finite global partition notion is used.

## New nodes

`lem-weil-pbc-proetale-finite-model-local-constancy` records the transport from scheme pullback
models to localized-site constant models. Its module and theorem are proved.

`lem-weil-pbc-proetale-finite-model-stalks` records finiteness of the specified fixed-module
geometric stalk from these local models, using site points and cofinality. It is proved.

`lem-weil-pbc-comparison-finite-local-constancy-reflection` records the descent of finite local
constancy by lisse origin and full faithfulness. It is proved.

`lem-weil-pbc-comparison-stratified-essential-image` records the generic finite-stratification
gluing argument with its explicit open-closed induction. It is proved.

`lem-weil-pbc-comparison-stratified-counit` combines finite models on strata with classicality
gluing and the adjunction criterion for an invertible counit. It is proved.

`lem-weil-pbc-fixed-module-constructible-origin` records the exact assigned source-library
constructible-origin equivalence without changing the other node's ringed-coefficient attachment.
It is proved and uses the same original global partition to establish the preimage constructible.

The existing `lem-sf-proetale-open-closed-sequence` node has its proof route and Lean record updated;
its mathematical statement is unchanged. Change record:
`coord/changes/E2-ProEtaleOpenClosedSequence.md`.


## Second reading by E2

1. **Statements and visible definitions: pass.** I read the seven delivered modules and
   compared each path with the shared repository. Six supporting files are absent there.
   The diff of `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` changes only the
   equivalence's proof and adds two ordinary proof imports. Every existing signature,
   definition, docstring and public import is byte-for-byte unchanged. In particular the
   conclusion still produces a constructible etale sheaf for the given finite coefficient
   ring and arbitrary scheme, and constructibility still means the original finite global
   scheme stratification. The restored open-closed interface uses the actual adjunction's
   unit and counit; the obsolete name in its old DAG attachment is documented by
   `coord/changes/E2-ProEtaleOpenClosedSequence.md`. No existing consumers of that absent
   module were found. The separate ringed-coefficient origin theorem is untouched.

2. **Proofs and axioms: pass, relative to the reported existing open dependencies.**
   All seven files compiled locally with `lcompile.py --all`, without errors or warnings.
   Static inspection found no delivered `sorry`, forbidden axiom or implementation escape,
   and no holed definition. I also compiled scratch copies of all seven files with
   `#print axioms` for their public theorems. `finiteModels_over` and
   `exact_openClosedSequence` use only `propext`, `Classical.choice`, and `Quot.sound`.
   The finite-stalk, reflection, stratification, counit and origin theorems additionally
   use `sorryAx` from existing open dependencies, including geometric-neighborhood
   cofilteredness, lisse origin and the affine-neighborhood theorem. They introduce no
   new holes. The axiom probe's long-name line caused only a scratch-file line-length
   warning; the delivered sources have no overlong lines. The etale preimage is the
   specified direct image `ν_* F`, not an arbitrary witness of an unproved existence
   theorem. The site point and the erased stratification are explicit constructions;
   their proof fields do not hide missing data.

3. **Supporting statements and small cases: pass.** There are no sorry split-offs.
   `finiteModels_over` transports the same finite module across the slice equivalence.
   `finite_geometricStalk_of_finite_models` constructs the geometric lift point, identifies
   its fiber with the actual neighborhood colimit, and restricts that point to a covering
   slice before evaluating a finite constant model. It uses no geometric-stalk
   conservativity. Reflection uses lisse origin and full faithfulness to lift the
   comparison isomorphism. Stratified gluing assumes only classicality on the strata,
   whereas the counit theorem supplies it from finite models; neither restates the
   constructible-origin equivalence as an unproved lemma. I checked empty bases, empty
   and redundant strata, zero modules and the zero ring. The zero-stratum induction has
   no base points and uses the empty open cover. On the complement the selected stratum
   is genuinely empty and `eraseEmptyStratum` removes exactly that index. An immersion
   with full image is treated as a closed immersion, never asserted to be an isomorphism.

   I independently searched the library and upstream checkout for finite-stalk,
   slice-fiber and stratified-essential-image results. The upstream origin equivalence
   still has the same hole. Additional `msearch.py` searches used LeanFinder's query
   "Restriction to a slice site preserves the fiber at a point, and a finite constant
   sheaf has finite stalks", Loogle's `"essImage", "ShortExact"`, and grep's
   `sheafFiberOverIso|finite.*sheafFiber|essImage_of_openCover|essImage_openClosed`.
   They found generic point-fiber facts but no replacement for the geometric or
   stratified theorems. The proof already uses Mathlib's constant-fiber and final-colimit
   APIs. The existing recorded geometric-topos-point module is absent from this checkout;
   its set-valued attachment is not a reusable compiled module here.

4. **Route, imports and pruning: pass.** I read the local Stacks source
   `proetale.tex`, `lemma-compare-locally-constant` (099Y),
   `lemma-compare-constructible` (09AK), and the open-closed statement (09AH).
   The proof retains local constancy, local closed-stratum selection, induction and
   open-closed gluing. The derived open-cover criterion is applied to the degree-zero
   sheaf, with its bounded-below direct image justified before taking zeroth homology.
   For the extension step the existing `etaleOrigin_of_shortExact` lifts the extension
   boundary; closed direct-image comparison is underived. At the top the same given
   stratification proves the direct image constructible, avoiding any identification
   of affine-local and finite-global constructibility. Both unit records
   `sk-thm-properbasechange` and `sk-prop-sf-comparison`, including `realized`, remain
   unchanged. No realized step is bypassed. The report lists every old direct proof
   dependency removed from the open-closed node and makes no global-pruning claim.
   Proof-only imports are ordinary imports. I tested removing the local-model module's
   lower-shriek definitions import and the stalk module's filtered-colimits import:
   the former supplies `localizationRestriction`, and the latter supplies the
   locally-bijective sheafification instance needed by the constant-fiber isomorphism.
   Both are necessary and were restored; the final Lean sources retain the reviewed
   proof and imports.

5. **DAG and records: pass.** I checked all seven node attachments against the actual
   signatures verbatim, and checked that each `proof_deps` is exactly the union of its
   proof steps' `uses`, with every cited node present. The six new nodes have source,
   creation, blueprint, unit, chapter, search and Lean records. Their proof steps match
   the slice transport, finite-fiber computation, lisse reflection, finite induction,
   counit criterion and final same-stratification argument. The existing open-closed
   node changes only `lean`, `proof`, `proof_deps`, `proof_origin` and permitted
   `tool_uses` deletions. Its proof now directly reuses the public closed-counit,
   disjoint-support and joint-isomorphism-detection API in the imported source module;
   the seven returned duplicate mate/counit declarations are absent. The mathematical
   node statement is unchanged. The stronger ringed origin node's attachment and plan
   are preserved, with the fixed-module theorem recorded separately.

Second-reading changes: added this independent review and its search and axiom evidence.
No Lean proof, signature, definition or DAG edit was needed. The temporary import-removal
checks were reverted. The delivered count is one original hole closed, zero holes added,
zero unfinished split-offs, and no claim of a globally pruned module.
