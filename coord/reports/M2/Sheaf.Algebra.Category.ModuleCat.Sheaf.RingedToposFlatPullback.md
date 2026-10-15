## What changed

The statement of `SheafOfModules.isFlat_ringedToposPullback` is unchanged. Its proof now
separates algebraic inverse image from extension of scalars and completely formalizes the
extension-of-scalars argument of Stacks Tag 05V4.

In the item module, private proved helpers establish that the functor to underlying abelian
sheaves preserves finite colimits under the stated **weak** sheafification assumptions,
that restriction of scalars is exact, and that the tensor comparison reflects exactness
back to the target module category. No stronger `HasSheafify` hypothesis is introduced.

`TensorSheafificationOfUniverses.lean` proves
`PresheafOfModules.sheafification_tensorHom_isIso`. Its proof constructs descent of set
maps by local lifting and unique gluing, descends bilinear pairings, proves additivity and
homogeneity locally, and uses the sheafification adjunction and coyoneda criterion.

`ScalarTensorComparisonOfUniverses.lean` proves
`SheafOfModules.nonempty_scalarTensorComparisonOfUniverses`. It constructs the sectionwise
base-change tensor equivalence using Mathlib, applies the preceding descent theorem to
the scalar-extension sheafification unit, and proves naturality before sheafification.
The resulting comparison requires no flatness of either the coefficient map or the module.

`FlatAlgebraicInverseImageOfUniverses.lean` isolates the pre-scalar-extension inverse-image
step. This is a strict part of the original argument: it has no second coefficient ring
or coefficient map, while the original module contains the complete subsequent exactness
argument and the two comparison modules contain its tensor constructions.

All four delivered modules compile without warnings. The longest local compile was about
50 seconds after moving naturality before sheafification; the item itself compiles in
about 5–13 seconds. An axiom audit shows only `propext`, `Classical.choice`, and
`Quot.sound` for both new proved public theorems; the parent additionally has `sorryAx` from the named remaining
inverse-image lemma. The target signature was compared verbatim with the repository source.
The new statements include the zero module, zero coefficient rings, identity coefficient
maps, empty finite relations, and sites with empty covering sieves; no additional
nonemptiness, nonzero-ring, flat-ring-map, or universe-comparison hypotheses were added.

## Proved and sorry left

Closed the original hole in `SheafOfModules.isFlat_ringedToposPullback`.

Proved with no holes:

- `PresheafOfModules.sheafification_tensorHom_isIso`
  (`lem-weil-pbc-tensor-local-bijection-universes`).
- `SheafOfModules.nonempty_scalarTensorComparisonOfUniverses`
  (`lem-weil-pbc-scalar-tensor-comparison-universes`).
- The item's private helpers `forget_preserves_colimits`, `restrict_exact`,
  `scalarFlat_of_tensorComparison`, and `isFlat_changeOfRingsOfUniverses`.

Added exactly one hole, and this is every hole left in the delivered Lean sources:

- `SheafOfModules.isFlat_algebraicInverseImageOfUniverses`
  (`lem-weil-pbc-flat-algebraic-inverse-image-universes`).

This is a decomposition: one original hole closed and one strictly smaller hole added,
not a claim of a net decrease in holes. The whole scalar-extension part is now proved.
The remaining lemma needs the inverse-image part of Tag 05VD in the original independent
universes. In the site-presentation route it needs the generalized local equational
criterion, representation of finitely many sections and their zero relation at a common
filtered-colimit stage, and transport of the resulting covering and matrix factorization.
The source proof and the empty-relation case are written out in its docstring and node.
A direct route was also checked in scratch Lean: the graph axioms do transport finite
sums, scalar relations, and the finite sums of coefficient products that vanish
in the matrix factorization. The substantial missing ingredients in that route are local
existence of the factorization after inverse image and the generalized flatness criterion.
The underlying-sheaf isomorphism also proves preservation of finite limits by
`I.modules` in scratch Lean (4.3 seconds). This by itself does not prove preservation
of flatness. Another scratch check proves that effective epimorphisms of type-valued
sheaves are locally surjective without `HasSheafify` for types, by descending the map to the image
subsheaf, and that a coequalizer-preserving functor sends effective epimorphisms to
effective epimorphisms when the source has pullbacks. The converse is also proved in
scratch by local lifting and unique gluing, using the sectionwise kernel pair to check independence. Combining these gives a complete scratch
proof that a left adjoint between the categories of type-valued sheaves preserves local
surjectivity, without any `HasSheafify` assumption on types (9.2 seconds). To complete
this alternative route one still needs the finite relation/factorization sheaves and
the generalized flatness criterion. One can encode each finite relation as a finite
limit of powers of the ring and module sheaves and its local matrix factorizations as
an effectively epimorphic family; finite-limit and effective-epimorphic-family
transport would then replace the site-presentation argument.
No unfinished scratch proof is imported by the delivery.

## No longer needed

Removed these original direct imports:

- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`
- `Sheaf.CategoryTheory.RingedToposSitePresentation`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`

The last import is redundant with the public flatness interface; its definitions are
still used. Also removed an initially added redundant direct import of
`Mathlib.CategoryTheory.Limits.Preserves.Finite` (publicly available through `FlatOnSite`).
The scalar comparison also compiles after removing an initially added redundant
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` import. Both proved comparison
modules now publicly import only `TensorProductOfUniverses`, rather than `FlatOnSite`: no
flatness definition is needed for their statements. The direct
`Mathlib.CategoryTheory.Sites.LocallyBijective` import in the tensor descent module and
`Mathlib.LinearAlgebra.TensorProduct.Tower` import in the scalar comparison module also
proved redundant and have been removed.

The parent's former proof dependencies no longer used as declarations are:

- `lem-weil-pbc-ringed-topos-site-presentation`
- `lem-weil-pbc-presheaf-pullback-sets-left-exact`
- `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`
- `lem-pc-sites-sheafification-underlying-sets`
- `lem-pc-sites-module-sheafification-interface`
- `lem-weil-pbc-site-sheafification-sections-local`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-site-flat-equational-criterion`

Their specialized declarations do not serve the delivered independent-universe proof.
The corresponding mathematical work for inverse image is still needed inside the new
inverse-image item; removing these imports does not claim that work has been proved.
No UNIT statement or realized proof step is bypassed: the original node is not itself a
realized UNIT step, and its flat-pullback assertion and its users are preserved.

The following is the complete list of 83 project modules removed from **this item's**
transitive import closure, with their attached nodes where present. This is a local
closure comparison, not a claim that all these modules disappear from every target's
closure; other branches may still use them.

| Module | Attached nodes |
| --- | --- |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` | No direct node attachment |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion` | `lem-weil-pbc-site-flat-equational-criterion` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat` | `lem-weil-pbc-slice-restriction-flat` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` | `lem-pc-sheaf-modules-tensor-closed` |
| `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` | `lem-weil-pbc-module-sheaves-colimits-forgetful` |
| `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` | `def-weil-extension-by-zero-presheaf` |
| `Sheaf.CategoryTheory.IndexedCoveringClass` | `def-weil-pbc-indexed-covering-class` |
| `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` | `lem-pur-site-restriction-module-adjunction-exact` |
| `Sheaf.CategoryTheory.RingedSliceExtensionExactness` | `lem-weil-pbc-ringed-slice-extension-exactness` |
| `Sheaf.CategoryTheory.RingedSliceExtensionTensor` | `lem-weil-pbc-ringed-slice-extension-tensor` |
| `Sheaf.CategoryTheory.RingedToposMorphism` | `def-weil-pbc-ringed-topos-morphism` |
| `Sheaf.CategoryTheory.RingedToposSitePresentation` | `lem-weil-pbc-ringed-topos-site-presentation` |
| `Sheaf.CategoryTheory.SheafAbelianObjectsBijective` | `lem-weil-pbc-sheaf-abelian-objects-bijective` |
| `Sheaf.CategoryTheory.SheafAbelianObjectsInjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-injective` |
| `Sheaf.CategoryTheory.SheafAbelianObjectsSurjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-surjective` |
| `Sheaf.CategoryTheory.SheafRingObjectReconstruction` | `lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction` |
| `Sheaf.CategoryTheory.SheafRingObjectsBijective` | `lem-weil-pbc-sheaf-ring-objects-bijective` |
| `Sheaf.CategoryTheory.SheafRingObjectsInjective` | `lem-weil-pbc-sheaf-ring-objects-injective` |
| `Sheaf.CategoryTheory.SheafRingObjectsSurjective` | `lem-weil-pbc-sheaf-ring-objects-surjective` |
| `Sheaf.CategoryTheory.SheafSubcategoryComparison` | `lem-weil-pbc-sheaf-subcategory-comparison` |
| `Sheaf.CategoryTheory.SheavesAbelianForward` | `lem-weil-pbc-sheaf-abelian-forward` |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian` | `lem-weil-pbc-sheaf-algebraic-structures-abelian-component` |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects` | `lem-weil-pbc-sheaf-algebraic-structures-objects` |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing` | `lem-weil-pbc-sheaf-algebraic-structures-ring-component` |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore` | `lem-weil-pbc-sheaf-algebraic-structures-ring-core` |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism` | `lem-weil-pbc-sheaf-algebraic-structures-ring-morphism` |
| `Sheaf.CategoryTheory.SiteCoveringAxioms` | `def-weil-pbc-sites-and-cohomology` |
| `Sheaf.CategoryTheory.SiteExtensionByZeroExact` | `lem-weil-pbc-site-extension-by-zero-exact` |
| `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf` | `def-weil-pbc-site-extension-by-zero-presheaf` |
| `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint` | `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint` |
| `Sheaf.CategoryTheory.SiteInverseImageTensor` | `lem-weil-pbc-left-exact-site-inverse-image-tensor` |
| `Sheaf.CategoryTheory.SmallSetOfCoveringFamilies` | `lem-weil-pbc-small-set-of-covering-families` |
| `Sheaf.Paper.SiteRestrictionExact` | `lem-weil-pbc-site-restriction-exact` |
| `Sheaf.Paper.SiteSheafificationSectionsLocal` | `lem-weil-pbc-site-sheafification-sections-local` |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce` | No direct node attachment |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` | No direct node attachment |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` | No direct node attachment |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients` | No direct node attachment |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize` | No direct node attachment |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` | No direct node attachment |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` | No direct node attachment |
| `WeilConjectures.CategoryTheory.Monoidal.Conjugate` | No direct node attachment |
| `WeilConjectures.CategoryTheory.Sites.MonObj` | No direct node attachment |
| `WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal` | No direct node attachment |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlus` | No direct node attachment |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf` | No direct node attachment |
| `WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence` | No direct node attachment |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` | No direct node attachment |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits` | No direct node attachment |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering` | No direct node attachment |
| `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` | No direct node attachment |
| `WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT` | No direct node attachment |

## Where the brief, the DAG or earlier work was wrong

The planned `SheafOfModules.isFlat_iff_local_equationalCriterion` is stated for one
universe, a `SmallCategory`, a precoverage with pullback axioms, and the older monoidal
`IsFlat`. The item is stated for independent site, morphism, ring and module universes,
arbitrary Grothendieck topologies, and `IsFlatOnSite`. The planned
`CategoryTheory.ringedTopos_sitePresentation` likewise uses the specialized one-universe
precoverage and `RingedToposMorphism` interface, rather than this item's
`AlgebraicInverseImageOfUniverses`. These are genuine interface mismatches, not obstacles
caused by their proofs still being `sorry`. Neither statement was changed.

For the scalar-extension step, the required comparison and tensor descent in the
independent-universe API were not already stated. They have now been constructed and
proved. The proof of preservation of finite colimits on underlying abelian sheaves also
avoids relying on the stronger sheafification hypothesis used by an older source-library
instance. No existing definition or theorem signature was changed, and no forced
adaptation was necessary. The only immediate importer,
`Sheaf.Paper.KFlatRingedToposPullback` (held by K3), compiles unchanged against the new
module in 4.5 seconds. It imports this item privately.

The first dry run waited on the shared `library-builder.lock`, with many other
deliveries queued. I stopped only this delivery’s waiting preflight and reran
`deliver3.py --no-push` with its supported `WEIL_DELIVERY_CACHE_DISABLE=1` setting.
This selects the normal source scanners; all compile, axiom and static checks remain
enabled. No tool or repository file was modified.

## New nodes

`lem-weil-pbc-tensor-local-bijection-universes` is the proved local descent theorem in
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses`. Its node records
the gluing argument, bilinearity checks, adjunction, and recorded Mathlib searches.

`lem-weil-pbc-scalar-tensor-comparison-universes` is the proved natural tensor comparison
in `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses`. Its node
records the sectionwise base-change equivalence, the tensor sheafification-unit
isomorphism, and naturality, with recorded searches.

`lem-weil-pbc-flat-algebraic-inverse-image-universes` is the sole remaining hole in
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses`. Its node
contains the inverse-image portion of Tag 05VD, including the local equational criterion,
filtered representatives, covering refinements and empty-relation case. It excludes the
now-proved subsequent scalar-extension step. The successful Loogle, LeanFinder and
source searches found no theorem with the needed arbitrary-site and independent-universe statement. LeanSearch was also tried for all
three new nodes; its endpoint returned Internal Server Error, recorded as unavailable
without a mathematical verdict. The other search kinds supplied the fallback.

The removal of two unused public imports and the private helper section are recorded in
`coord/changes/M2-ringed-topos-flat-pullback-imports.md`. Existing signatures and
definitions are unchanged.


## Second reading by M2

1. **Interfaces: PASS.** Compared all four delivered modules with the repository.
   The three support modules are new. The complete existing
   `isFlat_ringedToposPullback` signature, including universes, implicit arguments,
   instances and conclusion, is byte-for-byte unchanged. No existing definition is
   altered. The only public-interface change is removal of the two unused public
   imports recorded in `M2-ringed-topos-flat-pullback-imports.md`; the sole direct
   importer is `Sheaf.Paper.KFlatRingedToposPullback`. No adaptation is delivered. A fresh scratch copy of that importer compiled
   unchanged against the delivered modules in 6.6 seconds.
2. **Proofs and axioms: PASS, with the declared decomposition.** Read the local
   lifting, bilinear descent, sectionwise base-change equivalence, naturality,
   forgetful-colimit argument, exact restriction and exactness-reflection proofs.
   All four sources compiled locally through `lcompile.py`. A separate scratch
   import with `#print axioms` confirms that both new proved public theorems use
   only `propext`, `Classical.choice`, `Quot.sound`. The parent and the remaining
   inverse-image theorem additionally use `sorryAx`, exactly as reported. The
   only source hole is `isFlat_algebraicInverseImageOfUniverses`; there are no
   forbidden declarations or holes in definitions. `localLift` chooses the
   uniquely specified glued section of a proved existence-and-uniqueness theorem.
3. **Split statement: PASS.** Read Stacks `sites-modules.tex`,
   `lemma-pullback-flat` (05VD) and `lemma-flat-change-of-rings` (05V4), and the
   operation graphs and underlying-sheaf isomorphisms of
   `AlgebraicInverseImageOfUniverses`. The remaining statement removes the
   coefficient map and second scalar ring; the parent proves the entire subsequent
   scalar-extension argument, so this is a strict part of the argument rather than
   a restatement. Checked identity inverse image, zero modules and zero rings,
   empty relations and empty covering sieves: none needs an added hypothesis.
   Fresh LeanFinder, Loogle and source searches found no applicable existing result.
   In particular `CategoryTheory.flat_sheafPullback_obj` was opened and rejected as
   a replacement: it treats constant Noetherian coefficients and specialized site
   and value universes. The generalized equational criterion and site-presentation
   work remain substantial; no quick proof of this hole was found. Its docstring
   and node give the source argument, including the empty-relation case.
4. **Route and pruning: PASS.** The proof first reduces to inverse-image flatness,
   then proves scalar extension by the explicit natural tensor comparison and
   exactness reflected on abelian sheaves. The two tensor support modules import
   `TensorProductOfUniverses` publicly for their statements, and the descent module
   is imported privately where used only in a proof. The parent has private proof
   imports. Every one of the nine removed original `proof_deps` is listed under
   `No longer needed`; the current source-closure comparison confirms the listed
   83 project modules removed from this item's closure. This is not a claim about
   their removal from all targets. Opened `sk-thm-properbasechange.json`: neither
   this item nor a removed dependency realizes one of its statement or proof steps,
   and its realized route is preserved.
5. **Nodes: PASS.** Compared the original node with the delivered record: only
   `proof`, `proof_deps`, `proof_origin` change. In all four nodes `proof_deps`
   equals the union of the proof steps' `uses`. The parent records the actual
   inverse-image/scalar-extension reduction; both proved support nodes describe
   the constructions read in Lean. The new nodes carry the source, searches,
   creation record, blueprint reference, chapter, unit and Lean attachment. The
   remaining hole has exactly its declared node and no extra hidden obligation.

Second reading changed the report only: added this independent point-by-point
review and the fresh search/axiom evidence, and corrected the local closure-pruning
list from 86 to 83 modules against the current shared repository. No Lean proof,
statement or definition needed repair. One original hole is closed and one strictly smaller hole is added;
this remains a decomposition with net zero holes closed, with two new support
statements fully proved.
