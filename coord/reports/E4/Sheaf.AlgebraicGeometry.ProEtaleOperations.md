## What changed

Filled the six original sorry sites in `Sheaf.AlgebraicGeometry.ProEtaleOperations`, with
five direct proofs and one decomposition through a new underlying-abelian comparison.
All existing declaration signatures, visibility, public imports and data definitions are
unchanged, including all public instance bodies. Added only proved private helpers to the
original module. Updated the proof route
of `def-weil-pbc-proetale-operations`; its attachment to the separate canonical-adjunction
module is preserved. There are no forced adaptations or change records.

The tensor maps are packaged into a functor. A sectionwise extension/restriction Hom
bijection, composed with module sheafification, proves the scalar-extension adjunction.
Transporting the model-site module adjunction supplies the module inverse-image adjunction.
Their composite is the prescribed module pullback/direct-image adjunction. Additivity follows
from this adjunction and sectionwise additivity of direct image. Restriction along the
coefficient isomorphism is an equivalence, so its left adjoint preserves finite limits.
Abelian inverse image preserves finite limits by representable flatness of base change.
The new underlying-sheaf comparison then gives module left exactness, and left adjunction
gives finite colimits.

The Grothendieck property on the small model, transported across the module equivalence,
gives K-injective resolutions using the existing source instance. Exact functor instances
prove the K-flat quasi-isomorphism clause. The source right-derived-unit instance handles
K-injective representatives, and the source exact/right-derived adjunction handles the
unbounded derived adjunction.

Validation: both sandbox modules compile together through lcompile.py. Axiom inspection
shows only `propext`, `Classical.choice` and `Quot.sound` for pullback functoriality and
K-injective resolution existence. The operations conjunction and downstream wrappers and
derived results can still depend on `sorryAx` through the one comparison below. Additivity
and finite-colimit preservation themselves are proved by adjunction in the conjunction;
the original public instance wrappers still project from that conjunction.
The added proof imports were tested individually; a redundant additive-adjunction import
was removed, and the other new source imports are required by the compiler.

## Proved and sorry left

All names below are in `AlgebraicGeometry.Scheme`.

Original holes closed without a new obligation of their own:

- `proEtaleRingModulePullback_functorial`.
- `proEtaleRingModules_hasKInjectiveResolutions`.
- `proEtaleRingDerivedPullback_kFlat`.
- `proEtaleRingDerivedDirectImage_kInjective`.
- `proEtaleRingDerivedOperations_adjunction`.

Original hole decomposed:

- `proEtaleRingModuleOperations_properties`: its five-clause conclusion is now proved from
  one strictly smaller comparison plus the proved private adjunction, equivalence and
  additivity helpers. The comparison is used only for finite-limit preservation.

The original item has no sorry left. One hole is added:

- `proEtaleModelModuleInverseImage_underlying`, in
  `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying`, node
  `lem-weil-pbc-proetale-module-inverse-image-underlying`.

Thus six old holes are removed, one new hole is added: five net holes closed, including one
explicit decomposition. This does not claim that the import closure is sorry-free. The
separate canonical normalization in `ProEtaleOperationsCanonicalAdjunction` is untouched.

## No longer needed

Removed these seven direct proof imports from the item:

- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`.
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.

The item's implementation no longer needs the planned results
`lem-weil-pbc-exact-functor-derived-functor`, `lem-pc-kflat-resolution`,
`prop-pur-kinjective-resolutions-exist`, or
`lem-pc-pre-derived-adjoint-functors-general`: the already proved Mathlib/source APIs apply
directly. No K-flat replacement construction is needed, only the quasi-isomorphism in the
given resolution. Likewise `lem-weil-pbc-site-pullback-abelian-exact` is replaced here by
Mathlib's flat Kan-extension and sheaf pullback instances. No modules are withdrawn.
The algebraic-structure and lifted-adjunction results remain available through the existing
inverse-image module and in the comparison node's proof plan; removing their redundant
imports here does not assert that they are globally unreachable. All seven removals are
pruning of this proof's direct dependencies, not a whole-library reachability claim.

A local graph check of this item's imports in the two library roots gives 223 modules
before and 154 after: 75 removed and six added. The only newly reached sorry-bearing
module is the new comparison. This is an item-closure check, not the pinned target ledger
or a claim that these modules are unused by other targets. The removed modules are:

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`.
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`.
- `Sheaf.Algebra.Homology.CyclePullbackCore`.
- `Sheaf.Algebra.Homology.CyclePullbackLaws`.
- `Sheaf.Algebra.Homology.CyclePullbackLifting`.
- `Sheaf.Algebra.Homology.CyclePullbackResolution`.
- `Sheaf.Algebra.Homology.CyclePullbackTower`.
- `Sheaf.Algebra.Homology.CyclePullbackTowerComparison`.
- `Sheaf.Algebra.Homology.FilteredColimitsTensor`.
- `Sheaf.Algebra.Homology.FilteredColimitsTensorTotal`.
- `Sheaf.Algebra.Homology.FlatAugmentationEpicification`.
- `Sheaf.Algebra.Homology.FlatCoverFunctor`.
- `Sheaf.Algebra.Homology.FlatTruncationSuccessor`.
- `Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison`.
- `Sheaf.Algebra.Homology.FlatTruncationTower`.
- `Sheaf.Algebra.Homology.KFlatClosure`.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`.
- `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree`.
- `Sheaf.Algebra.Homology.RelativeFlatExtension`.
- `Sheaf.Algebra.Homology.TelescopeColimit`.
- `Sheaf.Algebra.Homology.TelescopeShiftMono`.
- `Sheaf.Algebra.Homology.TruncationTelescope`.
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`.
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`.
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`.
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`.
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`.
- `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`.
- `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
- `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.HomEquiv`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidFiltration`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomologicalBicomplex`.
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic`.
- `WeilConjectures.FromJoel.Algebra.Homology.TotalComplex`.
- `WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.FromJoel.CategoryTheory.Idempotents.Basic`.
- `WeilConjectures.FromJoel.CategoryTheory.Limits.Constructions.EventuallyConstant`.
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`.
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`.
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`.
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target or existing interface was changed. The first
dry run classified changes of three public instance proof bodies as interface changes;
those bodies were restored verbatim before the final dry run. The tensor notation scope
was also localized to private proof helpers, preserving the original global commands. The node has
no numbered proof array; its construction and argument are in its long statement, which was
read as the plan. Its lean attachment now names the supplementary canonical adjunction;
that attachment was retained, rather than redirected to this older operations module.

The remaining issue is an interface bridge: Mathlib's small-site module pullback is an
abstract left adjoint, while the exactness argument is stated for the action lift of set
inverse image. The supplied algebraic-structure lemmas do not directly identify those two
functors for the chosen inverse-image ring. Existing constant-coefficient module-valued
sheaf comparisons have a different domain and do not supply this varying-ring comparison.
The varying-ring construction in `EtaleInverseImageModuleConstruction` and its action-law
helpers is specialized to the small etale site; it cannot be applied to pro-etale models.
`NoetherianStratumDetection` has a noncommutative analogue, but importing it here closes
an import cycle (checked with import_direction.py).

## New nodes

`lem-weil-pbc-proetale-module-inverse-image-underlying` states only the natural comparison
between the underlying abelian sheaf of the chosen model-site module pullback and
abelian inverse image on those model sites. The importing item already proves transfer of
finite-limit preservation through the up/down module equivalences. Its source is
[Stacks 03D2](https://stacks.math.columbia.edu/tag/03D2) and
[03D3](https://stacks.math.columbia.edu/tag/03D3), `sites-modules.tex`, labels
`lemma-pullback-module` and `lemma-adjoint-push-pull-modules`; the exactness application is
[04JC](https://stacks.math.columbia.edu/tag/04JC). The source proof was read, including the
linearity argument and its omitted converse. The docstring and node spell out the converse
by computing both mates and using injectivity of the adjunction bijection. The comparison
still needs its action lift and its identification with the chosen model-site module left
adjoint formalized, including compatibility of the coefficient-ring unit and naturality.
Those are the precise outstanding tasks; additivity, scalar extension, finite-colimit
preservation, resolutions and derived adjunction are not part of this remaining hole.

Checked the statement conceptually at the identity morphism, zero coefficients and empty
schemes: it is invariant under the model-site equivalences and imposes no nontriviality or
nonemptiness hypothesis. The proof only transports algebraic operations and compares left
adjoints, so it requires no flatness of the scheme morphism. Searched the full blueprint
for “inverse image underlying modules”, “module inverse image” and 03D2, plus the DAG and
both Lean roots. No separate node for this chosen varying-ring module comparison was found.
Mathlib searches are recorded from actual leanfinder, loogle, grep and leansearch calls;
leansearch returned Internal Server Error and is recorded as unavailable.

## Second reading by E4

1. Compared the delivered operations module with the repository version. All existing
   declaration signatures and definitions are byte-for-byte unchanged; the report and DAG
   record the added comparison module and the proof-route edits. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all` and checked for forbidden
   constructs. The operations module has no `sorry`; the sole remaining `sorry` is the
   named theorem `proEtaleModelModuleInverseImage_underlying`, with its matching node and
   source docstring. Verdict: pass, with that explicit split obligation.
3. Searched the Lean roots, DAG and blueprint for the comparison statement and its component
   results. The comparison is a genuinely smaller underlying-abelian statement, tested at
   identity, zero coefficients and empty schemes, and is not duplicated upstream. Verdict:
   pass.
4. Checked the proof from the target downward. The model-site adjunction, scalar extension,
   exactness transfer, K-injective and derived-adjunction routes are used; seven obsolete
   direct imports and their unused planned dependencies are listed under `No longer needed`.
   Verdict: pass; the comparison is the only intentional decomposition.
5. Checked the DAG node proofs, dependencies, origin, unit and Lean attachments against the
   code. The unit route remains `sk-thm-properbasechange`; the new node is marked `split`
   and has the required fields. Verdict: pass.

Changed after this reading: appended this review record only. No Lean statement, definition,
or proof was changed during the second reading.
