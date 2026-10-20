## What changed

Replaced the single upper `sorry` by assembly of the existing native derived monoidal
localization, its Koszul symmetry, inverse tensorator comparisons and source-level
closedness/section-formula results. The target theorem signature and every existing
public definition and all public imports are unchanged.

Added `RingedDerivedTensorNative`: the native symmetric structure, invertibility of
Q's tensorator when either complex is K-flat, its natural comparison, the simultaneous
K-flat comparison, the unit comparison, and the symmetry/associator/unitor squares.
All declarations in this module are constructed or proved; it has no `sorry`.
The construction uses the generic source-library derived monoidal machinery with the
available independent-universe flat resolutions. No data is selected from an arbitrary
unproved existence claim.

Added the independent source results `RingedDerivedTensorHomAdjunction` (Stacks 08J9)
and `RingedTensorComplexConstraints` (Stacks 0FPQ), and updated the DAG proof route.
The original unit route is retained: `sk-prop-sf-biduality-general` has no realized
statement or step assigned to this item; the item remains below the same biduality
transport node and supplies its full original interface.

Validation: `lcompile.py --all` compiled all four modules in import order.
The observed times were 44.0 s for the native tensor, 8.9 s for the adjunction
statement, 16.9 s for the complex-constraint statement, and 36.2 s for the original
item with its complete assembly proof. The unchanged original declarations and
public imports were compared against the shared source; only proof imports and the theorem proof (including its local notation scope) differ.

## Proved and sorry left

Closed the body of `CategoryTheory.ringedDerived_closed_symmetric_monoidal` (one upper
hole). The complete Lean assembly proves it from the native tensor construction and
the two source results below. This is a decomposition, not a net proof of the item:
one hole closed, two holes added, net minus one within this packet. This is not
a claim about the pinned target-closure ledger. A separate traversal found no
module removed from the current `Challenge` import closure; the 76-module
pruning list below is local to the assigned item.

New remaining holes, each the whole proof of a named theorem:

- `CategoryTheory.RingedDerivedNative.closedAdjunction`, node
  `lem-sf-ringed-derived-tensor-hom-adjunction`.
- `CategoryTheory.RingedDerivedNative.complexConstraints`, node
  `lem-sf-ringed-tensor-complex-constraints`.

Neither is the original assertion under another name. The first fixes the already
constructed tensor and proves only the closed adjunction and evaluation normalization;
it asserts no symmetry, one-K-flat comparison or structural pure-section formulas.
The second concerns arbitrary complexes before localization, without any derived Hom,
K-flatness or adjunction. The native localization construction and the assembly of all
these components are proved Lean code.

The native module proves `localizedSymmetric`, `complex_symmetry`, the inverse lax
coherence lemmas, `homotopySymmetric`, `kFlat_of_acyclic`, `quotientLaxBraided`,
`localization_isIso_mu`, `localization_isIso_ε`, `derivedSymmetric`,
`localizationLaxBraided`, `kFlat`, `isIso_mu`, `tensorIso_naturality`,
`comparison_app`, `symmetry_square`, `associator_square`, `isIso_ε`, `leftUnitor_square`, and
`rightUnitor_square`. The monoidal, symmetric, lax and comparison data are actual
constructions. The source-level axioms they depend on remain existing project items.

## No longer needed

Removed these direct proof imports from the item (some remain transitive dependencies
of the retained native/Hom constructions, so this is not a claim that their source
declarations can be removed):

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`

The old proof route is replaced, so all these old direct `proof_deps` edges and their
obsolete top-level `tool_uses` approvals are removed from the item. Definitions and
foundational tools still needed transitively are retained in the new nodes' routes:

- `lem-pc-sheaf-modules-tensor-closed`
- `prop-pur-kinjective-resolutions-exist`
- `lem-sfb-total-tensor-homotopy`
- `def-pc-tensor-complex-sheaves`
- `def-pur-sheaf-tensor-product`
- `lem-weil-pbc-site-derived-tensor-descent`
- `def-pc-flat-sheaf-modules`
- `lem-pc-kflat-closure`
- `def-pc-kflat-complex`
- `def-weil-abstract-derived-category`
- `def-sfb-monoidal-category`
- `lem-pur-quasi-iso-cone-acyclic`
- `lem-pur-acyclic-kflat-tensor-arbitrary`
- `lem-pc-kflat-resolution`
- `def-pur-derived-internal-hom`
- `lem-pur-hom-kflat-into-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-sc-derived-hom-tensor-total`
- `lem-pur-hom-complex-global-homotopy`
- `def-pur-hom-complex`

In particular, the item no longer needs the custom
`WeilSiteDerivedTensorDescent` / `SiteDerivedTensorDescentIndependentCoefficients`,
`KFlatTelescopeClosure`, or `AcyclicKFlatTensor` route. The generic derived-monoidal
counit criterion proves one-K-flat comparison directly. No source-library declaration
or module is withdrawn. Whether other targets still need an old module is left to
the maintainer's reachability calculation.

The complete item-local import-closure difference is below. These 76 modules are
no longer imported through this item; other consumers may still require them.
This list does not request deletion of any source declaration or module.

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`
- `Sheaf.Algebra.Homology.KFlatClosure`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtExistence`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtUniqueness`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomTensorPair`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomTensorReversePair`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclic`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`
- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
- `WeilConjectures.Algebra.Homology.CyclePullbackCore`
- `WeilConjectures.Algebra.Homology.CyclePullbackLaws`
- `WeilConjectures.Algebra.Homology.CyclePullbackLifting`
- `WeilConjectures.Algebra.Homology.CyclePullbackResolution`
- `WeilConjectures.Algebra.Homology.CyclePullbackTower`
- `WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensorTotal`
- `WeilConjectures.Algebra.Homology.FlatAugmentationEpicification`
- `WeilConjectures.Algebra.Homology.FlatCoverFunctor`
- `WeilConjectures.Algebra.Homology.FlatTruncationSuccessor`
- `WeilConjectures.Algebra.Homology.FlatTruncationTelescopeComparison`
- `WeilConjectures.Algebra.Homology.FlatTruncationTower`
- `WeilConjectures.Algebra.Homology.HomComplexGlobalCochains`
- `WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy`
- `WeilConjectures.Algebra.Homology.HomTensorComparisonNaturality`
- `WeilConjectures.Algebra.Homology.HomTensorCurryNaturalPure`
- `WeilConjectures.Algebra.Homology.HomTensorDegreewise`
- `WeilConjectures.Algebra.Homology.HomTensorDegreewiseConstruction`
- `WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation`
- `WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso`
- `WeilConjectures.Algebra.Homology.HomTensorDifferential`
- `WeilConjectures.Algebra.Homology.HomTensorDifferentialComponent`
- `WeilConjectures.Algebra.Homology.HomTensorDifferentialSummand`
- `WeilConjectures.Algebra.Homology.HomTensorDifferentialSummandPure`
- `WeilConjectures.Algebra.Homology.HomTensorLocalizedExt`
- `WeilConjectures.Algebra.Homology.HomTensorNaturality`
- `WeilConjectures.Algebra.Homology.HomTensorNaturalityComponent`
- `WeilConjectures.Algebra.Homology.HomTensorReverseConstruction`
- `WeilConjectures.Algebra.Homology.HomTensorSectionNaturality`
- `WeilConjectures.Algebra.Homology.HomTensorSummandLocalizedExt`
- `WeilConjectures.Algebra.Homology.HomTensorSummandRestriction`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `WeilConjectures.Algebra.Homology.KFlat`
- `WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree`
- `WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains`
- `WeilConjectures.Algebra.Homology.RelativeFlatExtension`
- `WeilConjectures.Algebra.Homology.TelescopeColimit`
- `WeilConjectures.Algebra.Homology.TelescopeShiftMono`
- `WeilConjectures.Algebra.Homology.TruncationTelescope`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`

## Where the brief, the DAG or earlier work was wrong

The earlier Lean review said the source's derived monoidal instance was unusable
because flat resolutions and graded tensor instances were missing. The current library
provides them at independent coefficient universes. They can be assembled without
constructing a second derived monoidal category or repeating the cone argument.

The existing `homComplex_tensorTotal_iso` and
`isKInjective_homComplex_of_isKFlat` declarations have coefficient universe `max c v`,
whereas this item requires `max c v u`. `RingedInternalHomSignedCalculus` similarly
fixes site/coefficient universes together. They are relevant source results, but do not
literally close the present independent-universe normalized adjunction. The new 08J9
node records that precise remaining result, with a complete mathematical proof and
its own source. The narrower source lemmas are not represented as already applicable Lean proofs;
the new theorem imports only the definitions its statement needs.

The new statements admit the empty site, zero coefficient ring, characteristic two,
arbitrary negative cochain degrees and unbounded complexes. Pure-section formulas
assert identities on the specified generators; they do not assert that global pure
sections generate the sheafified tensor. The one-K-flat comparison needs no
termwise-flatness assumption. The proof's chosen monoidal and comparison data are
fixed constructions, not arbitrary witnesses of an admitted existence theorem.

## New nodes

`lem-sf-ringed-derived-native-tensor` attaches the fully constructed and proved native
localization tensor API. Its proof uses the existing sheaf tensor, independent colimit
and flat-resolution results and the generic derived monoidal localization.

`lem-sf-ringed-derived-tensor-hom-adjunction` isolates Stacks 08J9's normalized
adjunction for that fixed tensor and comparison at independent universes. Its proof
is K-flat/K-injective currying, global H0, localization naturality and evaluation.

`lem-sf-ringed-tensor-complex-constraints` isolates Stacks 0FPQ's formulas for the
native complex constraints on the recorded sheafification generators. Its proof is
right-adjoint lax monoidal coherence followed by the complex summand formulas.

No change record is required: no existing statement or definition was changed and no
consumer adaptation was made.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
