## What changed

Proved `SheafOfModules.strictRingSystem_abelian_exists` in the item module.
Constructed morphism abelian groups and the preadditive structure componentwise.
The existing componentwise finite cones and cocones give finite limits and
colimits before an abelian instance is chosen, and evaluation preserves them.
A compatible morphism with invertible components has a compatible componentwise
inverse. Mathlib's `Abelian.PreservesCoimageImageComparison.iso` makes every
evaluated coimage-image comparison invertible. Joint detection of isomorphisms
and `Abelian.ofCoimageImageComparisonIsIso` give the abelian structure.

For uniqueness, normalized additive evaluations determine every component of
addition on morphisms. `AddCommGroup.ext` and `Preadditive.ext` identify the
preadditive structures, and all other abelian fields are propositions. This
avoids the general biproduct uniqueness theorem and its instance search.

A private proved existence theorem packages the abelian structure, its
normalization, and preservation by evaluation. Both the public existence and
exactness theorems use this theorem. Local bindings retain the witnesses rather
than inline them. Moved the unchanged public abelian instance and its existence
theorem below the private finite constructions, avoiding circularity. All new
proof helpers are private and completely proved. All existing public theorem
signatures, public definition bodies, public declarations and public imports
are preserved. In particular, `StrictRingSystem.AbelianNormalized`, the scalar
family, the tensor-coherence record and the theory record retain their original
bodies and representations.

Scalar-restriction and colimit proofs use the proved `toSheaf` preservation
instance directly from
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
Private limit and colimit objects refer to named identity and composition
lemmas. Their universal maps refer to named compatibility lemmas, and transition
cones refer to named naturality lemmas. The same component maps and universal
properties are retained, with compact record terms. These changes are recorded in:

- `coord/changes/Z7-system-limit-object-compact.md`
- `coord/changes/Z7-system-colimit-object-compact.md`
- `coord/changes/Z7-system-universal-witnesses-compact.md`

Isomorphism reflection, the abelian criterion, evaluation, subsequence and
derived declarations use transparency-respecting elaboration. The mapped
comparison lemma receives its source and target categories explicitly, avoiding
repeated inference through the component constructions. The original setting is
scoped to the ordinary pure-tensor definition and tensor-coherence record where
the balanced formulas need it. Unused-variable linting is disabled only for the
unchanged final existence theorem; elaboration, kernel and axiom checks remain
active. The full module with the restored normalization definition and the
unchanged official axiom probe compiled in 52.9 seconds, reporting 158 checked
public declarations and exactly the one remaining theorem with `sorry`.
The compile limit is unchanged.

The public interfaces compiled with all five unchanged direct consumers:
`Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint`,
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`,
`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
`Sheaf.Paper.SmoothPurityNormalizedEquivalence`, and
`Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`. No consumer adaptation was
needed. The final uniqueness proof changes no public definition or statement.

## Proved and sorry left

Closed one existing hole: `SheafOfModules.strictRingSystem_abelian_exists`
(blueprint node `lem-pur-system-level-left-extension`). Its focused compiler axiom
check reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The full
module's official axiom probe reports no non-permitted axiom.

One existing hole remains unchanged:
`SheafOfModules.systemLevelLeftExtensionTheory`, attached to
`lem-pur-system-level-left-extension`. Its existing docstring gives the complete
ordinary-derived construction and its sources. No holes were added or split off.
This delivery proves the abelian foundation; it does not claim the assembled
derived left-extension theory is proved.

## No longer needed

No mathematical node or module is withdrawn. The remaining theorem retains its
DAG route and dependencies. The abelian uniqueness proof does not need
`subsingleton_preadditive_of_hasBinaryBiproducts`; it compares addition through
the normalized evaluations directly.

The following unused private proof imports were
removed from this module; some are still public dependencies or used by other
modules, and the remaining derived-theory construction can import its tools when
its proof uses them:

- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`
- `WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The abelian proof needs neither K-flat resolutions nor derived adjunctions nor
K-injective theory. It uses the direct `toSheaf` preservation instance and
Mathlib's coimage-image comparison API. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The already proved componentwise finite cones and
cocones do not require the abelian structure on strict systems. Moving the
existence theorem below them lets them construct that structure without a new
product-site equivalence or any new unproved lemma. This follows the componentwise
abelian argument in Stacks Tags 03DA and 03DB. The node copy records the direct
abelian foundation and componentwise uniqueness in its first proof step and
proof origin. Its unfinished Grothendieck and derived-extension route, and the
dependencies for that route, are retained.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
