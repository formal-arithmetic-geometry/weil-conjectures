## Worker report

Item: lem-sfb-integral-roos-derived-pullback-unit. Stage 2, NB, 2026-10-22.
Module: Sheaf.Paper.IntegralRoosDerivedPullbackUnit.
Declaration: WeilConjectures.IntegralPullbackStrictRoos.integralRoosDerivedPullbackUnit.
One theorem, with sorry as its whole proof. No definitions, axioms, new nodes,
statement changes or dependency-record changes are delivered.

The earlier dispatch failure concerned attempting a second stage-1 split of an
already reviewed split. This packet states the existing child in Lean; it does not
split it again. The preserved sandbox initially contained only brief markers.
The first dry run confirmed the absence of a packet and did not push anything.

### Hypotheses and objects, matched individually

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension of Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The actual integer ring, uniformizer and quotients
  are those of Padic.CoefficientExtension, through `datum l E = pbcIntegralDatum l E`.
* The positive-characteristic field: `(k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`. For a field its positive
  characteristic is prime; conversely the prime fact excludes characteristic zero.
* Schemes and morphism: `{X Y : Scheme.{u}} (g : X ⟶ Y)`, their `Over` instances
  for `Spec k`, and `[g.IsOver (Spec (.of k))]`.
* Separated schemes: the two `IsSeparated` instances of the structure maps.
* Finite type over k: `LocallyOfFiniteType` and `QuasiCompact` for each structure map.
* The actual small pro-etale sites are `X.ProEt` and `Y.ProEt`, with object universe
  u+1 and morphism universe u; neither is replaced by an equated-universe site.
  Coefficients use the existing u+1 size lift, as does the parent normalization module.
* C_Z and R_Z are the existing `C l E Z` and `R l E Z`. These are respectively the
  constant integral ring and the finite-quotient limit presentation of the continuous
  coefficients. `ImmersionCompletedPullback.completedRingIso` and the integral
  coefficient-limit declaration identify this presentation with pulled coefficients,
  preserving every finite projection. This is the same presentation as in the parent.
* S_(n+1,Z) is `(datum l E).finiteRing Z n`; n runs through all natural numbers,
  so no positive quotient is omitted. `res l E Z` is scalar restriction along the
  recorded constant-function map. `pullR` and `pullC` are the recorded module pullbacks.
* The flat-term K-flat complex P is quantified by `(P : complexesR l E Y)
  (hP : GoodR l E Y P)`. `GoodR` unfolds to the dependency's
  `CochainComplex.IsKFlatIndependentCoefficients` and flatness `IsFlatOnSite` of
  every integer-indexed term. Q is `(cxRes l E Y).obj P`.
* The strict complex towers are the existing `(cxT l E g).obj P`, `cxU` and `cxV`:
  these apply respectively pulled reduction, reduction after completed pullback,
  and constant pullback after restricted reduction. Their existing transitions and
  quotient augmentations are `bT`, `bU` and `bV`, not newly chosen morphisms.
* Localization is `DerivedCategory.Q`; unbounded complexes are indexed by ℤ.
* The signed cone is the existing `roosF`, with coordinates `roosχ`. Its construction
  is Cone(1-s)[-1], with reordered coordinates giving D(y,x)=(-dy-(1-s)x,dx).
  `IsAugmentationNormalized` requires each alpha to be exactly (0,b) in these
  coordinates, on every degree of every complex.
* The normalized comparisons rho are `κR` and `κC`, with limit inclusions `jR,jC`.
  `IsUnitNormalized` requires the inclusion to have coordinates (0,z) and its
  localized composite with kappa to be the actual universal derived-limit unit.
  It therefore fixes the K-injective normalization, rather than choosing unrelated
  isomorphisms of the objects underlying a triangle.

### Conclusions, matched clause by clause

1. `completedCoefficientMap g (datum l E) = ((datum l E).integralRingIso g).hom`
   is c_g=a_R in the common limit presentation. The following `∀ n` equality is
   exactly pr_(n,X) a_R = a_n g^-1(pr_(n,Y)), written in Lean composition order.
   The integralRingIso is the datum's canonical Cartesian isomorphism; it is not
   an arbitrary map supplied as a hypothesis.
2. `IsIso (towerCounit l E g P)` identifies the derived pulled reduction tower
   with qT, using the composite of the two existing universal computation counits.
   `IsIso (completedOrdinaryPullbackComplexCounit ... P)` identifies g_R^*P
   with the ordinary derived pullback of [P]. The final whole-morphism equality
   identifies the *augmentation* as well as the object: q(alpha_T) followed by
   kappa equals the constant-tower unit followed by derived limit of the pulled
   quotient augmentation, transported through those counits.
3. `IsIso (completedReductionTowerComplexCounit ... (cxPullR.obj P))` identifies
   U with the finite derived reductions of ordinary derived pullback.
4. The analogous `OrderedExchange.reductionComplexCounit` is invertible for
   g_C^*Q. The isomorphism `constantTowerIso l E g d a e` identifies V with its
   reduction tower. `IsLambdaNormalized`, `PulledReduction.IsOrdinaryNormalized`
   and the displayed formula for the components of e fix the existing balanced
   tensor comparison on generators. All are natural isomorphisms of strict towers,
   including all transition maps. `IsConstantUnitNormalized` fixes its augmentation.
5. `eR` is the natural derived isomorphism q Roos(U) to completion of the ordinary
   pulled complex, on the full subcategory `GoodR`. Its target is the actual
   `pbcActualCompletion (datum l E) X`, a reflection onto intrinsic complete objects.
   The next-to-last group of equalities says q(alpha_U) followed by eR is its
   actual `pbcActualCompletionUnit`, as an entire derived morphism.
6. `eC` is the corresponding natural isomorphism q Roos(V) to the existing
   `OrderedExchange.completion` of the constant pulled complex. The alpha_V
   equality identifies its whole morphism with `OrderedExchange.unit`.
   The eR target lies in D(R_X); the eC target lies in D(C_X).
7. `ε`, `IsENormalized`, and the displayed equality
   `cxRes.map (αT P) ≫ (ε P).hom = dComplex.hom.app P ≫ αV P`
   identify the scalar-restricted augmentation with the constant construction.
   IsENormalized fixes the map by the identity-on-tuples restriction/product
   comparison and the product of the strict level comparisons on both coordinates.
8. On complete inputs the existing `pbcActualCompletedPullback_tower` and the
   completed/constant equivalence interpret these same strict towers and units
   as Stacks completed inverse image. On arbitrary inputs the explicit eR/eC
   targets are ordinary inverse image followed by completion. These are the two
   domain conventions of the node; no completeness predicate is imposed on P.
9. The three GoodR/GoodC conclusions state the resolving-class properties needed
   for those named computation counits. They expose the canonical representative
   calculations already in the node's proof, rather than adding a resolving-class
   assumption on a quotient tower or replacing any canonical construction.

### Dependency declarations used

The following existing declarations and source signatures/docstrings were read.
Recorded dependencies are used through their modules, without private duplicates.

* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`, with the imported integer ring,
  uniformizer and finite-quotient constructions.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; its field,
  over-scheme, separatedness and finite-type setting is rendered explicitly here.
* Mathlib.CategoryTheory.Sites.ConstantSheaf: `CategoryTheory.constantSheaf`.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `upperStarFromPointComp` and
  `condensedPullbackHom`; the canonical Cartesian coefficient interpretation.
* Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  `SheafOfModules.restrictScalars` (same underlying abelian sheaf).
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and `lowerStar`;
  the sheaf-module versions used by the existing completion modules retain their
  tensor/adjunction normalization.
* Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`, in `GoodR` and `GoodC`.
* Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite:
  `SheafOfModules.IsFlatOnSite`, in the same predicates.
* Mathlib.Algebra.Homology.BifunctorShift: `CochainComplex.mapBifunctor`;
  the existing quotient complex functors use the sheaf tensor and its totalization.
* Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `DerivedCategory.Q`.
* Sheaf.CategoryTheory.StrictRoosComparison: `CategoryTheory.strictRoosComparison`;
  natural descent, injective-resolution normalization and augmented-map interpretation.
* Sheaf.Paper.PbcQbarCompletedPullback publicly retains CompletedTowerPullback and
  PbcActualStrictPullback: `completedCoefficientMap`, `completedTowerPullback`,
  `completedPullbackComparison`, `completedOrdinaryPullbackComplexCounit`,
  `completedReductionTowerComplexCounit`, `pbcActualCompletion`,
  `pbcActualCompletionUnit`, and `pbcActualCompletedPullback_tower`.
  Its current primary record is Qbar-specific; the required original integral
  interface is already publicly imported, so no dependency repair is necessary.
* Sheaf.Paper.ConstantCompletionEquivalence:
  `CategoryTheory.ConstantCompletion.equivalence`, finite reductions, completion,
  completion units and their restriction comparisons, as the proof dependency.

The owning published module Sheaf.Paper.IntegralPullbackStrictRoosNormalization
already supplies `datum`, R/C, ModR/ModC, res, redR/redC, pullR/pullC, T/U/V,
complex functors, GoodR/GoodC, bT/bU/bV, towerCounit, normalization predicates and
constantTowerIso. These definitions are reused verbatim. Its parent theorem is
neither called nor assumed. No theorem is added to stmt_deps, which would create
an inappropriate parent-child dependency cycle. The maintainer must continue to
omit an automatic proof import of this child into that parent owning module,
since that would close an import cycle; proof assembly can use a separate module.

All already stated proof dependencies are imported directly or through public
imports. The two sibling proof nodes without Lean records are not silently
restated: their arguments remain proof dependencies for the later proof stage.

### Edge cases

* Identity g: all finite coefficient maps and normalized balanced maps specialize
  to the canonical identity comparisons; the unit equations still specify actual units.
* P=0: all augmentations and completion units are the unique zero-object maps.
* P=R_Y[0]: it is a valid resolving representative; positive quotients begin at
  pi^1, and no n=0 quotient by the unit ideal is introduced.
* Noncomplete and unbounded P: the quantification only asks for a flat-term
  K-flat representative. Neither finite Tor bounds, boundedness, constructibility
  nor completeness appears as an input hypothesis. Completion is still the target.
* Empty schemes: there is no nonemptiness, point, nonzero sheaf or faithful scalar
  assumption; the sheaf categories and derived units retain their degenerate case.
* Small site sizes: objects u+1 and arrows u are retained exactly; no equality of
  these universes is imposed to use a specialized site API.
* D(R_X) versus D(C_X): connected by the explicit restriction functor and epsilon;
  no equality of these two categories is asserted.

### Searches and validation

* msearch.py leanfinder: "The integral pulled quotient Roos augmentation represents
  the derived completion unit of pullback, with constant and completed coefficient
  sheaves distinguished." Eight hits, all ordinary SheafOfModules pullback/unit
  declarations; none states this derived completion assertion.
* msearch.py loogle: "SheafOfModules.pullback, DerivedCategory.Q". Zero hits.
* msearch.py grep in Mathlib/Algebra: "Roos|completionUnit|completedPullback". Zero hits.
* rg in lean/WeilConjectures and lean/Sheaf for integral/Roos and derived pullback
  augmentation terms found the existing parent helper module, strict Roos comparison,
  CompletedTowerPullback, and IntegralPullbackCompletedComparison. The last concerns
  completed integral pullback on complete inputs and a different representative
  comparison, not this assertion about arbitrary ambient flat-term K-flat inputs.
* Literal search for this item's id in lean/WeilConjectures found no declaration.
* Current server source for Sheaf.Paper.IntegralPullbackStrictRoosNormalization was
  read using scompile.py --source and agrees with the helper interface used here.
* Read current blueprint det-lem-int-tensor-pullback.proof.md, first and Stacks
  comparison paragraphs, and local proetale.tex lemmas naive-completion and
  pushforward-Noetherian-case (099M/099N), particularly (2),(5) and the proof of (5).
* scompile.py passed both the sandbox and library module checks, with no errors
  and no warnings. Final file compile: sandbox 26.0 s; library 17.5 s.
* Every delivered Lean line is at most 100 characters; autoImplicit is false;
  every binder and universe is explicit. Signature in lean.statement is copied
  verbatim from the theorem keyword up to its proof assignment.

No STATEMENT-DISPUTED finding. No correction to the paper, node or dependencies.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
