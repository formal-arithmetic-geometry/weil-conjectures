# CategoryTheory.ConstantLeftModuleInverseImageLift

## Reason

Extract the unchanged normalized lift and its supporting definitions into the module of the exact-transport construction. A second proved result supplies the normalized comparison isomorphisms. Both supporting theorems are fully proved in this delivery. Their names, universes, fields and bodies are unchanged; the original module publicly imports the extraction, preserving the consumer API and mathematical meaning.

## Old

The following declarations occur in Sheaf.CategoryTheory.ConstantLeftModuleInverseImage:

```lean
/-- Constant-coefficient module sheaves, using the recorded general-site category.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :=
  ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget constant scalars, retaining the abelian sheaf.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev V {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget the abelian group structure.
Source: Stacks, 00YV (2) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev U {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
  sheafCompose J (forget AddCommGrpCat.{u})

/-- The underlying-set functor on constant-coefficient modules.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev W {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J (Type u) := V J Λ ⋙ U J

/-- Characterization of a sheaf's addition map by its values on sections.
The projections allow arbitrary choices of categorical products.
Source: Stacks, discussion preceding 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsAddition {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A) : Prop :=
  ∀ (T : Cᵒᵖ) (x : ((U J).obj A ⨯ (U J).obj A).obj.obj T),
    a.hom.app T x =
      @id (A.obj.obj T)
        ((prod.fst : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x) +
      @id (A.obj.obj T)
        ((prod.snd : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x)

/-- A constant scalar endomorphism of the underlying abelian sheaf. This is
not required to be a module morphism when the ring is noncommutative.
Source: Stacks, fixed-ring paragraph in the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsScalar {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) (a : (V J Λ).obj M ⟶ (V J Λ).obj M) : Prop :=
  ∀ (T : Cᵒᵖ) (x : M.val.obj T),
    a.hom.app T x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x

/-- The underlying set sheaf of the sheafified constant ring `Λ_C`.
Source: Stacks, 00YV (2) and 0H7J (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev CoeffSet {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] : Sheaf J (Type u) :=
  (sheafCompose J (forget RingCat.{u})).obj ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Characterization of the addition map of the constant ring sheaf by its values
on sections. Source: Stacks, ring paragraph of the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingAdd {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) +
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

/-- Characterization of the multiplication map of the constant ring sheaf by its
values on sections, in the given order (no commutativity). Source: Stacks, ring
paragraph of the proof of 00YV (blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingMul {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) *
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-- A normalized lift of the given geometric morphism. The set comparisons and
unit equations connect both adjunctions to `L ⊣ R`; addition and scalar equations
specify the transported operations. Zero and negation are determined by addition.
The ring comparison is normalized on every scalar summand of the constant sheaf
(these summands determine it uniquely) and carries the addition and multiplication
transported by `L` to those of the target constant ring.
Source: Stacks, 00YV (2), (5), (6), 0H7J, and the node's proof steps 1--6
(blueprint: lem-pe-constant-left-module-inverse-image). -/
structure ConstantLeftModuleInverseImageLift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) where
  /-- The comparison `f⁻¹|Λ_C| ≅ |Λ_D|`, written on `L` of the constant set sheaf. -/
  ringUnderlying :
    L.obj ((constantSheaf J (Type u)).obj Λ) ≅
      (sheafCompose K (forget RingCat.{u})).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of Λ))
  /-- The comparison carries the addition `L(+) ∘ p⁻¹` transported by `L` to the
  addition of `Λ_D`. -/
  ring_add : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingAdd J Λ m → IsRingAdd K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  /-- The comparison carries the multiplication `L(μ) ∘ p⁻¹` transported by `L`
  to the multiplication of `Λ_D`. With `ring_add`, the bijectivity of the
  comparison and `constant_scalar` at `0` and `1`, it is a ring-sheaf isomorphism
  from the transported ring structure on `f⁻¹Λ_C` to `Λ_D`. -/
  ring_mul : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingMul J Λ m → IsRingMul K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  pointIso : L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
    (constantSheaf K (Type u)).obj PUnit.{u+1}
  constant_scalar : ∀ r : Λ,
    L.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ ringUnderlying.hom ≫
      (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      pointIso.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))
  moduleFunctor : Modules J Λ ⥤ Modules K Λ
  moduleDirect : Modules K Λ ⥤ Modules J Λ
  moduleAdj : moduleFunctor ⊣ moduleDirect
  additive : moduleFunctor.Additive
  preservesFiniteLimits : PreservesFiniteLimits moduleFunctor
  preservesFiniteColimits : PreservesFiniteColimits moduleFunctor
  abelianInverse : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}
  abelianDirect : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}
  abelianAdj : abelianInverse ⊣ abelianDirect
  abelianSetIso : abelianInverse ⋙ U K ≅ U J ⋙ L
  abelianDirectSetIso : abelianDirect ⋙ U J ≅ U K ⋙ R
  abelian_addition : ∀ (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A)
    (b : (U K).obj (abelianInverse.obj A) ⨯ (U K).obj (abelianInverse.obj A) ⟶
      (U K).obj (abelianInverse.obj A)),
    IsAddition J A a → IsAddition K (abelianInverse.obj A) b →
      b ≫ abelianSetIso.hom.app A =
        prod.map (abelianSetIso.hom.app A) (abelianSetIso.hom.app A) ≫
          inv (prodComparison L ((U J).obj A) ((U J).obj A)) ≫ L.map a
  abelian_unit : ∀ A : Sheaf J AddCommGrpCat.{u},
    (U J).map (abelianAdj.unit.app A) ≫
      abelianDirectSetIso.hom.app (abelianInverse.obj A) ≫
      R.map (abelianSetIso.hom.app A) = adj.unit.app ((U J).obj A)
  underlyingIso : moduleFunctor ⋙ V K Λ ≅ V J Λ ⋙ abelianInverse
  directUnderlyingIso : moduleDirect ⋙ V J Λ ≅ V K Λ ⋙ abelianDirect
  moduleSetIso : moduleFunctor ⋙ W K Λ ≅ W J Λ ⋙ L
  moduleSetIso_compatibility : ∀ M : Modules J Λ,
    (U K).map (underlyingIso.hom.app M) ≫ abelianSetIso.hom.app ((V J Λ).obj M) =
      moduleSetIso.hom.app M
  scalar_compatibility : ∀ (M : Modules J Λ) (r : Λ)
    (a : (V J Λ).obj M ⟶ (V J Λ).obj M)
    (b : (V K Λ).obj (moduleFunctor.obj M) ⟶ (V K Λ).obj (moduleFunctor.obj M)),
    IsScalar J Λ M r a → IsScalar K Λ (moduleFunctor.obj M) r b →
      b ≫ underlyingIso.hom.app M = underlyingIso.hom.app M ≫ abelianInverse.map a
  unit_compatibility : ∀ M : Modules J Λ,
    (V J Λ).map (moduleAdj.unit.app M) ≫
      directUnderlyingIso.hom.app (moduleFunctor.obj M) ≫
      abelianDirect.map (underlyingIso.hom.app M) = abelianAdj.unit.app ((V J Λ).obj M)
```

## New

The identical declarations above occur in Sheaf.CategoryTheory.ConstantLeftModuleTransport. The original module re-exports them with:

```lean
public import Sheaf.CategoryTheory.ConstantLeftModuleTransport
```

ConstantLeftModuleInverseImageData and constant_left_module_inverse_image retain their original signatures. No target interpretation changes; no target statement or definition body is altered.

## Users

The source import graph was refreshed on 2026-10-20. It contains 47 current
transitive consumers. The table retains consumers from earlier snapshots, including
the five users named in the return on head `1afa1abf98`, and adds
`Sheaf.Paper.ConstantTowerDirectImageNormalization` named in the current return on
head `b1473c27a`. Every current consumer is listed. The moved declarations retain their
signatures, bodies, and public visibility through re-export, so consumer statements
and definitions keep their meaning. No consumer needs adaptation. Representative
consumers were compiled against the extracted interface. Holder names are from the
current claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstantBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstructibleCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CodimensionOneCostalkReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | P9 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonFlatPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteOpenConstantGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | X5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology | V7 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicConstructibleConstantComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicIntegralConstantModelCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EllAdicRationalConstantModelCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EtaleGeometricCostalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ExcellentEtaleConstantProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteClosedSupportExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IndEtaleDerivedHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | Y5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.KunnethSupported | X3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.LocalSystemTensorMonodromy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.OpenClosedConstructibleTest | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PrimePowerCostalkReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualPurityEtaleLocality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualPurityProperDegreeDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PuncturedPerverseHighComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.QuasiExcellentEtaleDirectImageFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.RegularDimensionFunctionPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.RegularSpecializationGeometry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SemistableCoordinateDivisorPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.StrictLocalRegularIntegralFibres | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportQuotientFlat | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportedGeneratorsCostalkDetection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.TorsionStalkProEtaleResolutionMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.ConstantLeftModuleInverseImage | H3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.DerivedBaseChangeMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.ModuleRestrictionKernelComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.SitePointFibre | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.ObjectDerivedSectionsPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicConstructibleResidueTriangles | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicLisseStratumModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicResidueExtensionClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicStratifiedDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicStratifiedLocalModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdicTorFlatCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.AmplificationProper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundedBelowCtfReflection | W6 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientExtensionReductionModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartCommonStratification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageLisse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportDirectImageTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactificationProjectionPasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ComparisonTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompleteConstantResidueFreeModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompleteProetale | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompleteResidueTopCell | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedScalarShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConcentratedComplexShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedERealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleIntervals | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleIntervalsUnordered | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | D8 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedCompleteIntegralDetailed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedNakayama | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DirectedGaloisFiniteTensorGenerators | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DualBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ExternalRHomConePairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientFlatModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteResidueDualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTorAmplitudeProEtaleModule | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteWindow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrameClassLocalEquality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GaloisPartitionTensorClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GeometricStalkPerfect | W7 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCoherenceTower | B2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | W4 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | W3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | X2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCriterionReductions | X3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralCtfTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsCoefficientPresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsCoefficientRingDiagram | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsCompleteReflection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsCompleteRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsDefinitions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsResidueComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsResidueCriterion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsResidueRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralModelsStacksComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralResidueTor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicComparisonConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicComparisonTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.KummerAdditivity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseCompletedSystemComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | W5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedAffineNeighbourhoodLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.OrientedTripleLimitDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcDescentFunctors | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcRationalTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PerversityLocalizationCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointReductionUnits | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsDerivedReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsFiniteReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsFiniteness | P3 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PotentialRegularBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PreservationConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PrimeFieldTensorDevissage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleConstantModulePullbackComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleConstantModulePullbackHomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleConstructibleExactClosure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperFamilyWitnessCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperOpenCoefficientMate | W8 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PullbackFamilyWitnessCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PullbackTorAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityConcentratedEdge | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityConstantFiniteTor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityConventions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityGysinConstant | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QcqsOrientedTriplePresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalStalkExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RealSheafSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ResidueLisseProjectiveModels | J6 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfDirectImageCTFNonproper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfExchanges | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfIntegralConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfPreservationClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityCoefficientTowers | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerRightExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SmoothTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.StratifiedLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.StratifiedLatticeRank | T9 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.StratumScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | W5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassChern | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassFinite | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassProjective | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassSystems | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaCoefficientSetup | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TwConventions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UniformCompleteTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.VerdierExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilOne | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FlatModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FlatModelGeneration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.GeometricInverseImageConstantModule | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ModuleMapmodPullbackKFlat | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenClosedFlatness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SfCategories | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.SmoothPurity.UniqueAdjointCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.Topology.ProfinitePointSite | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.TotalSiteFreeModuleResolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.TraceFormula.TotalSiteInjectiveCechResolution | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| TargetsCheck | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.Statement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No adaptation; identical definitions and signatures are publicly re-exported. |

## Status

landed 20261020T154618-L-3136826 2026-10-20 (merge of deliver/H3/Sheaf.CategoryTheory.ConstantLeftModuleInverseImage)
