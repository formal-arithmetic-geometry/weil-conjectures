/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Scalar and normalized inverse-limit coherence for ringed open extension

Source: Stacks Project, Tags 09BP, 03DI, 03DJ and 03CY; the final paragraph of
blueprint `lem-cbc-completed-extension-zero-comparison.proof.md`
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence).

## Main statements

- `ringedOpenScalarLimitCoherence`: canonical scalar/open and normalized-limit coherence.
- `CbcLimitNormalized`: the specified ordinary-limit and K-injective normalization.
- `CbcAugmentationCompatible`: compatibility with all strict augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vA uA vB uB vC uC vD uD wA wB wC wD

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual derived postcomposition on strict towers, with levelwise exactness.
Source: Stacks 03DJ, 05RU
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerDerived : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤
    DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The actual complex-to-derived factorization for tower postcomposition.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The ordinary-limit unit normalization of the specified comparison. This is the
K-injective normalization of `exactProductFunctorStrictLimit`: on a K-injective tower
it reads `F lim I → lim FI → Rlim FI`. Its Roos description is precisely that theorem's
signed two-summand formula, not an unspecified triangle isomorphism.
Source: Stacks 0941; normalized comparison in
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop :=
  ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- Canonical localization of a commuting square, using the existing derived composition
and natural-isomorphism transports, including their exact complex factorizations.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H K

/-- The same canonical square on derived strict towers, using levelwise exactness.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  cbcDerivedSquare ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)
    ((Functor.whiskeringRight ℕᵒᵖ B D).obj G)
    ((Functor.whiskeringRight ℕᵒᵖ A C).obj H)
    ((Functor.whiskeringRight ℕᵒᵖ C D).obj K)
    ((Functor.whiskeringRight ℕᵒᵖ A D).mapIso e)

end

/-- The recorded exact-derived adjunction applied to the actual tower adjunction.
Source: Stacks 015F (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedTowerAdjunction
    {A B : Type uA} [Category.{vA} A] [Category.{vA} B] [Abelian A] [Abelian B]
    [HasLimits A] [HasLimits B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    cbcTowerDerived F ⊣ cbcTowerDerived G :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (adj.whiskerRight ℕᵒᵖ)

/-- Unit and counit equations for the scalar/open-extension square.
Source: Stacks 03DI, the two explicit Hom maps
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def CbcAdjunctionCompatible
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop :=
  (∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
    qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) ∧
  (∀ Q : C, e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
    adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q))

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Compatibility with every strict augmentation, written via its ordinary-limit cone
and the universal derived-limit unit. These are precisely the canonical maps of the
signed Roos normalization, including quotient-tower completion units.
Source: Stacks 0941 (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def CbcAugmentationCompatible
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop :=
  ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex A ℤ)
    (gamma : (Functor.const ℕᵒᵖ).obj Q ⟶ X.asFunctor),
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨Q, gamma⟩) ≫ etaA.app X) ≫
      lambda.hom.app (DerivedCategory.Q.obj X) ≫ LB.map ((cbcTowerFactors F).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
      (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨Q, gamma⟩)) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end
end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Existing sheafification specialized to the site's fixed coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

/-- Existing locally bijective description at the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

/-- Existing ring sheafification specialized to the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRingSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} T


variable {T : Scheme.{u}} (U : T.ProEt)
  {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionAdditive (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (localizedSystemExtension.{u + 1, u, 0} R U).Additive :=
  SheafOfModules.localizedSystemExtensionAdditive.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionLimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (localizedSystemExtension.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemExtensionLimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionColimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (localizedSystemExtension.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemExtensionColimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionAdditive (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (localizedSystemRestriction.{u + 1, u, 0} R U).Additive :=
  SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionLimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (localizedSystemRestriction.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionColimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (localizedSystemRestriction.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, 0} R U

/-- The actual restricted coefficient morphism on the slice presentation of the open.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcSliceCoefficientMap :=
  ((ProEt.topology T).overPullback CommRingCat.{u + 1} U).map a


/-- Scalar restriction on the literal restricted ring sheaves. The explicit type retains
Mathlib's ringed slice presentation; the data is the recorded restriction functor itself.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcSliceScalarRestriction :
    ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U) ⥤
      ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U) :=
  scalarRestriction.{u + 1, u, u + 1} (cbcSliceCoefficientMap U a)

/-- Additivity of the existing scalar functor, in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarAdditive : (cbcSliceScalarRestriction U a).Additive :=
  inferInstanceAs (scalarRestriction.{u + 1, u, u + 1} (cbcSliceCoefficientMap U a)).Additive

open Classical in
/-- The sheafified image of one actual extension-presheaf generator.
Source: Stacks 03DI and 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcExtensionGenerator (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) (V : T.ProEtᵒᵖ)
    (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{u + 1, u, 0} R U).obj N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} (𝟙
    (proEtaleModuleCoefficients R).obj)).unit.app
    ((extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients R) U).obj N)).app V
      (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)

variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]

/-- The recorded scalar-restriction exactness in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarLimits : PreservesFiniteLimits (cbcSliceScalarRestriction U a) :=
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (R.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (S.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
  scalarRestriction_limits.{u + 1, u, u + 1, wA} (cbcSliceCoefficientMap U a)

/-- The recorded scalar-restriction exactness in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarColimits : PreservesFiniteColimits (cbcSliceScalarRestriction U a) :=
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (R.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (S.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
  scalarRestriction_colimits.{u + 1, u, u + 1, wA} (cbcSliceCoefficientMap U a)

/-- Scalar restriction and open extension commute canonically, compatibly with their
adjunctions and with the specified normalized inverse-limit comparisons.

Source: Stacks 09BP, 03DI, 03DJ and 03CY; the completed-extension-zero blueprint proof
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence).

Proof plan, following the node:

1. Use the slice-site identification of [lem-weil-proetale-weakly-etale-localization]. For an
$S_U$-module sheaf $N$, the two extension presheaves have the same abelian groups and restriction
maps: at $V$ they are $\bigoplus_{\varphi:V\to U}N(V,\varphi)$. Their $R(V)$-actions are both
$r(s_\varphi)_\varphi=(a_V(r)s_\varphi)_\varphi$, by [def-pc-sheaf-restrict-scalars, def-weil-
extension-by-zero-presheaf]. By [def-weil-presheaf-modules-sheafification], their abelian
sheafifications coincide and the induced $R$-actions coincide by uniqueness of the extending
action. The identity thus induces $e_N:r_TJ_SN\to J_Rr_UN$ and its inverse. A map of $N$ acts on
each summand by the same map on either side, so $e$ is natural.

2. For the adjunction of [lem-pur-site-restriction-module-adjunction-exact], a map $h:N\to j^*Q$
extends to $J N\to Q$ by sending the generator $s$ in the summand indexed by $\varphi:V\to U$ to
$h_{(V,\varphi)}(s)\in Q(V)$, then using sheafification. Conversely restrict such a map and
precompose with the summand inclusion; these operations are inverse since all summand generators
generate the presheaf and sheafification has unique factorization. Consequently $\eta_N$ sends
$s$ to its summand generator followed by sheafification and $\epsilon_Q$ sends each generator to
the same section of $Q(V)$. Scalar restriction changes none of these maps. Also
$j_R^*r_T=r_Uj_S^*$ objectwise. Thus $j_R^*(e_N)\,r_U(\eta_N^S)=\eta_{r_UN}^R$ and
$\epsilon_{r_TQ}^R\,e_{j_S^*Q}=r_T(\epsilon_Q^S)$, with the displayed restriction identification
understood.

3. Scalar restriction preserves kernels because they are sectionwise kernels with the restricted
action; it preserves cokernels because sectionwise quotient groups and their abelian
sheafification are unchanged, with the unique restricted action. These kernel/cokernel
descriptions are [def-weil-sheaf-of-modules-category], and the action is [def-pc-sheaf-restrict-
scalars]. Hence $r_U,r_T$ are exact. Both $J$ and both $j^*$ are exact by [lem-pur-site-
restriction-module-adjunction-exact]. For strict towers the same conclusions hold levelwise by
[lem-weil-tower-category-levelwise-abelian]; the natural transformations of Steps 1–2 satisfy the
tower transition equations by their naturality. Apply all functors and transformations in every
cochain degree. Exactness permits descent to the unbounded derived categories by [lem-sf-exact-
functor-derived-triangulated]. The derived adjunction of [def-weil-exact-derived-adjunction] has
the localized original unit and counit, so the identities in Step 2 descend as well.

4. By [lem-weil-pbc-module-sheaves-limits-sectionwise], a product is the sectionwise product with
coordinate actions. Thus restricting scalars gives exactly the same underlying product and
projections, including the empty product, whose underlying group is zero. Invertibility of the
canonical product comparisons for $J_R,J_S$ is [lem-cbc-ringed-open-extension-products],
applicable since $j$ is quasi-compact; the base need not be quasi-compact or quasi-separated.
Countable products are exact in each of the four ringed categories by [lem-weil-proetale-
countable-products-exact], for arbitrary ring sheaves. Together with Step 3 this verifies all
hypotheses of [lem-cbc-exact-product-functor-strict-limit] for each of $r_T,J_S,J_R,r_U$. Write
$\phi_F$ for their canonical product maps and $\kappa_F$ for the maps on the two signed Roos
summands specified by that node.

5. Hereafter set $A=r_TJ_S$ and $B=J_Rr_U$. For any countable family $(N_n)$ in
$\operatorname{Mod}(S_U)$, with $P=\prod_nN_n$, form
$$u=(\prod_ne_{N_n})\,\phi_{r_T,(J_SN_n)}\,r_T(\phi_{J_S,(N_n)}),\qquad
v=\phi_{J_R,(r_UN_n)}\,J_R(\phi_{r_U,(N_n)})\,e_P.$$ Both have domain $AP$ and codomain
$\prod_nBN_n$. For every projection $\pi_n$ the defining projection equations for $\phi$ give
$\pi_nu=e_{N_n}A(\pi_n)$ and $\pi_nv=B(\pi_n)e_P$. These are equal by naturality of $e$ from Step
1, so $u=v$ by the product universal property. This is a calculation with the canonical maps of
[lem-cbc-exact-product-functor-strict-limit], rather than a choice of a product isomorphism.

6. For a strict tower complex $M$, let $H_M^q=P_M^q\oplus P_M^{q-1}$ and $d(x,y)=(dx,(1-s)x-dy)$,
as fixed in [lem-cbc-exact-product-functor-strict-limit]. Apply Step 5 separately to the families
$(M_n^q)_n$ and $(M_n^{q-1})_n$. Naturality of $e$ for the two biproduct projections shows that
$e_{H_M}$ is diagonal in these coordinates. Its naturality for the differentials and transitions
shows that the resulting equality is an equality of chain maps, with the same minus sign on both
sides. In notation $$K_A=\kappa_{r_T,J_SM}\,r_T(\kappa_{J_S,M}),\qquad
K_B=\kappa_{J_R,r_UM}\,J_R(\kappa_{r_U,M}),$$ the equality is $$H(e_M)K_A=K_Be_{H_M}.$$ All maps
are natural for strict tower chain maps. The cited normalized comparison provides their descent
to the derived categories.

7. Let $\theta$ denote the normalized natural isomorphism $L\to H$ of [lem-cbc-exact-product-
functor-strict-limit]; its normalization agrees with K-injective resolution, not just with an
unspecified Roos triangle. Substitute $\lambda_{F,M}=\theta_{FM}^{-1}\kappa_{F,M}F(\theta_M)$ in
the left-hand side of the required equation. The middle factors $r_T(\theta_{J_SM})$ and its
inverse cancel. Naturality of the target $\theta$ for $e_M:AM\to BM$ then makes that side
$$\theta_{BM}^{-1}H(e_M)K_A A(\theta_M).$$ Substitute the same formula on the right-hand side and
cancel $J_R(\theta_{r_UM})$ with its inverse. Naturality of the derived $e$ for $\theta_M:LM\to
H_M$ gives $B(\theta_M)e_{LM}=e_{H_M}A(\theta_M)$, so the right-hand side is
$$\theta_{BM}^{-1}K_Be_{H_M}A(\theta_M).$$ Step 6 proves these expressions equal. The four
functor occurrences and the target limit are exactly those in the statement. Naturality of
$\lambda$ and $e$ makes the resulting equality natural for every derived strict-tower morphism,
including morphisms represented by roofs.

8. For a strict augmentation $\gamma:\Delta C\to M$, [lem-cbc-exact-product-functor-strict-limit]
states that $\lambda_F\,F(u_\gamma)=u_{F\gamma}$. In the signed coordinates this is the equality
sending $c$ to $((F\gamma_n)(c),0)$, since $\phi_F$ is characterized by its projections. Apply
this assertion successively along $J_S,r_T$ and along $r_U,J_R$. Naturality of $e$ at $\gamma_n$
identifies the resulting augmentations: $e_{M_n}A(\gamma_n)=B(\gamma_n)e_C$. Step 7 therefore
identifies their canonical derived maps after either composite. A quotient-tower completion unit
is the map of its strict quotient augmentation, so it is included. In particular exactness
preserves the quotient maps used in such an augmentation. The argument used neither preservation
of K-injectives by scalar restriction nor tensoring along $a$; no flatness or boundedness is
needed.
-/
theorem ringedOpenScalarLimitCoherence
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (LUR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
    (etaUR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUR)
    (_hUR : LUR.IsRightDerivedFunctor etaUR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) (.up
        ℤ)))
    (LUS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
      S).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
    (etaUS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUS)
    (_hUS : LUS.IsRightDerivedFunctor etaUS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) (.up
        ℤ)))
    (LTR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)))
    (etaTR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTR)
    (_hTR : LTR.IsRightDerivedFunctor etaTR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        (.up
        ℤ)))
    (LTS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)))
    (etaTS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTS)
    (_hTS : LTS.IsRightDerivedFunctor etaTS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        (.up
        ℤ)))
    : ∃ (e : (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ (scalarRestriction.{u + 1, u, u + 1} a)
      ≅
        (cbcSliceScalarRestriction U a) ⋙
          (localizedSystemExtension.{u + 1, u, 0} R
          U))
      (d : (scalarRestriction.{u + 1, u, u + 1} a) ⋙ (localizedSystemRestriction.{u + 1, u, 0} R U)
        ≅
        (localizedSystemRestriction.{u + 1, u, 0} S U) ⋙ (cbcSliceScalarRestriction U a)),
      (∀ (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U))
        (V : T.ProEtᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
        (e.hom.app N).val.app V (cbcExtensionGenerator U S N V phi x) =
          cbcExtensionGenerator U R
            ((cbcSliceScalarRestriction U a).obj N) V phi x) ∧
      (∀ (Q : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) (V : (Over U)ᵒᵖ)
        (x : ((scalarRestriction.{u + 1, u, u + 1} a ⋙ localizedSystemRestriction.{u + 1, u, 0} R
          U).obj Q).val.obj
          V),
        (d.hom.app Q).val.app V x = x) ∧
      CbcAdjunctionCompatible
        (JS := localizedSystemExtension.{u + 1, u, 0} S U)
        (JR := localizedSystemExtension.{u + 1, u, 0} R U)
        (rT := scalarRestriction.{u + 1, u, u + 1} a)
        (rU := cbcSliceScalarRestriction U a)
        (qS := localizedSystemRestriction.{u + 1, u, 0} S U)
        (qR := localizedSystemRestriction.{u + 1, u, 0} R U)
        e d (localizedSystemAdjunction.{u + 1, u, 0} S U)
        (localizedSystemAdjunction.{u + 1, u, 0} R U) ∧
      CbcAdjunctionCompatible
        (JS := (localizedSystemExtension.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (JR := (localizedSystemExtension.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (rT := (scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ))
        (rU := (cbcSliceScalarRestriction U a).mapHomologicalComplex (.up ℤ))
        (qS := (localizedSystemRestriction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (qR := (localizedSystemRestriction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (NatIso.mapHomologicalComplex e (.up ℤ))
        (NatIso.mapHomologicalComplex d (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ)) ∧
      CbcAdjunctionCompatible
        (JS := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U))
        (JR := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U))
        (rT := cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a))
        (rU := cbcTowerDerived (cbcSliceScalarRestriction U a))
        (qS := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} S U))
        (qR := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} R U))
        (cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u +
          1, u, u + 1} a)
          (cbcSliceScalarRestriction U a)
            (localizedSystemExtension.{u + 1, u, 0} R
            U) e)
        (cbcDerivedTowerSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} S U))
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} R U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} S U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} R U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)),
        IsIso (piComparison (scalarRestriction.{u + 1, u, u + 1} a) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (cbcSliceScalarRestriction U a) N)) ∧
      ∃ (lambdaJS : LUS ⋙ (localizedSystemExtension.{u + 1, u, 0} S U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ LTS)
        (lambdarT : LTS ⋙ (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory ≅
          cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a) ⋙ LTR)
        (lambdarU : LUS ⋙ (cbcSliceScalarRestriction U a).mapDerivedCategory ≅
          cbcTowerDerived (cbcSliceScalarRestriction U a) ⋙ LUR)
        (lambdaJR : LUR ⋙ (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U) ⋙ LTR),
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS etaUS etaTS lambdaJS
          ∧
        CbcLimitNormalized (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR etaTS etaTR lambdarT ∧
        CbcLimitNormalized (cbcSliceScalarRestriction U a) LUS
          LUR etaUS etaUR
          lambdarU ∧
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR etaUR etaTR lambdaJR
          ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS
          etaUS etaTS lambdaJS ∧
        CbcAugmentationCompatible (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR
          etaTS etaTR lambdarT ∧
        CbcAugmentationCompatible (cbcSliceScalarRestriction U a)
          LUS LUR
          etaUS etaUR lambdarU ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR
          etaUR etaTR lambdaJR ∧
        ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
          S).over U)),
          (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory.map (lambdaJS.hom.app M) ≫
            lambdarT.hom.app ((cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U)).obj M)
              ≫
            LTR.map ((cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U)
              (scalarRestriction.{u + 1, u, u + 1} a)
              (cbcSliceScalarRestriction U a)
                (localizedSystemExtension.{u + 1, u,
                0} R U)
              e).hom.app M) =
          (cbcDerivedSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u + 1,
            u, u + 1} a)
            (cbcSliceScalarRestriction U a) (localizedSystemExtension.{u + 1, u, 0} R U) e).hom.app
              (LUS.obj M) ≫
            (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory.map (lambdarU.hom.app M)
              ≫
            lambdaJR.hom.app ((cbcTowerDerived (cbcSliceScalarRestriction U a)).obj
              M) := by
  sorry

end AlgebraicGeometry.Scheme
