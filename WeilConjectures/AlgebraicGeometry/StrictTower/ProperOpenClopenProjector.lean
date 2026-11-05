/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.StrictTower.OpenBetaSourceFactorization
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-!
# The clopen section projector of a proper/open square

Source: Stacks Project, more-etale.tex, Tag 0F7B; morphisms.tex, Tag 01W6(2);
sites-modules.tex, Tag 03DI; derived.tex, Tag 015F, and the strict-tower refinement
(blueprint: lem-cbc-proper-open-clopen-projector).

All coefficient rings are arbitrary commutative rings. The categories and normalized
operations are the recorded constant-ring module and strict-tower constructions.
The declarations together state the geometry, the section formula, its adjunction
normalization, its termwise descent, and the comparison specializations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u vC uC vD uD wC wD

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The ordinary direct-image adjunction, using exactly the constant-ring comparison.
Source: Stacks 03DA and 03DI
(blueprint: lem-cbc-proper-open-clopen-projector). -/
abbrev clopenModuleAdj {U X : Scheme.{u}} (s : U ⟶ X) :
    modulePullback B s ⊣ moduleDirectImage B s :=
  Scheme.proEtaleRingModuleAdjunction s (coefficients B X) (coefficients B U)
    (constantRingIso B s)

/-- The ordinary open unit is invertible, including on the empty open.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: identify the small pro-etale site of U with the localization of X's site at U.
Restriction of extension by zero recovers the original sheaf, with its specified
unit. Transport along the unit-preserving adjoint identification. -/
theorem clopenModule_openUnit_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : IsIso (moduleJAdj B s).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A s).unit :=
    (openImmersionAdjunctionTriple A s).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A s)
  let ff := (openImmersionLowerShriekAdjunction A s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B s) (R := modulePullback B s)
    (moduleJAdj B s) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A s) (fixedOpen B s)

/-- The direct-image transpose of the inverse ordinary open unit.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector). -/
def clopenModuleToDirect {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] :
    moduleJ B s ⟶ moduleDirectImage B s :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (moduleJ B s) (clopenModuleAdj B s).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (moduleJAdj B s).unit (clopenModule_openUnit_isIso B s))
      (moduleDirectImage B s) ≫ (Functor.leftUnitor _).hom

/-- The canonical transpose is invertible for clopen immersions.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: for a sheaf N on U both extension by zero and direct image have sections
N(H_U). The extension adjunction is given by gluing a prescribed section on H_U
with zero on H_C. Its unit is identity under this model, so the displayed transpose
is identity on N(H_U). Therefore it is an isomorphism, for arbitrary B. -/
theorem clopenModuleToDirect_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (clopenModuleToDirect B s) := by
  let d := moduleClopenIso B s
  have := clopenModule_openUnit_isIso B s
  let ff := (moduleJAdj B s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (moduleDirectImage B s).Full := Functor.Full.of_iso d
  have : (moduleDirectImage B s).Faithful := Functor.Faithful.of_iso d
  have hi (M : Modules B U) : IsIso ((clopenModuleToDirect B s).app M) := by
    have hu : IsIso ((clopenModuleAdj B s).unit.app ((moduleJ B s).obj M)) :=
      (clopenModuleAdj B s).isIso_unit_app_of_iso (d.app M)
    have hv : IsIso ((inv (moduleJAdj B s).unit).app M) := inferInstance
    dsimp only [clopenModuleToDirect, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The ordinary intrinsic projector. Its section characterization is stated below;
no arbitrary splitting or map is chosen.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector). -/
def clopenModulePi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Modules B X) ⟶ modulePullback B s ⋙ moduleJ B s :=
  (clopenModuleAdj B s).unit ≫ Functor.whiskerLeft (modulePullback B s)
    (@inv _ _ _ _ (clopenModuleToDirect B s) (clopenModuleToDirect_isIso B s))

/-- Mathlib's abelian structure on strict towers, with the coefficient universe fixed.
This is the existing functor-category instance over the existing module-sheaf instance.
Source: Stacks 02MZ and 03DA (blueprint: lem-cbc-proper-open-clopen-projector). -/
abbrev clopenTowerAbelian (X : Scheme.{u}) : Abelian (Towers B X) :=
  @Abelian.functorCategoryAbelian ℕᵒᵖ inferInstance (Modules B X) inferInstance
    (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
      (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
      (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}))

/-- Compatibility of an exact natural transformation with localization on complexes.
This predicate records the representative equation using the existing exact-functor
factorizations; it introduces no new derived functor or map.
Source: Stacks 015F and localization's universal property
(blueprint: lem-cbc-proper-open-clopen-projector). -/
def ClopenProjectorDescent
    {A : Type uC} [Category.{vC} A] [aA : Abelian A] [HasDerivedCategory.{wC} A]
    {D : Type uD} [Category.{vD} D] [aD : Abelian D] [HasDerivedCategory.{wD} D]
    (F H : A ⥤ D) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : F ⟶ H) (δ : F.mapDerivedCategory ⟶ H.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    δ.app (DerivedCategory.Q.obj K) ≫ H.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)

attribute [local instance] clopenTowerAbelian
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section ProjectorLocalization

variable {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]
  (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] (p : 𝟭 A ⟶ F ⋙ H)

@[irreducible] private def projector_lift :
    (𝟭 A).mapDerivedCategory ⟶ (F ⋙ H).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    ((𝟭 A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (𝟭 A).mapDerivedCategory (F ⋙ H).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex p (.up ℤ)) DerivedCategory.Q)

@[irreducible] private def projector_map :
    𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso A).inv ≫ projector_lift F H p ≫
    (Functor.mapDerivedCategoryCompIso F H).hom

end ProjectorLocalization

attribute [local irreducible] G J pi alpha gComp jComp jCongr beta betaInv
  jAdj adj towers_hasDerivedCategory

end AlgebraicGeometry.ProEtale.StrictTower
