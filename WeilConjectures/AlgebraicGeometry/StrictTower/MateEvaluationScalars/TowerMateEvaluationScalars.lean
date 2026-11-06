/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport

/-! # Evaluation and scalar restriction of the clopen proper/open mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A7 and 0D6E;
sites-modules.tex, Tags 03DI and 03DJ, and the strict-tower refinement
(blueprint: lem-cbc-tower-mate-evaluation-scalars).

The single-level arrow is the exact descent of the existing ordinary clopen arrow.
All comparison maps are constructed from the specified adjunctions. Index `n` means
positive level `n+1`; no boundedness, flatness or finite-coefficient assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars

section ExactTransformations
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
  {F G : C ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def exactNat (t : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q)

@[reassoc] private theorem exactNat_fac (t : F ⟶ G) (K : CochainComplex C ℤ) :
    (exactNat t).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
      F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory =
      G.mapDerivedCategoryFactors := rfl
  simp only [exactNat, Localization.liftNatTrans_app, hF, hG, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Functor.whiskerRight_app]

variable [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]

end ExactTransformations

section ExactEvaluation
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
  {L : C ⥤ D} {R : D ⥤ C}
  [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

end ExactEvaluation

section ExactScalarDescent
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end ExactScalarDescent

variable (B : Type (u + 1)) [CommRing B]

/-- The existing local-bijection characterization at the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance siteLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

/-- The existing abelian structure with its coefficient universe made explicit.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance modulesAbelian (X : Scheme.{u}) : Abelian (Modules B X) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

/-- The existing single-level exact inverse image, abbreviated for the formulas below.
Source: Stacks 03EK, 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev g {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B Y) ⥤ DerivedCategory (Modules B X) :=
  (modulePullback B f).mapDerivedCategory

/-- The existing single-level total direct image.
Source: Stacks 07A5 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev r {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B X) ⥤ DerivedCategory (Modules B Y) :=
  (moduleDirectImage B f).rightDerivedFunctor

/-- Exact descent of the existing single-level extension by zero.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev j {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    DerivedCategory (Modules B U) ⥤ DerivedCategory (Modules B X) :=
  (moduleJ B f).mapDerivedCategory

/-- The specified single-level derived adjunction.
Source: Stacks 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev dAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : g B f ⊣ r B f :=
  (clopenModuleAdj B f).mapDerivedCategoryRightDerivedAdjunction

/-- The exact single-level open adjunction, with its original unit and counit.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def dJAdj {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] : j B f ⊣ g B f :=
  (moduleJAdj B f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (modulePullback B f).rightDerivedFunctorIsoMapDerivedCategory

/-- The existing exact evaluation factorization with the original coefficient universe.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def evaluationFactors (X : Scheme.{u}) (n : ℕ) :=
  @Functor.mapDerivedCategoryFactors (Towers B X) inferInstance
    (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)
    (Modules B X) inferInstance (modulesAbelian B X)
    (inferInstance : HasDerivedCategory (Modules B X))
    ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)) inferInstance inferInstance inferInstance

variable {B} {Λ : Type (u + 1)} [CommRing Λ]

/-- Apply the existing constant-sheaf functor to the coefficient homomorphism.
Source: Stacks 0H7J (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def coefficientMap (φ : B →+* Λ) (X : Scheme.{u}) : coefficients B X ⟶ coefficients Λ X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

/-- Constant-section identifications commute with any coefficient homomorphism.
Source: Stacks 0H7J, 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the tower realization theorem's coefficient-naturality clause computes both
adjoints on a constant section b as the constant section φ(b). Sheafification's
universal property gives equality, and taking inverse-image adjoints gives this square. -/
theorem coefficient_square (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantRingIso B f).hom ≫ coefficientMap φ X =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap φ Y) ≫
        (constantRingIso Λ f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom φ)).symm

/-- The recorded sectionwise restriction functor for the actual constant ring-sheaf map.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev moduleRes (φ : B →+* Λ) (X : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap φ X)

/-- Exactness on kernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_limits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).1

/-- Exactness on cokernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_colimits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteColimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).2.1

/-- Exact descent of scalar restriction, on ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev Res (φ : B →+* Λ) (X : Scheme.{u}) :
    DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules B X) :=
  (moduleRes φ X).mapDerivedCategory

/-- The canonical ordinary scalar/inverse-image comparison, with direction as displayed.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarGModule (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback Λ f ⋙ moduleRes φ X ≅ moduleRes φ Y ⋙ modulePullback B f :=
  (@asIso _ _ _ _
    (Scheme.proEtaleRingRestrictionPullbackInv f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))).symm

/-- The canonical inverse-image scalar comparison after exact descent.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarG (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    g Λ f ⋙ Res φ X ≅ Res φ Y ⋙ g B f :=
  Scheme.proEtaleRingRestrictionDerivedPullback f (coefficients B Y) (coefficients Λ Y)
    (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
    (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f)

/-- The ordinary open comparison in the inverse direction, fixed by its open-unit transpose.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJInv (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleRes φ U ⋙ moduleJ B f ⟶ moduleJ Λ f ⋙ moduleRes φ X :=
  ((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm (scalarGModule φ f).hom).natTrans

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The open-unit transpose is invertible for arbitrary coefficient maps.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: identify the pro-etale open site with the slice. Apply
lem-cbc-ringed-open-scalar-adjunction: on the extension presheaf every direct-sum
summand is unchanged, its map is identity, and the remaining values are zero.
The theorem preserves the open units and counits, so uniqueness of transpose
identifies its inverse with scalarJInv. No flatness is needed. -/
theorem scalarJInv_app_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (M : Modules Λ U) :
    IsIso ((scalarJInv φ f).app M) := by
  have hIso : IsIso (FiniteOpenScalars.openResMap φ f) := by
    -- Paste through fixed coefficient coordinates, then take open inverse mates.
    let α := TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).hom
    let β := FiniteOpenScalars.fixedPull (A := B) f
    let γ := FiniteOpenScalars.fixedPull (A := Λ) f
    let δ := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom
    have : IsIso α.natTrans := by dsimp only [α, TwoSquare.mk]; infer_instance
    have : IsIso β.natTrans := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso γ.natTrans := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso δ.natTrans := by dsimp only [δ, TwoSquare.mk]; infer_instance
    have : IsIso (TwoSquare.hComp γ δ).natTrans := by
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let oa := moduleJAdj Λ f
    let ob := moduleJAdj B f
    let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) f
    let od := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) f
    have := fixedRestriction_equivalence B U
    have := fixedRestriction_equivalence B X
    have := fixedRestriction_equivalence Λ U
    have := fixedRestriction_equivalence Λ X
    have : IsIso ((mateEquiv oa od).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv γ.natTrans))).natTrans :=
      inverseMate_isIso_of_equivalences oa od _
    have : IsIso ((mateEquiv od oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv δ.natTrans))).natTrans := by
      simp only [δ, TwoSquare.mk, TwoSquare.natTrans, IsIso.Iso.inv_hom]
      rw [← scalarPullbackModel_eq B f Λ φ]
      exact scalarOpenModel_isIso B f Λ φ
    have hw : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _
          (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans))).natTrans := by
      rw [inv_hComp, inverseMate_vComp oa od oc]
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let w := TwoSquare.mk _ _ _ _ (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans)
    let t := TwoSquare.hComp α β
    have : IsIso t.natTrans := by
      dsimp only [t, TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let z := Functor.isoWhiskerRight (FiniteOpenScalars.resFixed φ X) _ ≪≫
      asIso (TwoSquare.hComp γ δ).natTrans ≪≫
      Functor.isoWhiskerLeft (modulePullback Λ f) (FiniteOpenScalars.resFixed φ U).symm
    have ht : CategoryTheory.inv t.natTrans =
        ((w.whiskerRight (FiniteOpenScalars.resFixed φ U).hom).whiskerLeft
          (FiniteOpenScalars.resFixed φ X).inv).natTrans := by
      have hz : t.natTrans = z.hom :=
        congrArg TwoSquare.natTrans (FiniteOpenScalars.resPull_fixed φ f)
      calc
        CategoryTheory.inv t.natTrans = CategoryTheory.inv z.hom :=
          IsIso.inv_eq_inv.mpr hz
        _ = _ := by
          simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
            Functor.isoWhiskerRight_inv, Iso.symm_inv, asIso_inv, w,
            TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
    have hi : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans))).natTrans := by
      rw [ht]
      exact inverseMate_iso_edges oa oc (FiniteOpenScalars.resFixed φ U)
        (FiniteOpenScalars.resFixed φ X).symm w
    let x := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).inv)
    let y := (mateEquiv ob oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β.natTrans))
    have : IsIso y.natTrans := inverseMate_isIso_of_equivalences ob oc _
    have he : (mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans)) = TwoSquare.hComp x y := by
      dsimp only [t]
      rw [inv_hComp]
      exact inverseMate_vComp oa ob oc _ _
    rw [he] at hi
    exact isIso_of_hComp x y
  change IsIso ((FiniteOpenScalars.openResMap φ f).app M)
  have := hIso
  infer_instance

set_option linter.style.haveILetI false in
theorem scalarJInv_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : IsIso (scalarJInv φ f) := by
  letI : ∀ M : Modules Λ U, IsIso ((scalarJInv φ f).app M) :=
    fun M ↦ scalarJInv_app_isIso φ f M
  exact NatIso.isIso_of_isIso_app _

/-- The canonical section-normalized ordinary open scalar comparison.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJModule (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleJ Λ f ⋙ moduleRes φ X ≅ moduleRes φ U ⋙ moduleJ B f :=
  (@asIso _ _ _ _ (scalarJInv φ f) (scalarJInv_isIso φ f)).symm

section ScalarCalculations

attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback

attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars

private theorem moduleRes_eq (φ : B →+* Λ) (X : Scheme.{u}) :
    moduleRes φ X = FiniteOpenScalars.res φ X := rfl

private theorem scalarGModule_eq (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarGModule φ f = (FiniteOpenScalars.pullRes φ f).symm := rfl

attribute [local irreducible] scalarGModule

section ScalarCompatibility

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  {u₀ : A₀ ⥤ B₀} {u₁ : A₁ ⥤ B₁} {u₂ : A₂ ⥤ B₂}
  {F G H : A₀ ⥤ A₁} {F' G' H' : B₀ ⥤ B₁}

private theorem scalarPaste_naturality {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') {M N : A₀} (f : M ⟶ N) :
    u₂.map (P.map (F.map f)) ≫ (b.hom.app (F.obj N) ≫ P'.map (a.hom.app N)) =
      (b.hom.app (F.obj M) ≫ P'.map (a.hom.app M)) ≫ P'.map (F'.map (u₀.map f)) := by
  have ha := a.hom.naturality f
  have hb := b.hom.naturality (F.map f)
  dsimp only [Functor.comp_map] at ha hb
  rw [← Category.assoc, hb, Category.assoc, ← P'.map_comp, ha, P'.map_comp,
    Category.assoc]

private def scalarPaste {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') :
    (F ⋙ P) ⋙ u₂ ≅ u₀ ⋙ (F' ⋙ P') :=
  NatIso.ofComponents (fun M ↦ b.app (F.obj M) ≪≫ P'.mapIso (a.app M))
    (fun f ↦ scalarPaste_naturality a b f)

private theorem scalarPaste_hom {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).hom.app M = b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) := rfl

private theorem scalarPaste_inv {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).inv.app M = P'.map (a.inv.app M) ≫ b.inv.app (F.obj M) := rfl

private def ScalarCompatible (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G') : Prop :=
  ∀ M, u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M)

private theorem scalarCompatible_apply
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'}
    {t : F ⟶ G} {t' : F' ⟶ G'} (h : ScalarCompatible t t' a b) (M : A₀) :
    u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M) := h M

private theorem scalarCompatible_of_inverse
    (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G')
    (h : ∀ M, a.inv.app M ≫ u₁.map (t.app M) = t'.app (u₀.obj M) ≫ b.inv.app M) :
    ScalarCompatible t t' a b := by
  intro M
  apply (cancel_epi (a.inv.app M)).1
  apply (cancel_mono (b.inv.app M)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj] using h M

private theorem scalarCompatible_identity (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    ScalarCompatible (𝟙 F) (𝟙 F') a a := by
  intro M
  dsimp only [Functor.comp_obj]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem scalarCompatible_of_id (a : F ⋙ u₁ ≅ u₀ ⋙ F')
    (t : F ⟶ F) (t' : F' ⟶ F') (ht : t = 𝟙 F) (ht' : t' = 𝟙 F') :
    ScalarCompatible t t' a a := by
  subst t
  subst t'
  exact scalarCompatible_identity a

private theorem scalarCompatible_transport {I : Type*}
    (L : I → (A₀ ⥤ A₁)) (L' : I → (B₀ ⥤ B₁))
    (a : ∀ x, L x ⋙ u₁ ≅ u₀ ⋙ L' x)
    (t : ∀ {x y : I}, x = y → (L x ⟶ L y))
    (t' : ∀ {x y : I}, x = y → (L' x ⟶ L' y))
    (ht : ∀ x, t (rfl : x = x) = 𝟙 (L x))
    (ht' : ∀ x, t' (rfl : x = x) = 𝟙 (L' x))
    {x y : I} (h : x = y) : ScalarCompatible (t h) (t' h) (a x) (a y) := by
  subst y
  exact scalarCompatible_of_id (a x) _ _ (ht x) (ht' x)

private theorem scalarCompatible_comp
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {c : H ⋙ u₁ ≅ u₀ ⋙ H'}
    {t : F ⟶ G} {t' : F' ⟶ G'} {s : G ⟶ H} {s' : G' ⟶ H'}
    (ht : ScalarCompatible t t' a b) (hs : ScalarCompatible s s' b c) :
    ScalarCompatible (t ≫ s) (t' ≫ s') a c := by
  intro M
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [hs M, reassoc_of% (ht M)]

private theorem scalarCompatible_inv
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {e : F ≅ G} {e' : F' ≅ G'}
    (h : ScalarCompatible e.hom e'.hom a b) :
    ScalarCompatible e.inv e'.inv b a := by
  intro M
  apply (cancel_epi (u₁.map (e.hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (h M), Iso.hom_inv_id_app, Category.comp_id]

private theorem scalarCompatible_whiskerLeft
    {P : A₂ ⥤ A₀} {P' : B₂ ⥤ B₀} (c : P ⋙ u₀ ≅ u₂ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerLeft P t) (Functor.whiskerLeft P' t')
      (scalarPaste c a) (scalarPaste c b) := by
  intro M
  simp only [Functor.whiskerLeft_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% (h (P.obj M))]
  exact congrArg (a.hom.app (P.obj M) ≫ ·) (t'.naturality (c.hom.app M)).symm

private theorem scalarCompatible_whiskerRight
    {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂} (c : P ⋙ u₂ ≅ u₁ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerRight t P) (Functor.whiskerRight t' P')
      (scalarPaste a c) (scalarPaste b c) := by
  intro M
  have hn := c.hom.naturality (t.app M)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.whiskerRight_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, h M, Functor.map_comp]

private theorem scalarPaste_refl_right (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    scalarPaste (P := 𝟭 A₁) (P' := 𝟭 B₁) a (Iso.refl u₁) = a := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app,
    Functor.id_map]
  erw [Category.id_comp]

private theorem scalarCompatible_projector
    {P : A₁ ⥤ A₀} {P' : B₁ ⥤ B₀}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₀ ≅ u₁ ⋙ P')
    (t : 𝟭 A₀ ⟶ F ⋙ P) (t' : 𝟭 B₀ ⟶ F' ⋙ P')
    (h : ∀ M, u₀.map (t.app M) ≫ b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) =
      t'.app (u₀.obj M)) :
    ScalarCompatible (u₀ := u₀) (u₁ := u₀) (F := 𝟭 A₀) (F' := 𝟭 B₀)
      t t' (Iso.refl u₀) (scalarPaste a b) := by
  intro M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app]
  exact (h M).trans (Category.id_comp _).symm

private theorem scalarCompatible_associator
    {A₃ B₃ : Type*} [Category A₃] [Category B₃]
    {u₃ : A₃ ⥤ B₃} {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    {Q : A₂ ⥤ A₃} {Q' : B₂ ⥤ B₃}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P')
    (c : Q ⋙ u₃ ≅ u₂ ⋙ Q') :
    ScalarCompatible (Functor.associator F P Q).hom
      (Functor.associator F' P' Q').hom
      (scalarPaste (scalarPaste a b) c) (scalarPaste a (scalarPaste b c)) := by
  intro M
  simp only [Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    scalarPaste_hom, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]

private def scalarAlphaPaste
    {A₃ A₄ : Type*} [Category A₃] [Category A₄]
    (Q : A₀ ⥤ A₁) (S : A₁ ⥤ A₂) (J : A₂ ⥤ A₁) (K : A₁ ⥤ A₃)
    (I : A₀ ⥤ A₄) (P : A₄ ⥤ A₃) (L : A₀ ⥤ A₂) (E : A₂ ⥤ A₃)
    (π : 𝟭 A₁ ⟶ S ⋙ J) (β : I ⋙ P ⟶ Q ⋙ K)
    (jc : J ⋙ K ⟶ E) (gc : Q ⋙ S ⟶ L) : I ⋙ P ⟶ L ⋙ E :=
  β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) K ≫
    Functor.whiskerRight (Functor.associator Q S J).inv K ≫
    (Functor.associator (Q ⋙ S) J K).hom ≫
    Functor.whiskerLeft (Q ⋙ S) jc ≫ Functor.whiskerRight gc E

private theorem scalarCompatible_six
    {A₃ A₄ B₃ B₄ : Type*} [Category A₃] [Category A₄] [Category B₃] [Category B₄]
    {u₃ : A₃ ⥤ B₃} {u₄ : A₄ ⥤ B₄}
    (Q : A₀ ⥤ A₁) (Q' : B₀ ⥤ B₁) (S : A₁ ⥤ A₂) (S' : B₁ ⥤ B₂)
    (J : A₂ ⥤ A₁) (J' : B₂ ⥤ B₁) (K : A₁ ⥤ A₃) (K' : B₁ ⥤ B₃)
    (I : A₀ ⥤ A₄) (I' : B₀ ⥤ B₄) (P : A₄ ⥤ A₃) (P' : B₄ ⥤ B₃)
    (L : A₀ ⥤ A₂) (L' : B₀ ⥤ B₂) (E : A₂ ⥤ A₃) (E' : B₂ ⥤ B₃)
    (aQ : Q ⋙ u₁ ≅ u₀ ⋙ Q') (aS : S ⋙ u₂ ≅ u₁ ⋙ S')
    (aJ : J ⋙ u₁ ≅ u₂ ⋙ J') (aK : K ⋙ u₃ ≅ u₁ ⋙ K')
    (aI : I ⋙ u₄ ≅ u₀ ⋙ I') (aP : P ⋙ u₃ ≅ u₄ ⋙ P')
    (aL : L ⋙ u₂ ≅ u₀ ⋙ L') (aE : E ⋙ u₃ ≅ u₂ ⋙ E')
    (π : 𝟭 A₁ ⟶ S ⋙ J) (π' : 𝟭 B₁ ⟶ S' ⋙ J')
    (β : I ⋙ P ⟶ Q ⋙ K) (β' : I' ⋙ P' ⟶ Q' ⋙ K')
    (jc : J ⋙ K ⟶ E) (jc' : J' ⋙ K' ⟶ E')
    (gc : Q ⋙ S ⟶ L) (gc' : Q' ⋙ S' ⟶ L')
    (hπ : ∀ M, u₁.map (π.app M) ≫ aJ.hom.app (S.obj M) ≫ J'.map (aS.hom.app M) =
      π'.app (u₁.obj M))
    (hβ : ScalarCompatible β β' (scalarPaste aI aP) (scalarPaste aQ aK))
    (hj : ScalarCompatible jc jc' (scalarPaste aJ aK) aE)
    (hg : ScalarCompatible gc gc' (scalarPaste aQ aS) aL) :
    ScalarCompatible (scalarAlphaPaste Q S J K I P L E π β jc gc)
      (scalarAlphaPaste Q' S' J' K' I' P' L' E' π' β' jc' gc')
      (scalarPaste aI aP) (scalarPaste aL aE) := by
  unfold scalarAlphaPaste
  have hpi := scalarCompatible_projector aS aJ π π' hπ
  have hpiq := scalarCompatible_whiskerLeft aQ hpi
  rw [scalarPaste_refl_right] at hpiq
  have hpiqb := scalarCompatible_whiskerRight aK hpiq
  have hassoc₁ := scalarCompatible_whiskerRight aK
    (scalarCompatible_inv (e := Functor.associator Q S J)
      (e' := Functor.associator Q' S' J') (scalarCompatible_associator aQ aS aJ))
  have hassoc₂ := scalarCompatible_associator (scalarPaste aQ aS) aJ aK
  have hgj := scalarCompatible_whiskerLeft (scalarPaste aQ aS) hj
  have hgk := scalarCompatible_whiskerRight aE hg
  exact scalarCompatible_comp hβ (scalarCompatible_comp hpiqb
    (scalarCompatible_comp hassoc₁ (scalarCompatible_comp hassoc₂
      (scalarCompatible_comp hgj hgk))))

end ScalarCompatibility

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible

private theorem scalar_pull_comp (φ : B →+* Λ) {U V X : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ X) :
    ScalarCompatible (moduleGComp Λ f g).hom (moduleGComp B f g).hom
      (scalarGModule φ (f ≫ g))
      (scalarPaste (scalarGModule φ g) (scalarGModule φ f)) := by
  apply scalarCompatible_of_inverse
  intro M
  have hh := FiniteOpenScalars.pullRes_comp φ f g M
  simpa only [scalarPaste_inv, scalarGModule_eq, Iso.symm_inv,
    moduleRes_eq, Functor.comp_obj, Category.assoc] using hh.symm

private theorem scalarJComp_conjugate (A : Type (u + 1)) [CommRing A]
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv ((moduleJAdj A j).comp (moduleJAdj A k))
        (moduleJAdj A (j ≫ k)) (openBetaModuleJComp A j k).inv =
      (moduleGComp A j k).inv :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

section ScalarEquality

attribute [local irreducible] scalarJModule singleJCongr

end ScalarEquality

end ScalarCalculations

section ScalarAlphaCalculations

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible
attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback
attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars
attribute [local irreducible] scalarGModule scalarJModule

private def scalarLiftAlpha (A : Type (u + 1)) [CommRing A]
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p) (hb : s ≫ b = k) (hq : s ≫ q = f) :
    moduleJ A i ⋙ modulePullback A p ⟶ modulePullback A f ⋙ moduleJ A k :=
  scalarAlphaPaste (modulePullback A q) (modulePullback A s)
    (moduleJ A s) (moduleJ A b) (moduleJ A i) (modulePullback A p)
    (modulePullback A f) (moduleJ A k) (clopenModulePi A s)
    (openBetaModule A q b i p hpb sq).hom
    ((openBetaModuleJComp A s b).hom ≫ (singleJCongr A hb).hom)
    ((moduleGComp A s q).inv ≫ (eqToIso (congrArg (modulePullback A) hq)).hom)

private theorem scalarLiftAlpha_eq (A : Type (u + 1)) [CommRing A]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i) :
    scalarLiftAlpha A (pullback.snd p i) (pullback.fst p i)
        (squareLift k f p i h) k f p i (pullback.condition.symm)
        (IsPullback.of_hasPullback p i).flip (pullback.lift_fst k f h)
        (pullback.lift_snd k f h) = singleAlpha A k f p i h := by
  unfold scalarLiftAlpha scalarAlphaPaste singleAlpha
  rfl

end ScalarAlphaCalculations

end AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars
