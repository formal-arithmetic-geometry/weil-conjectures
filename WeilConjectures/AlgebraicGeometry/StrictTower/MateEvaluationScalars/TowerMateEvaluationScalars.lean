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

private def ScalarCompatible (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G') : Prop :=
  ∀ M, u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M)

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

end ScalarCompatibility

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible

section ScalarEquality

attribute [local irreducible] scalarJModule singleJCongr

end ScalarEquality

end ScalarCalculations

section ScalarAlphaCalculations

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible
attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback
attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars
attribute [local irreducible] scalarGModule scalarJModule

end ScalarAlphaCalculations

end AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars
