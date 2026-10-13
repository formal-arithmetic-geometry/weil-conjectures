/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
import Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Open pullback squares and restricted counits

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-t2-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical pullback comparison across a commuting square of open inclusions.
Source: Stacks Project, Tag 0D5S, applied to the constructed open pullback comparisons.
(blueprint: def-pc-t2-open-pullback-square-iso). -/
noncomputable def singleComplexOpenPullbackSquareIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (s : X ⟶ Y) (U : Y.Opens) (U' : X.Opens)
    (j : U'.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = U'.ι ≫ s) :
    (schemeOpenRestriction Y U).mapDerivedCategory ⋙ derivedPullback j ≅
      derivedPullback s ⋙ (schemeOpenRestriction X U').mapDerivedCategory := by
  classical
  let c := @singleComplexOpenPinnedComposition.{u, w} _
  let d := Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y U).symm
      (derivedPullback j) ≪≫
    c j U.ι ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) hj) ≪≫
      (c U'.ι s).symm ≪≫
        Functor.isoWhiskerLeft (derivedPullback s) (singleComplexOpenPullbackIso X U')
  refine NatIso.ofComponents (fun M ↦
    (derivedPullback j).mapIso ((singleComplexOpenPullbackIso Y U).symm.app M) ≪≫
      (c j U.ι).app M ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj M) hj) ≪≫
      (c U'.ι s).symm.app M ≪≫
      (singleComplexOpenPullbackIso X U').app ((derivedPullback s).obj M)) ?_
  intro M N v
  simpa only [d, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.app_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.mapIso_hom,
    eqToIso.hom, eqToHom_app, Category.assoc] using d.hom.naturality v

private theorem counit_factorization
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₁} {L : D₁ ⥤ D₂} {R : D₂ ⥤ D₁}
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (b : G ⊣ H) (a : L ⊣ R)
    (ε : Q₁ ⋙ L ⟶ G ⋙ Q₂) (η : H ⋙ Q₁ ⟶ Q₂ ⋙ R)
    (h : ∀ (M : C₁) (K : C₂) (v : G.obj M ⟶ K),
      a.homEquiv (Q₁.obj M) (Q₂.obj K) (ε.app M ≫ Q₂.map v) =
        Q₁.map (b.homEquiv M K v) ≫ η.app K) (I : C₂) :
    L.map (η.app I) ≫ a.counit.app (Q₂.obj I) =
      ε.app (H.obj I) ≫ Q₂.map (b.counit.app I) := by
  apply (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).injective
  have h₁ := (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).apply_symm_apply (η.app I)
  have h₂ := (b.homEquiv (H.obj I) I).apply_symm_apply (𝟙 (H.obj I))
  simp only [a.homEquiv_counit] at h₁
  simp only [b.homEquiv_symm_id] at h₂
  rw [h₁, h, h₂, Q₁.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Elaborating the pinned derived functor data requires additional heartbeats.
private theorem pinned_counit_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) f
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback f).map (F.rightDerivedFunctorUnit.app I) ≫
        (a f).counit.app (DerivedCategory.Qh.obj I) =
      (ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
            |>.mapHomotopyCategory (.up ℤ)).counit.app I) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : (Scheme.Modules.tensorPullback f).Additive :=
    (Classical.choose exists_derivedPullbackComposition) f
  exact counit_factorization
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      |>.mapHomotopyCategory (.up ℤ))
    (singleComplexOpenPinnedAdjunction f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
    (Classical.choose_spec (exists_schemeDerivedAdjunction f
      (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f))) I

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- The representative calculation elaborates several derived functor comparisons.
/-- The sectionwise direct-image comparison is the mate of the open pullback square.
Source: Stacks Project, cohomology.tex, Tags 08FE, 08BS and 08HY.
(blueprint: lem-pc-t2-open-counit-compatibility).

Proof: Compute direct image on a K-injective complex. Open restriction preserves
K-injectivity, since exact extension by zero is its left adjoint. The underived
comparison used in singleComplexOpenDirectImageIso is the sectionwise identity
on inverse-image opens. Under the tensor-pullback adjunction its mate is the
open pullback comparison: both counit composites evaluate the same restricted
tensor on sections. Derive this equality using the right-derived factorization
identities and the left-derived counits defining the composition comparisons.
The Hom equivalences of the chosen adjunctions are pinned to these same counits
and right-derived units by exists_schemeDerivedAdjunction. Thus the equality on
representatives descends to the displayed equality in the derived category.
This is an identity of natural transformations, including empty opens and zero
objects; no boundedness assumption is used. -/
theorem singleComplexOpen_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (K : schemeDerivedCategory X) :
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let RX := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory
    (derivedPullback (f ∣_ V)).map ((singleComplexOpenDirectImageIso f V).hom.app K) ≫
        (a (f ∣_ V)).counit.app (RX.obj K) =
      (singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).hom.app ((schemeDerivedDirectImage f).obj K) ≫
          RX.map ((a f).counit.app K) := by
  classical
  let a := @singleComplexOpenPinnedAdjunction.{u, w} _
  let RX := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory
  let RY := (schemeOpenRestriction Y V).mapDerivedCategory
  let L₀ := derivedPullback (f ∣_ V)
  let F := schemeDerivedDirectImage f
  let P := F ⋙ RY ⋙ L₀
  let α : P ⟶ RX :=
    Functor.whiskerRight (singleComplexOpenDirectImageIso f V).hom L₀ ≫
      Functor.whiskerLeft RX (a (f ∣_ V)).counit
  let β : P ⟶ RX :=
    Functor.whiskerLeft F
        (singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
          (morphismRestrict_ι f V)).hom ≫
      Functor.whiskerRight (a f).counit RX
  have hrep (I : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) [I.IsKInjective] :
      α.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
        β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) := by
    let J := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let t := rY.mapDerivedCategoryFactorsh.inv.app
        ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
      RY.map (G.rightDerivedFunctorUnit.app J)
    have : IsIso (G.rightDerivedFunctorUnit.app J) := inferInstance
    have : IsIso t := inferInstance
    rw [← cancel_epi (L₀.map t)]
    change L₀.map t ≫ (L₀.map ((singleComplexOpenDirectImageIso f V).hom.app _) ≫
        (a (f ∣_ V)).counit.app _) = _
    rw [← L₀.map_comp_assoc]
    have hu := singleComplexOpen_directImage_unit f V J
    dsimp only at hu
    have hu' := hu
    rw [← Category.assoc] at hu' 
    rw [hu', L₀.map_comp, L₀.map_comp]
    simp only [Category.assoc]
    erw [(a (f ∣_ V)).counit.naturality (rX.mapDerivedCategoryFactorsh.inv.app J)]
    simp only [Functor.id_map]
    erw [reassoc_of% (pinned_counit_unit (f ∣_ V)
      ((rX.mapHomotopyCategory (.up ℤ)).obj J))]
    have hp := singleComplexOpen_pullback_counit_representative f V J
    simpa only [singleComplexOpenPullbackSquareIso, β, t, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
      Category.assoc] using hp.symm
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have he : K ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) :=
    e ≪≫ (DerivedCategory.quotientCompQhIso _).app I
  change α.app K = β.app K
  rw [← cancel_mono (RX.map he.hom), ← α.naturality, ← β.naturality, hrep I]


end AlgebraicGeometry
