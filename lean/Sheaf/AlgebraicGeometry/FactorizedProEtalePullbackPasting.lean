/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pasting constant-coefficient pro-etale pullback squares

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
`lemma-derived-pullback-composition`; the two-square deduction in the node
(blueprint: lem-pur-factorized-pullback-square-pasting).

## Main statements

- `proEtaleFactorizedPullback_pasting`: equality of the two canonical derived paths.
- `proEtaleFactorizedPullback_pasting_representatives`: their termwise normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategory

/-- The ordinary compositor with the published unit-section normalization.
The unit-section equation in the cited theorem determines its maps: the adjunction
identifies a map out of pullback with its composite with the unit. Thus this choice
selects the canonical isomorphism, rather than an unspecified witness of existence.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryComposition
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h ≅
      proEtaleConstantRingPullback A (h ≫ k) :=
  (Classical.choose (proEtaleConstantRingPullbackComposition_ordinary h k A)).symm

/-- The ordinary square comparison, with the specified equality transport.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinarySquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A vY ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙ proEtaleConstantRingPullback A vX :=
  proEtalePastingOrdinaryComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingPullback A) e) ≪≫
      (proEtalePastingOrdinaryComposition vX u A).symm

/-- The left ordinary path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryLeft
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (rY ≫ sY) ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙
        (proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX) :=
  Functor.isoWhiskerRight (proEtalePastingOrdinaryComposition rY sY A).symm
      (proEtaleConstantRingPullback A u) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingPullback A sY) 
      (proEtalePastingOrdinarySquare u rX rY er A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (proEtalePastingOrdinarySquare u sX sY es A)
      (proEtaleConstantRingPullback A rX) ≪≫
    Functor.associator _ _ _

/-- The right ordinary path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryRight
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (rY ≫ sY) ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙
        (proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX) :=
  proEtalePastingOrdinarySquare u (rX ≫ sX) (rY ≫ sY) et A ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingPullback A u) 
      (proEtalePastingOrdinaryComposition rX sX A).symm

/-- The derived square comparison, with the specified equality transport.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedSquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A vY ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙ proEtaleConstantRingDerivedPullback A vX :=
  proEtaleConstantRingPullbackComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e) ≪≫
      (proEtaleConstantRingPullbackComposition vX u A).symm

/-- The left derived path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedLeft
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A (rY ≫ sY) ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙
        (proEtaleConstantRingDerivedPullback A sX ⋙ proEtaleConstantRingDerivedPullback A rX) :=
  Functor.isoWhiskerRight (proEtaleConstantRingPullbackComposition rY sY A).symm
      (proEtaleConstantRingDerivedPullback A u) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A sY) 
      (proEtalePastingDerivedSquare u rX rY er A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (proEtalePastingDerivedSquare u sX sY es A)
      (proEtaleConstantRingDerivedPullback A rX) ≪≫
    Functor.associator _ _ _

/-- The right derived path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedRight
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A (rY ≫ sY) ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙
        (proEtaleConstantRingDerivedPullback A sX ⋙ proEtaleConstantRingDerivedPullback A rX) :=
  proEtalePastingDerivedSquare u (rX ≫ sX) (rY ≫ sY) et A ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u) 
      (proEtaleConstantRingPullbackComposition rX sX A).symm

section Transport

universe v₀ v₁ v₂ v₃
variable {S : Type v₀} [Category.{v₁} S] (D : S → Type v₂) [∀ X, Category.{v₃} (D X)]
  (P : ∀ {X Y : S}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : S} (h : Z ⟶ Y) (k : Y ⟶ X), P k ⋙ P h ≅ P (h ≫ k))

private def transportedExpansion
    {X Y Z : S} (h : Z ⟶ Y) (k : Y ⟶ X) (f : Z ⟶ X) (e : f = h ≫ k) :
    P f ≅ P k ⋙ P h :=
  eqToIso (congrArg P e) ≪≫ (c h k).symm

private theorem transportedExpansion_coherence
    {X Y Z W : S} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (jh : W ⟶ Y) (hk : Z ⟶ X) (t : W ⟶ X)
    (ejh : jh = j ≫ h) (ehk : hk = h ≫ k)
    (et : t = j ≫ hk) (et' : t = jh ≫ k) (M : D X)
    (hc : (c j (h ≫ k)).inv.app M ≫ (P j).map ((c h k).inv.app M) =
      (eqToIso (congrArg P (Category.assoc j h k).symm)).hom.app M ≫
        (c (j ≫ h) k).inv.app M ≫ (c j h).inv.app ((P k).obj M)) :
    (transportedExpansion D P c j hk t et).hom.app M ≫
        (P j).map ((transportedExpansion D P c h k hk ehk).hom.app M) =
      (transportedExpansion D P c jh k t et').hom.app M ≫
        (transportedExpansion D P c j h jh ejh).hom.app ((P k).obj M) := by
  subst jh
  subst hk
  cases et
  simpa only [transportedExpansion, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.assoc] using hc

private theorem transportedExpansion_refl
    {X Y Z : S} (h : Z ⟶ Y) (k : Y ⟶ X) :
    transportedExpansion D P c h k (h ≫ k) rfl = (c h k).symm := by
  simp only [transportedExpansion, eqToIso_refl, Iso.refl_trans]

private def genericSquare
    {X Y : S} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) : P vY ⋙ P u ≅ P u ⋙ P vX :=
  c u vY ≪≫ eqToIso (congrArg P e) ≪≫ (c vX u).symm

private theorem genericSquare_expansion
    {X Y : S} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (f : X ⟶ Y)
    (ef : f = u ≫ vY) (ef' : f = vX ≫ u) :
    genericSquare D P c u vX vY e =
      (transportedExpansion D P c u vY f ef).symm ≪≫
        transportedExpansion D P c vX u f ef' := by
  subst f
  apply Iso.ext
  simp only [transportedExpansion, genericSquare, eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, eqToIso.hom]

private theorem generic_pasting
    {X Y : S} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (hc₁ : ∀ M : D Y, (c u (rY ≫ sY)).inv.app M ≫ (P u).map ((c rY sY).inv.app M) =
      (eqToIso (congrArg P (Category.assoc u rY sY).symm)).hom.app M ≫
        (c (u ≫ rY) sY).inv.app M ≫ (c u rY).inv.app ((P sY).obj M))
    (hc₂ : ∀ M : D Y, (c rX (u ≫ sY)).inv.app M ≫ (P rX).map ((c u sY).inv.app M) =
      (eqToIso (congrArg P (Category.assoc rX u sY).symm)).hom.app M ≫
        (c (rX ≫ u) sY).inv.app M ≫ (c rX u).inv.app ((P sY).obj M))
    (hc₃ : ∀ M : D Y, (c rX (sX ≫ u)).inv.app M ≫ (P rX).map ((c sX u).inv.app M) =
      (eqToIso (congrArg P (Category.assoc rX sX u).symm)).hom.app M ≫
        (c (rX ≫ sX) u).inv.app M ≫ (c rX sX).inv.app ((P u).obj M)) :
    (Functor.isoWhiskerRight (c rY sY).symm (P u) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (P sY) (genericSquare D P c u rX rY er) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (genericSquare D P c u sX sY es) (P rX) ≪≫
      Functor.associator _ _ _).hom =
    (genericSquare D P c u (rX ≫ sX) (rY ≫ sY) et ≪≫
      Functor.isoWhiskerLeft (P u) (c rX sX).symm).hom := by
  apply NatTrans.ext
  funext M
  let t := u ≫ (rY ≫ sY)
  have e₁ : t = (rX ≫ u) ≫ sY := by
    dsimp [t]
    rw [← er, Category.assoc]
  have e₂ : t = rX ≫ (sX ≫ u) := by
    rw [e₁, Category.assoc, ← es]
  have h₁ := transportedExpansion_coherence D P c u rY sY
    (rX ≫ u) (rY ≫ sY) t er.symm rfl rfl e₁ M (hc₁ M)
  have h₂ := transportedExpansion_coherence D P c rX u sY
    (rX ≫ u) (sX ≫ u) t rfl es.symm e₂ e₁ M (hc₂ M)
  have h₃ := transportedExpansion_coherence D P c rX sX u
    (rX ≫ sX) (sX ≫ u) t rfl rfl e₂ et M (hc₃ M)
  rw [← cancel_epi ((transportedExpansion D P c u (rY ≫ sY) t rfl).hom.app M)]
  simp only [genericSquare_expansion D P c u rX rY er (rX ≫ u) er.symm rfl,
    genericSquare_expansion D P c u sX sY es (sX ≫ u) es.symm rfl,
    genericSquare_expansion D P c u (rX ≫ sX) (rY ≫ sY) et t rfl et,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc]
  simp only [transportedExpansion_refl, Iso.symm_hom] at h₁ h₂ h₃ ⊢
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₁, Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact h₃

end Transport

/-- Pasting the two canonical commuting-square comparisons agrees with the
comparison of their composite endomorphisms, as natural transformations.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting).
Proof: (1) The constant-ring-map and constant-coefficient-composition nodes identify
all coefficient maps with the specified constant-section maps, including composites.
(2) Equality elimination gives substitution for each index of the canonical compositor;
composite, inverse and whiskered equality transports are therefore the expected ones.
Proof irrelevance identifies any supplied outer-square equality with the pasted equality.
(3) Apply lem-trf-derived-pullback-coherence to (u,rY,sY). Expand C_r and cancel the
adjacent inverse compositors, transporting along er. The left path becomes
(P_rX C_s)(c_rX,u P_sY)c_urX,sY c_u,tY^{-1}.
(4) Apply coherence to (rX,u,sY), expand C_s and cancel its inverse compositor.
Transport along es to obtain (P_rX c_sX,u)c_rX,usX c_u,tY^{-1}.
(5) Apply coherence to (rX,sX,u). This is (d_X P_u) C_t, with the outer transport
from step (2). The associators only reassociate the three evaluated functors.
Extensionality in the derived object gives equality of natural transformations. -/
theorem proEtaleFactorizedPullback_pasting
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] [Finite A] :
    (proEtalePastingDerivedLeft u rX sX rY sY er es A).hom =
      (proEtalePastingDerivedRight u rX sX rY sY et A).hom := by
  exact generic_pasting (fun T ↦ proEtaleDerivedCategory T A)
    (proEtaleConstantRingDerivedPullback A)
    (fun h k ↦ proEtaleConstantRingPullbackComposition h k A)
    u rX sX rY sY er es et
    (fun M ↦ proEtaleConstantRingDerivedPullback_composition_coherence u rY sY A M)
    (fun M ↦ proEtaleConstantRingDerivedPullback_composition_coherence rX u sY A M)
    (fun M ↦ proEtaleConstantRingDerivedPullback_composition_coherence rX sX u A M)

private theorem composition_localization
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullbackComposition h k A =
      (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A k)
        (proEtaleConstantRingPullback A h)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (proEtalePastingOrdinaryComposition h k A) := by
  let a := Classical.choose (proEtaleConstantRingPullbackComposition_ordinary h k A)
  have ha := (Classical.choose_spec
    (proEtaleConstantRingPullbackComposition_ordinary h k A)).2
  have hs : Functor.mapDerivedCategoryNatIso (proEtalePastingOrdinaryComposition h k A) =
      (Functor.mapDerivedCategoryNatIso a).symm := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_symm a
  apply Iso.ext_inv
  rw [Iso.trans_inv, Iso.symm_inv, hs, Iso.symm_inv]
  exact (congrArg Iso.hom ha).symm

private theorem localized_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (proEtaleConstantRingPullback A) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

section Localization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
  [Abelian C] [Abelian D] [Abelian E] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory B]

private theorem localized_right
    {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (e : F ≅ F') (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom G.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso F' G).inv := by
  rw [← cancel_mono (Functor.mapDerivedCategoryCompIso F' G).hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G

private theorem localized_left
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G G' : D ⥤ E} [G.Additive] [G'.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e)).hom =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryCompIso F G').inv := by
  rw [← cancel_mono (Functor.mapDerivedCategoryCompIso F G').hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e

omit [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem localized_associator
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    Functor.mapDerivedCategoryNatIso (Functor.associator F G H) = Iso.refl _ := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem associator_hom_id
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) :
    (Functor.associator F G H).hom = 𝟙 _ := rfl

private theorem associator_inv_id
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) :
    (Functor.associator F G H).inv = 𝟙 _ := rfl

private theorem compositor_bridge
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).symm ≪≫
        Functor.mapDerivedCategoryCompIso F (G ⋙ H) =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso F G) H.mapDerivedCategory ≪≫
        (Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H)).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Functor.mapDerivedCategoryCompIso_assoc F G H]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp,
    Iso.hom_inv_id, Functor.whiskerLeft_id', Category.comp_id]

private theorem left_localization_general
    (U : C ⥤ D) (RY SY TY : C ⥤ C) (RX SX : D ⥤ D)
    [U.Additive] [RY.Additive] [SY.Additive] [TY.Additive] [RX.Additive] [SX.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
    [PreservesFiniteLimits SY] [PreservesFiniteColimits SY]
    [PreservesFiniteLimits TY] [PreservesFiniteColimits TY]
    [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
    [PreservesFiniteLimits SX] [PreservesFiniteColimits SX]
    (aY : TY ≅ SY ⋙ RY) (ar : RY ⋙ U ≅ U ⋙ RX) (aS : SY ⋙ U ≅ U ⋙ SX) :
    (Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso aY ≪≫ Functor.mapDerivedCategoryCompIso SY RY)
        U.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft SY.mapDerivedCategory (Functor.mapDerivedCategorySquareIso ar) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso aS) RX.mapDerivedCategory ≪≫
      Functor.associator _ _ _).hom =
    (Functor.mapDerivedCategorySquareIso
        (Functor.isoWhiskerRight aY U ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft SY ar ≪≫ (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight aS RX ≪≫ Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft U.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso SX RX)).hom := by
  have h₁ := congrArg Iso.hom (compositor_bridge SY RY U)
  have h₂ := congrArg Iso.inv (compositor_bridge SY U RX)
  have h₃ := Functor.mapDerivedCategoryCompIso_assoc U SX RX
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv] at h₁ h₂
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, localized_associator, localized_left, localized_right,
    Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    associator_hom_id, associator_inv_id, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h₃, Iso.inv_hom_id_assoc]
  erw [Category.id_comp]
  rw [reassoc_of% h₂, reassoc_of% h₁]
  simp only [Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]

end Localization

private theorem square_localization
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtalePastingDerivedSquare u vX vY e A =
      Functor.mapDerivedCategorySquareIso (proEtalePastingOrdinarySquare u vX vY e A) := by
  apply Iso.ext
  simp only [proEtalePastingDerivedSquare, proEtalePastingOrdinarySquare,
    composition_localization, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [localized_transport e A]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem right_localization
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u) (A : Type u) [CommRing A] :
    (proEtalePastingDerivedRight u rX sX rY sY et A).hom =
      (Functor.mapDerivedCategorySquareIso
        (proEtalePastingOrdinaryRight u rX sX rY sY et A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom := by
  simp only [proEtalePastingDerivedRight, proEtalePastingOrdinaryRight,
    square_localization, composition_localization, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, localized_left,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]

private theorem left_localization
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (A : Type u) [CommRing A] :
    (proEtalePastingDerivedLeft u rX sX rY sY er es A).hom =
      (Functor.mapDerivedCategorySquareIso
        (proEtalePastingOrdinaryLeft u rX sX rY sY er es A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom := by
  simp only [proEtalePastingDerivedLeft, proEtalePastingOrdinaryLeft,
    square_localization, composition_localization]
  have h := left_localization_general (proEtaleConstantRingPullback A u)
    (proEtaleConstantRingPullback A rY) (proEtaleConstantRingPullback A sY)
    (proEtaleConstantRingPullback A (rY ≫ sY))
    (proEtaleConstantRingPullback A rX) (proEtaleConstantRingPullback A sX)
    (proEtalePastingOrdinaryComposition rY sY A).symm
    (proEtalePastingOrdinarySquare u rX rY er A)
    (proEtalePastingOrdinarySquare u sX sY es A)
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_comp,
    Functor.mapDerivedCategoryNatIso_symm] using h

/-- On a K-flat complex with flat terms, each path is the class of its termwise
ordinary pasting map. `mapDerivedCategorySquareIso` is the canonical localization
of the termwise map, with source and target composition factorization isomorphisms;
the final whiskered comparison expands the target into its three pullback functors.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting).
Proof: (6) Apply lem-weil-pbc-ringed-pullback-preserves-kflat repeatedly: all successive
ordinary pullbacks of K remain K-flat with flat terms. The normalized compositor in
lem-weil-pbc-proetale-derived-pullback-composition is the localization of its ordinary
termwise map; the published ordinary comparison has exactly its unit normalization.
Localization preserves inverses, so inverse compositors have the inverse termwise maps.
Exact termwise descent in def-weil-pbc-proetale-operations identifies whiskering with
ordinary pullback of those maps. Equality elimination identifies all equality transports
with the termwise transports, starting with identity maps in the reflexive case.
Compose these identities for each path, including the canonical associators. This gives
the two component formulas below. No boundedness assumption on K is needed. -/
theorem proEtaleFactorizedPullback_pasting_representatives
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] [Finite A]
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (hK : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt)
      (ProEt.topology Y) (proEtaleConstantRing Y A) K)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Y.ProEt) (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (K.X n)) :
    (proEtalePastingDerivedLeft u rX sX rY sY er es A).hom.app
        (DerivedCategory.Q.obj K) =
      (Functor.mapDerivedCategorySquareIso
          (F₁ := proEtaleConstantRingPullback A (rY ≫ sY))
          (F₂ := proEtaleConstantRingPullback A u)
          (G₁ := proEtaleConstantRingPullback A u)
          (G₂ := proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX)
          (proEtalePastingOrdinaryLeft u rX sX rY sY er es A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom.app (DerivedCategory.Q.obj K) ∧
    (proEtalePastingDerivedRight u rX sX rY sY et A).hom.app
        (DerivedCategory.Q.obj K) =
      (Functor.mapDerivedCategorySquareIso
          (F₁ := proEtaleConstantRingPullback A (rY ≫ sY))
          (F₂ := proEtaleConstantRingPullback A u)
          (G₁ := proEtaleConstantRingPullback A u)
          (G₂ := proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX)
          (proEtalePastingOrdinaryRight u rX sX rY sY et A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom.app (DerivedCategory.Q.obj K) := by
  have _ := hK
  have _ := hflat
  exact ⟨NatTrans.congr_app (left_localization u rX sX rY sY er es A)
    (DerivedCategory.Q.obj K), NatTrans.congr_app (right_localization u rX sX rY sY et A)
    (DerivedCategory.Q.obj K)⟩

end AlgebraicGeometry.Scheme
