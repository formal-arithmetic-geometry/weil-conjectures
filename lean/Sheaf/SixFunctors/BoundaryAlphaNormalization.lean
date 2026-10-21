/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.HomCongr
public import Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive

/-!
# Evaluation-normalized boundary alpha on the ordinary etale derived categories

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md, second paragraph,
and the node's expanded proof steps 1--6
(blueprint: lem-weil-boundary-alpha-normalization).

Every map below is built from the recorded etale functors. The Hom-chain equivalence
is constructed from adjunctions and the canonical projection map independently of alpha.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/-- The independent chain of adjunction and signed-symmetry bijections.
Source: expanded steps 1--3 (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def CategoryTheory.boundaryHomChain
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : ∀ U V, (P.obj U).obj V ≅ (P.obj V).obj U)
    (sD : ∀ U V, (Q.obj U).obj V ≅ (Q.obj V).obj U)
    (L : D ⥤ C) (W K : D) (B : C)
    (pi : (Q.obj (F.obj B)).obj K ≅ F.obj ((P.obj B).obj (L.obj K))) :
    (B ⟶ G.obj ((H.obj (op K)).obj W)) ≃
      (B ⟶ (J.obj (op (L.obj K))).obj (G.obj W)) :=
  (adj.homEquiv B ((H.obj (op K)).obj W)).symm |>.trans
    ((aD.adj K).homEquiv (F.obj B) W).symm |>.trans
    (Iso.homCongr (sD K (F.obj B)) (Iso.refl W)) |>.trans
    (Iso.homCongr pi (Iso.refl W)) |>.trans
    (adj.homEquiv ((P.obj B).obj (L.obj K)) W) |>.trans
    (Iso.homCongr (sC B (L.obj K)) (Iso.refl (G.obj W))) |>.trans
    ((aC.adj (L.obj K)).homEquiv B (G.obj W))

private theorem homChain_natural
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : ∀ U V, (P.obj U).obj V ≅ (P.obj V).obj U)
    (sD : ∀ U V, (Q.obj U).obj V ≅ (Q.obj V).obj U)
    (L : D ⥤ C) (W K : D) (B B' : C)
    (pi : (Q.obj (F.obj B)).obj K ≅ F.obj ((P.obj B).obj (L.obj K)))
    (pi' : (Q.obj (F.obj B')).obj K ≅ F.obj ((P.obj B').obj (L.obj K)))
    (b : B ⟶ B')
    (hp : (Q.map (F.map b)).app K ≫ pi'.hom =
      pi.hom ≫ F.map ((P.map b).app (L.obj K)))
    (hD : (Q.map (F.map b)).app K ≫ (sD K (F.obj B')).inv =
      (sD K (F.obj B)).inv ≫ (Q.obj K).map (F.map b))
    (hC : (P.obj (L.obj K)).map b ≫ (sC B' (L.obj K)).inv =
      (sC B (L.obj K)).inv ≫ (P.map b).app (L.obj K))
    (c : B' ⟶ G.obj ((H.obj (op K)).obj W)) :
    boundaryHomChain F G adj P Q H J aD aC sC sD L W K B pi (b ≫ c) =
      b ≫ boundaryHomChain F G adj P Q H J aD aC sC sD L W K B' pi' c := by
  have hp' : pi.inv ≫ (Q.map (F.map b)).app K =
      F.map ((P.map b).app (L.obj K)) ≫ pi'.inv := by
    apply (cancel_mono pi'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hp, pi.inv_hom_id_assoc]
  simp only [boundaryHomChain, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Adjunction.homEquiv_naturality_left_symm]
  rw [← reassoc_of% hD, reassoc_of% hp']
  rw [adj.homEquiv_naturality_left]
  rw [← reassoc_of% hC]
  exact (aC.adj (L.obj K)).homEquiv_naturality_left b _

/-- The evaluation-normalized comparison, expanded before specialization.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def CategoryTheory.boundaryNormalizationMap
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : ∀ U V, (P.obj U).obj V ≅ (P.obj V).obj U)
    (sD : ∀ U V, (Q.obj U).obj V ≅ (Q.obj V).obj U)
    (L : D ⥤ C) (W K : D)
    (pi : (Q.obj (F.obj (G.obj ((H.obj (op K)).obj W)))).obj K ≅
      F.obj ((P.obj (G.obj ((H.obj (op K)).obj W))).obj (L.obj K))) :
    (G.obj ((H.obj (op K)).obj W) ⟶
      (J.obj (op (L.obj K))).obj (G.obj W)) :=
      (aC.adj (L.obj K)).homEquiv (G.obj ((H.obj (op K)).obj W)) (G.obj W)
        ((sC (L.obj K) _).hom ≫ (sC _ (L.obj K)).hom ≫
          adj.homEquiv ((P.obj (L.obj K)).obj (G.obj ((H.obj (op K)).obj W)))
            ((Q.obj K).obj ((H.obj (op K)).obj W))
            (F.map ((sC (L.obj K) _).hom) ≫ pi.inv ≫
              (sD _ K).hom ≫
                (Q.obj K).map (adj.counit.app ((H.obj (op K)).obj W))) ≫
          G.map ((sD K _).hom ≫ (sD _ K).hom ≫
            (aD.adj K).counit.app W))

private theorem homChain_identity
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : ∀ U V, (P.obj U).obj V ≅ (P.obj V).obj U)
    (sD : ∀ U V, (Q.obj U).obj V ≅ (Q.obj V).obj U)
    (hc : ∀ U V, (sC U V).hom ≫ (sC V U).hom = 𝟙 _)
    (hd : ∀ U V, (sD U V).hom ≫ (sD V U).hom = 𝟙 _)
    (L : D ⥤ C) (W K : D)
    (pi : (Q.obj (F.obj (G.obj ((H.obj (op K)).obj W)))).obj K ≅
      F.obj ((P.obj (G.obj ((H.obj (op K)).obj W))).obj (L.obj K))) :
    boundaryHomChain F G adj P Q H J aD aC sC sD L W K _ pi (𝟙 _) =
      boundaryNormalizationMap F G adj P Q H J aD aC sC sD L W K pi := by
  unfold boundaryNormalizationMap
  have hci (U V : C) : (sC U V).inv = (sC V U).hom := by
    apply (cancel_mono (sC U V).hom).mp
    rw [Iso.inv_hom_id]
    exact (hc V U).symm
  have hdi (U V : D) : (sD U V).inv = (sD V U).hom := by
    apply (cancel_mono (sD U V).hom).mp
    rw [Iso.inv_hom_id]
    exact (hd V U).symm
  simp only [boundaryHomChain, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Adjunction.homEquiv_symm_id, hci, hdi,
    reassoc_of% (hc _ _), reassoc_of% (hd _ _)]
  apply congrArg ((aC.adj (L.obj K)).homEquiv (G.obj ((H.obj (op K)).obj W)) (G.obj W))
  erw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_symm_apply, Category.assoc]

private theorem homChain_parameter
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : ∀ U V, (P.obj U).obj V ≅ (P.obj V).obj U)
    (sD : ∀ U V, (Q.obj U).obj V ≅ (Q.obj V).obj U)
    (L : D ⥤ C) (W K K' : D) (B : C)
    (pi : (Q.obj (F.obj B)).obj K ≅ F.obj ((P.obj B).obj (L.obj K)))
    (pi' : (Q.obj (F.obj B)).obj K' ≅ F.obj ((P.obj B).obj (L.obj K')))
    (u : K ⟶ K') (v : L.obj K ⟶ L.obj K')
    (hp : (Q.obj (F.obj B)).map u ≫ pi'.hom =
      pi.hom ≫ F.map ((P.obj B).map (v)))
    (hD : (Q.obj (F.obj B)).map u ≫ (sD K' (F.obj B)).inv =
      (sD K (F.obj B)).inv ≫ (Q.map u).app (F.obj B))
    (hC : (P.map (v)).app B ≫ (sC B (L.obj K')).inv =
      (sC B (L.obj K)).inv ≫ (P.obj B).map (v))
    (b : B ⟶ G.obj ((H.obj (op K')).obj W)) :
    boundaryHomChain F G adj P Q H J aD aC sC sD L W K B pi
        (b ≫ G.map ((H.map u.op).app W)) =
      boundaryHomChain F G adj P Q H J aD aC sC sD L W K' B pi' b ≫
        (J.map (v).op).app (G.obj W) := by
  have hp' : pi.inv ≫ (Q.obj (F.obj B)).map u =
      F.map ((P.obj B).map (v)) ≫ pi'.inv := by
    apply (cancel_mono pi'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hp, pi.inv_hom_id_assoc]
  simp only [boundaryHomChain, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Adjunction.homEquiv_naturality_right_symm]
  erw [← aC.homEquiv_naturality_one (v)]
  apply congrArg ((aC.adj (L.obj K)).homEquiv B (G.obj W))
  erw [aD.homEquiv_symm_naturality_one u]
  rw [← reassoc_of% hD, reassoc_of% hp', adj.homEquiv_naturality_left,
    ← reassoc_of% hC]
  rfl

private theorem swap_inv_left {C : Type*} [Category C] {P : C ⥤ C ⥤ C}
    (s : P ≅ P.flip) {B B' : C} (b : B ⟶ B') (V : C) :
    (P.obj V).map b ≫ ((s.app B').app V).inv =
      ((s.app B).app V).inv ≫ (P.map b).app V := by
  exact NatTrans.congr_app (s.inv.naturality b) V

private theorem swap_inv_right {C : Type*} [Category C] {P : C ⥤ C ⥤ C}
    (s : P ≅ P.flip) (B : C) {V V' : C} (v : V ⟶ V') :
    (P.map v).app B ≫ ((s.app B).app V').inv =
      ((s.app B).app V).inv ≫ (P.obj B).map v := by
  exact (s.inv.app B).naturality v

private theorem iso_of_homEquivs {C : Type*} [Category C] {X Y : C}
    (a : X ⟶ Y) (eX : (X ⟶ X) ≃ (X ⟶ Y)) (eY : (Y ⟶ X) ≃ (Y ⟶ Y))
    (hX : ∀ b, eX b = b ≫ a) (hY : ∀ b, eY b = b ≫ a) : IsIso a := by
  let g : Y ⟶ X := eY.symm (𝟙 Y)
  have hga : g ≫ a = 𝟙 Y := by
    rw [← hY g]
    exact eY.apply_symm_apply _
  have hag : a ≫ g = 𝟙 X := by
    apply eX.injective
    rw [hX, hX, Category.assoc, hga, Category.comp_id, Category.id_comp]
  exact ⟨⟨g, hag, hga⟩⟩

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- The canonical functor data of the boundary Hom calculation, including its categories.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
structure BoundaryData (C : Type u₁) (D : Type u₂)
    [Category.{v₁} C] [Category.{v₂} D] where
  F : C ⥤ D
  G : D ⥤ C
  adj : F ⊣ G
  P : C ⥤ C ⥤ C
  Q : D ⥤ D ⥤ D
  H : Dᵒᵖ ⥤ D ⥤ D
  J : Cᵒᵖ ⥤ C ⥤ C
  aD : Q ⊣₂ H
  aC : P ⊣₂ J
  sC : P ≅ P.flip
  sD : Q ≅ Q.flip
  L : D ⥤ C
  projection : ∀ (B : C) (K : D),
    (Q.obj (F.obj B)).obj K ⟶ F.obj ((P.obj B).obj (L.obj K))
  projection_left : ∀ (B B' : C) (K : D) (b : B ⟶ B'),
    (Q.map (F.map b)).app K ≫ projection B' K =
      projection B K ≫ F.map ((P.map b).app (L.obj K))
  projection_right : ∀ (B : C) (K K' : D) (u : K ⟶ K'),
    (Q.obj (F.obj B)).map u ≫ projection B K' =
      projection B K ≫ F.map ((P.obj B).map (L.map u))
  involutionC : ∀ U V : C,
    ((sC.app U).app V).hom ≫ ((sC.app V).app U).hom = 𝟙 _
  involutionD : ∀ U V : D,
    ((sD.app U).app V).hom ≫ ((sD.app V).app U).hom = 𝟙 _

namespace BoundaryData

/-- Assemble the data before specializing to a derived sheaf category.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
def ofFunctors
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D)
    (H : Dᵒᵖ ⥤ D ⥤ D) (J : Cᵒᵖ ⥤ C ⥤ C)
    (aD : Q ⊣₂ H) (aC : P ⊣₂ J)
    (sC : P ≅ P.flip) (sD : Q ≅ Q.flip) (L : D ⥤ C)
    (projection : ∀ (B : C) (K : D),
      (Q.obj (F.obj B)).obj K ⟶ F.obj ((P.obj B).obj (L.obj K)))
    (hleft : ∀ (B B' : C) (K : D) (b : B ⟶ B'),
      (Q.map (F.map b)).app K ≫ projection B' K =
        projection B K ≫ F.map ((P.map b).app (L.obj K)))
    (hright : ∀ (B : C) (K K' : D) (u : K ⟶ K'),
      (Q.obj (F.obj B)).map u ≫ projection B K' =
        projection B K ≫ F.map ((P.obj B).map (L.map u)))
    (hc : ∀ U V : C, ((sC.app U).app V).hom ≫ ((sC.app V).app U).hom = 𝟙 _)
    (hd : ∀ U V : D, ((sD.app U).app V).hom ≫ ((sD.app V).app U).hom = 𝟙 _) :
    BoundaryData C D where
  F := F
  G := G
  adj := adj
  P := P
  Q := Q
  H := H
  J := J
  aD := aD
  aC := aC
  sC := sC
  sD := sD
  L := L
  projection := projection
  projection_left := hleft
  projection_right := hright
  involutionC := hc
  involutionD := hd

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (d : BoundaryData C D)

/-- The independent chain of seven adjunction and symmetry equivalences.
Source: expanded steps 1--3 (blueprint: lem-weil-boundary-alpha-normalization). -/
def chain (W K : D) (B : C) (hPi : IsIso (d.projection B K)) :
    (B ⟶ d.G.obj ((d.H.obj (op K)).obj W)) ≃
      (B ⟶ (d.J.obj (op (d.L.obj K))).obj (d.G.obj W)) :=
  letI := hPi
  boundaryHomChain d.F d.G d.adj d.P d.Q d.H d.J d.aD d.aC
    (fun U V ↦ (d.sC.app U).app V) (fun U V ↦ (d.sD.app U).app V)
    d.L W K B (asIso (d.projection B K))

/-- The evaluation-normalized comparison from the stored canonical data.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def alpha (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K)) :
    d.G.obj ((d.H.obj (op K)).obj W) ⟶
      (d.J.obj (op (d.L.obj K))).obj (d.G.obj W) :=
  letI := hPi
  boundaryNormalizationMap d.F d.G d.adj d.P d.Q d.H d.J d.aD d.aC
    (fun U V ↦ (d.sC.app U).app V) (fun U V ↦ (d.sD.app U).app V)
    d.L W K (asIso (d.projection _ K))

/-- Exceptional transpose of inverse projection followed by tensoring the counit.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def q (M N : D) (hPi : IsIso (d.projection (d.G.obj N) M)) :
    (d.P.obj (d.L.obj M)).obj (d.G.obj N) ⟶ d.G.obj ((d.Q.obj M).obj N) :=
  letI := hPi
  d.adj.homEquiv _ _
    (d.F.map ((d.sC.app (d.L.obj M)).app (d.G.obj N)).hom ≫
      inv (d.projection (d.G.obj N) M) ≫
      ((d.sD.app (d.F.obj (d.G.obj N))).app M).hom ≫
      (d.Q.obj M).map (d.adj.counit.app N))

/-- Evaluation after the canonical signed interchange.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def evaluation (W K : D) :
    (d.Q.obj ((d.H.obj (op K)).obj W)).obj K ⟶ W :=
  ((d.sD.app ((d.H.obj (op K)).obj W)).app K).hom ≫ (d.aD.adj K).counit.app W

/-- The specified evaluation pairing on the exceptional inverse image.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def r (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K)) :
    (d.P.obj (d.G.obj ((d.H.obj (op K)).obj W))).obj (d.L.obj K) ⟶ d.G.obj W :=
  ((d.sC.app (d.G.obj ((d.H.obj (op K)).obj W))).app (d.L.obj K)).hom ≫
    d.q K ((d.H.obj (op K)).obj W) hPi ≫
    d.G.map (((d.sD.app K).app ((d.H.obj (op K)).obj W)).hom ≫ d.evaluation W K)

private theorem alpha_eq_transpose_r (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K)) :
    d.alpha W K hPi = (d.aC.adj (d.L.obj K)).homEquiv _ _
      (((d.sC.app (d.L.obj K)).app (d.G.obj ((d.H.obj (op K)).obj W))).hom ≫
        d.r W K hPi) := by
  rfl

private theorem alpha_eq_chain (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K)) :
    d.alpha W K hPi = d.chain W K _ hPi (𝟙 _) := by
  let := hPi
  exact (homChain_identity d.F d.G d.adj d.P d.Q d.H d.J d.aD d.aC
    (fun U V ↦ (d.sC.app U).app V) (fun U V ↦ (d.sD.app U).app V)
    d.involutionC d.involutionD d.L W K (asIso (d.projection _ K))).symm

private theorem chain_postcomp (W K : D) (B : C)
    (hPi : IsIso (d.projection B K))
    (hPiX : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K))
    (b : B ⟶ d.G.obj ((d.H.obj (op K)).obj W)) :
    d.chain W K B hPi b = b ≫ d.alpha W K hPiX := by
  let := hPi
  let := hPiX
  rw [d.alpha_eq_chain]
  have h := homChain_natural d.F d.G d.adj d.P d.Q d.H d.J d.aD d.aC
    (fun U V ↦ (d.sC.app U).app V) (fun U V ↦ (d.sD.app U).app V)
    d.L W K B _ (asIso (d.projection B K)) (asIso (d.projection _ K)) b
    (d.projection_left _ _ _ b)
    (swap_inv_right d.sD K (d.F.map b)) (swap_inv_left d.sC b (d.L.obj K)) (𝟙 _)
  simpa only [chain, Category.comp_id] using h

private theorem chain_parameter (W K K' : D) (B : C)
    (hPi : IsIso (d.projection B K)) (hPi' : IsIso (d.projection B K'))
    (u : K ⟶ K') (b : B ⟶ d.G.obj ((d.H.obj (op K')).obj W)) :
    d.chain W K B hPi (b ≫ d.G.map ((d.H.map u.op).app W)) =
      d.chain W K' B hPi' b ≫ (d.J.map (d.L.map u).op).app (d.G.obj W) := by
  let := hPi
  let := hPi'
  exact homChain_parameter d.F d.G d.adj d.P d.Q d.H d.J d.aD d.aC
    (fun U V ↦ (d.sC.app U).app V) (fun U V ↦ (d.sD.app U).app V)
    d.L W K K' B (asIso (d.projection B K)) (asIso (d.projection B K')) u (d.L.map u)
    (d.projection_right B K K' u)
    (swap_inv_left d.sD u (d.F.obj B)) (swap_inv_right d.sC B (d.L.map u)) b

private theorem alpha_natural (W K K' : D)
    (hPi : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K))
    (hPi' : IsIso (d.projection (d.G.obj ((d.H.obj (op K')).obj W)) K'))
    (hCross : IsIso (d.projection (d.G.obj ((d.H.obj (op K')).obj W)) K))
    (u : K ⟶ K') :
    d.G.map ((d.H.map u.op).app W) ≫ d.alpha W K hPi =
      d.alpha W K' hPi' ≫ (d.J.map (d.L.map u).op).app (d.G.obj W) := by
  have h := d.chain_parameter W K K' _ hCross hPi' u (𝟙 _)
  rw [d.chain_postcomp W K _ hCross hPi _, ← d.alpha_eq_chain W K' hPi'] at h
  simpa only [Category.id_comp] using h

private theorem alphaIsoOnTests (W K : D) (P_C : ObjectProperty C)
    (hPF : ∀ B, P_C B → IsIso (d.projection B K))
    (hX : P_C (d.G.obj ((d.H.obj (op K)).obj W)))
    (hY : P_C ((d.J.obj (op (d.L.obj K))).obj (d.G.obj W))) :
    IsIso (d.alpha W K (hPF _ hX)) ∧
      ∀ (B : C) (hB : P_C B) (b : B ⟶ d.G.obj ((d.H.obj (op K)).obj W)),
        d.chain W K B (hPF B hB) b = b ≫ d.alpha W K (hPF _ hX) := by
  have hpost (B : C) (hB : P_C B) (b : B ⟶ d.G.obj ((d.H.obj (op K)).obj W)) :=
    d.chain_postcomp W K B (hPF B hB) (hPF _ hX) b
  refine ⟨?_, hpost⟩
  exact iso_of_homEquivs (d.alpha W K (hPF _ hX))
    (d.chain W K _ (hPF _ hX)) (d.chain W K _ (hPF _ hY))
    (hpost _ hX) (hpost _ hY)

/-- The normalized comparison expressed through equal canonical functors.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def alphaWithFunctors (H' : Dᵒᵖ ⥤ D ⥤ D) (L' : D ⥤ C)
    (hH : d.H = H') (hL : d.L = L') (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((H'.obj (op K)).obj W)) K)) :
    d.G.obj ((H'.obj (op K)).obj W) ⟶ (d.J.obj (op (L'.obj K))).obj (d.G.obj W) := by
  subst H'
  subst L'
  exact d.alpha W K hPi

/-- The independent Hom chain expressed through equal canonical functors.
Source: expanded steps 1--3 (blueprint: lem-weil-boundary-alpha-normalization). -/
def chainWithFunctors (H' : Dᵒᵖ ⥤ D ⥤ D) (L' : D ⥤ C)
    (hH : d.H = H') (hL : d.L = L') (W K : D) (B : C)
    (hPi : IsIso (d.projection B K)) :
    (B ⟶ d.G.obj ((H'.obj (op K)).obj W)) ≃
      (B ⟶ (d.J.obj (op (L'.obj K))).obj (d.G.obj W)) := by
  subst H'
  subst L'
  exact d.chain W K B hPi

/-- The exceptional transpose expressed using the canonical pullback interface.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def qWithPullback (L' : D ⥤ C) (hL : d.L = L') (M N : D)
    (hPi : IsIso (d.projection (d.G.obj N) M)) :
    (d.P.obj (L'.obj M)).obj (d.G.obj N) ⟶ d.G.obj ((d.Q.obj M).obj N) := by
  subst L'
  exact d.q M N hPi

/-- The normalized evaluation pairing expressed through equal canonical functors.
Source: expanded step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def rWithFunctors (H' : Dᵒᵖ ⥤ D ⥤ D) (L' : D ⥤ C)
    (hH : d.H = H') (hL : d.L = L') (W K : D)
    (hPi : IsIso (d.projection (d.G.obj ((H'.obj (op K)).obj W)) K)) :
    (d.P.obj (d.G.obj ((H'.obj (op K)).obj W))).obj (L'.obj K) ⟶ d.G.obj W := by
  subst H'
  subst L'
  exact d.r W K hPi

private theorem alphaWithFunctors_natural
    (H' : Dᵒᵖ ⥤ D ⥤ D) (L' : D ⥤ C)
    (hH : d.H = H') (hL : d.L = L') (W K K' : D)
    (hPi : IsIso (d.projection (d.G.obj ((H'.obj (op K)).obj W)) K))
    (hPi' : IsIso (d.projection (d.G.obj ((H'.obj (op K')).obj W)) K'))
    (hCross : IsIso (d.projection (d.G.obj ((H'.obj (op K')).obj W)) K))
    (u : K ⟶ K') :
    d.G.map ((H'.map u.op).app W) ≫ d.alphaWithFunctors H' L' hH hL W K hPi =
      d.alphaWithFunctors H' L' hH hL W K' hPi' ≫
        (d.J.map (L'.map u).op).app (d.G.obj W) := by
  subst H'
  subst L'
  exact d.alpha_natural W K K' hPi hPi' hCross u

private theorem alphaWithFunctors_isoOnTests
    (H' : Dᵒᵖ ⥤ D ⥤ D) (L' : D ⥤ C)
    (hH : d.H = H') (hL : d.L = L') (W K : D) (P_C : ObjectProperty C)
    (hPF : ∀ B, P_C B → IsIso (d.projection B K))
    (hX : P_C (d.G.obj ((H'.obj (op K)).obj W)))
    (hY : P_C ((d.J.obj (op (L'.obj K))).obj (d.G.obj W))) :
    IsIso (d.alphaWithFunctors H' L' hH hL W K (hPF _ hX)) ∧
      ∀ (B : C) (hB : P_C B) (b : B ⟶ d.G.obj ((H'.obj (op K)).obj W)),
        d.chainWithFunctors H' L' hH hL W K B (hPF B hB) b =
          b ≫ d.alphaWithFunctors H' L' hH hL W K (hPF _ hX) := by
  subst H'
  subst L'
  exact d.alphaIsoOnTests W K P_C hPF hX hY

end BoundaryData
end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Cache the canonical small-site sheafification proof with atomic arguments.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundarySmallSheafify (A : Type (u + 1)) [CommRing A] :
    HasSmallSiteSheafify (ModuleCat.{u + 1} A) := by
  infer_instance

attribute [local instance 10000] boundarySmallSheafify

/-- Cache the canonical etale sheafification proof with atomic arguments.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundarySheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  infer_instance

attribute [local instance 10000] boundarySheafify

/-- Cache the canonical Grothendieck property of the ordinary etale sheaf category.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundarySheafGrothendieck (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundarySheafGrothendieck

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryMonoidalPreadditive (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    MonoidalPreadditive (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundaryMonoidalPreadditive

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryCoproducts (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundaryCoproducts

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryTensor4 (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
  intros
  infer_instance

attribute [local instance 10000] boundaryTensor4

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryTensor12 (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
  intros
  infer_instance

attribute [local instance 10000] boundaryTensor12

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryTensor23 (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
  intros
  infer_instance

attribute [local instance 10000] boundaryTensor23

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryCountableColimits (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundaryCountableColimits

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryExactColimits (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundaryExactColimits

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryLeftTensorColimits (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj X) := by
  intros
  infer_instance

attribute [local instance 10000] boundaryLeftTensorColimits

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryRightTensorColimits (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj X) := by
  intros
  infer_instance

attribute [local instance 10000] boundaryRightTensorColimits

/-- Cache a canonical hypothesis of derived inverse image at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryFlatResolution (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  infer_instance

attribute [local instance 10000] boundaryFlatResolution

/-- Cache the canonical inverse-image hypothesis at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryUpperStarAdditive (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) :
    (upperStar (ModuleCat.{u + 1} A) i).Additive := by
  infer_instance

attribute [local instance 10000] boundaryUpperStarAdditive

/-- Cache the canonical inverse-image hypothesis at atomic arguments.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryUpperStarKFlat (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) :
    (upperStar (ModuleCat.{u + 1} A) i).PreservesKFlatQuasiIso := by
  infer_instance

attribute [local instance 10000] boundaryUpperStarKFlat

/-- The canonical bundled data at the finite coefficient ring.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryData (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    BoundaryData (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  BoundaryData.ofFunctors
    (C := (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))) (D :=
      (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (R(lowerStar (ModuleCat.{u + 1} A) i)) (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))
    (derivedTensor (ModuleCat.{u + 1} A) Z) (derivedTensor (ModuleCat.{u + 1} A) T)
    (derivedHom (ModuleCat.{u + 1} A) T) (derivedHom (ModuleCat.{u + 1} A) Z)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) T)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) Z)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) Z)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) T) (L(upperStar (ModuleCat.{u + 1} A) i))
    (fun B K ↦ ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app B).app K)
    (fun B B' K b ↦ NatTrans.congr_app
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).naturality b) K)
    (fun B K K' u ↦ by
      have h := ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app B).naturality u
      dsimp only [derivedTensorRightDerivedLowerStar,
        rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
        Functor.postcompose₂_obj_obj_obj_map, Functor.whiskeringLeft₂_obj_obj_obj_obj_map,
        Functor.id_obj] at h
      exact h) (derivedTensorSymmetry_involutive A Z) (derivedTensorSymmetry_involutive A T)

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The actual finite quotient coefficient ring, lifted to the small-etale coefficient
universe. Index n denotes level n+1, so every positive level occurs.
Source: coefficient convention (blueprint: lem-weil-boundary-alpha-normalization). -/
abbrev boundaryCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- Finiteness of the lifted positive-level quotient, from the recorded coefficient theorem.
Source: coefficient convention (blueprint: lem-weil-boundary-alpha-normalization). -/
instance boundaryCoefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (boundaryCoefficient l E n) :=
  Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))

variable (A : Type (u + 1)) [CommRing A]

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The descended Koszul symmetry, exactly the symmetry in AmbientDualityPairing.
Source: evaluation identities (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundarySigma (T : Scheme.{u}) (M N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
  + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj N ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj N).obj M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).app M).app N

/-- The ordinary etale derived internal Hom with its native coefficient interface.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryHom (T : Scheme.{u}) :
    (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ ⥤ (DerivedCategory (Sheaf
      T.smallEtaleTopology (ModuleCat.{u + 1} A))) ⥤ (DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :=
  derivedHom (ModuleCat.{u + 1} A) T

/-- Morphisms in the native ordinary etale derived category.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
abbrev boundaryMorphism (T : Scheme.{u}) (M N : (DerivedCategory (Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} A)))) := M ⟶ N

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- Evaluation DK tensor K to W, obtained from the actual tensor-Hom counit and the
Koszul symmetry. This is the evaluation normalized by AmbientDualityPairing.
Source: evaluation identities (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryEvaluation {T : Scheme.{u}} (W K : (DerivedCategory (Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} A)))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W)).obj K ⟶ W :=
  (boundarySigma A T _ K).hom ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app W

variable [Finite A] {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- The cached internal Hom is the canonical etale internal Hom.
Source: expanded step 1 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryData_H_eq :
    (boundaryData A i).H = boundaryHom A T := by
  rfl

/-- The cached inverse image is the canonical derived etale inverse image.
Source: expanded step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryData_L_eq :
    (boundaryData A i).L = (L(upperStar (ModuleCat.{u + 1} A) i)) := by
  rfl

/-- Ri_* is Ri_! for the closed immersion, and this is its ambient right adjoint.
Source: ambient exceptional adjunction (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryG : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) ⥤
  (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (boundaryData A i).G

/-- The actual canonical projection map in the order FB tensor M to F(B tensor i^*M).
Source: expanded proof step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryProjection (B : (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))) (M
  : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) :
    boundaryMorphism A T
      (((boundaryData A i).Q.obj ((boundaryData A i).F.obj B)).obj M)
      ((boundaryData A i).F.obj
        (((boundaryData A i).P.obj B).obj ((boundaryData A i).L.obj M))) :=
  (boundaryData A i).projection B M

/-- q is the exceptional transpose of PF inverse followed by 1 tensor the counit.
The three arrows before tensoring the counit are PF inverse in the node's tensor order.
Source: expanded proof step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaQ (M N : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPi : IsIso (boundaryProjection A i ((boundaryG A i).obj N) M)) :
    boundaryMorphism A Z
      (((boundaryData A i).P.obj ((L(upperStar (ModuleCat.{u + 1} A) i)).obj M)).obj
        ((boundaryG A i).obj N))
      ((boundaryG A i).obj (((boundaryData A i).Q.obj M).obj N)) :=
  (boundaryData A i).qWithPullback (L(upperStar (ModuleCat.{u + 1} A) i))
    (boundaryData_L_eq A i) M N hPi

/-- The specified r_K, with DK equal to RHom(K,W), not a separately supplied object.
Source: evaluation-normalized r (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaR (W K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPi : IsIso (boundaryProjection A i
      ((boundaryG A i).obj (((boundaryHom A T).obj (op K)).obj W)) K)) :
    boundaryMorphism A Z
      (((boundaryData A i).P.obj
        ((boundaryG A i).obj (((boundaryHom A T).obj (op K)).obj W))).obj
          ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K)) ((boundaryG A i).obj W) :=
  (boundaryData A i).rWithFunctors (boundaryHom A T)
    (L(upperStar (ModuleCat.{u + 1} A) i))
    (boundaryData_H_eq A i) (boundaryData_L_eq A i) W K hPi

/-- Alpha is the tensor-Hom transpose of the specified r_K with its signed symmetry.
Source: normalized comparison (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlpha (W K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPi : IsIso (boundaryProjection A i
      ((boundaryG A i).obj (((boundaryHom A T).obj (op K)).obj W)) K)) :
    boundaryMorphism A Z
      ((boundaryG A i).obj (((boundaryHom A T).obj (op K)).obj W))
      (((boundaryData A i).J.obj (op ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K))).obj
        ((boundaryG A i).obj W)) :=
  (boundaryData A i).alphaWithFunctors (boundaryHom A T)
    (L(upperStar (ModuleCat.{u + 1} A) i))
    (boundaryData_H_eq A i) (boundaryData_L_eq A i) W K hPi

/-- The independent composite of six bijections: exceptional adjunction, tensor-Hom,
first symmetry, projection, exceptional adjunction, and symmetry followed by tensor-Hom.
It never mentions alpha. Source: expanded proof steps 1--3
(blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaHomChain (W K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
  A)))) (B : (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPi : IsIso (boundaryProjection A i B K)) :
    boundaryMorphism A Z B
      ((boundaryG A i).obj (((boundaryHom A T).obj (op K)).obj W)) ≃
      boundaryMorphism A Z B
        (((boundaryData A i).J.obj (op ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K))).obj
          ((boundaryG A i).obj W)) :=
  (boundaryData A i).chainWithFunctors (boundaryHom A T)
    (L(upperStar (ModuleCat.{u + 1} A) i))
    (boundaryData_H_eq A i) (boundaryData_L_eq A i) W K B hPi

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The structure-map exceptional inverse image of the constant coefficient object.
Source: omega_T convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryOmegaT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :
    (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  dualizingComplex (ModuleCat.{u + 1} A) aT

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The actual contravariant RHom into omega_T.
Source: D_T convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable abbrev boundaryDT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :
    (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ ⥤ (DerivedCategory (Sheaf
      T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (boundaryHom A T).flip.obj (boundaryOmegaT A aT)

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The actual contravariant RHom into omega_Z = i^times omega_T.
Source: D_Z convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryDZ {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :
    (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ ⥤ (DerivedCategory (Sheaf
      Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (boundaryData A i).J.flip.obj ((boundaryG A i).obj (boundaryOmegaT A aT))

private theorem boundaryG_eq : boundaryG A i = (boundaryData A i).G := by
  rfl

attribute [local irreducible] boundaryG boundaryProjection boundaryAlpha boundaryAlphaHomChain

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem boundaryAlpha_natural {k : Type u} [Field k]
    (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (K K' : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPi : IsIso (boundaryProjection A i
      ((boundaryG A i).obj ((boundaryDT A aT).obj (op K))) K))
    (hPi' : IsIso (boundaryProjection A i
      ((boundaryG A i).obj ((boundaryDT A aT).obj (op K'))) K'))
    (hCross : IsIso (boundaryProjection A i
      ((boundaryG A i).obj ((boundaryDT A aT).obj (op K'))) K))
    (u : K ⟶ K') :
    (boundaryG A i).map ((boundaryDT A aT).map u.op) ≫
        boundaryAlpha A i (boundaryOmegaT A aT) K hPi =
      boundaryAlpha A i (boundaryOmegaT A aT) K' hPi' ≫
        (boundaryDZ A i aT).map
          (L(upperStar (ModuleCat.{u + 1} A) i).map u).op := by
  have hp := hPi
  unfold boundaryProjection boundaryDT at hp
  dsimp only [Functor.flip_obj_obj] at hp
  rw [boundaryG_eq] at hp
  have hp' := hPi'
  unfold boundaryProjection boundaryDT at hp'
  dsimp only [Functor.flip_obj_obj] at hp'
  rw [boundaryG_eq] at hp'
  have hpc := hCross
  unfold boundaryProjection boundaryDT at hpc
  dsimp only [Functor.flip_obj_obj] at hpc
  rw [boundaryG_eq] at hpc
  unfold boundaryG boundaryDT boundaryDZ boundaryAlpha
  dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map]
  unfold boundaryG
  with_reducible
    exact (boundaryData A i).alphaWithFunctors_natural
      (boundaryHom A T) (L(upperStar (ModuleCat.{u + 1} A) i))
      (boundaryData_H_eq A i) (boundaryData_L_eq A i)
      (boundaryOmegaT A aT) K K' hp hp' hpc u

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- Normalization on any class of tests containing the source and target of alpha.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
private theorem boundaryAlphaNormalizationOfTests
    {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (P_D : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (P_C : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPF : ∀ B, P_C B → ∀ M, P_D M → IsIso (boundaryProjection A i B M))
    (K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hK : P_D K)
    (_hiK : P_C ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K))
    (hGDK : P_C ((boundaryG A i).obj ((boundaryDT A aT).obj (op K))))
    (_hdual : ∀ B, P_C B → P_C ((boundaryDZ A i aT).obj (op B))) :
    IsIso (boundaryAlpha A i (boundaryOmegaT A aT) K (hPF ((boundaryG A i).obj
        (((boundaryHom A T).obj (op K)).obj (boundaryOmegaT A aT))) hGDK K hK)) ∧
    (∀ (B : (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hB : P_C B)
      (b : B ⟶ (boundaryG A i).obj ((boundaryDT A aT).obj (op K))),
      boundaryAlphaHomChain A i (boundaryOmegaT A aT) K B (hPF B hB K hK) b =
      b ≫ boundaryAlpha A i (boundaryOmegaT A aT) K (hPF ((boundaryG A i).obj
        (((boundaryHom A T).obj (op K)).obj
          (boundaryOmegaT A aT))) hGDK K hK)) := by
  have hY := _hdual _ _hiK
  unfold boundaryG boundaryDT at hGDK
  unfold boundaryDZ boundaryG at hY
  dsimp only [Functor.flip_obj_obj] at hGDK hY
  unfold boundaryProjection at hPF
  unfold boundaryAlpha boundaryAlphaHomChain boundaryG boundaryDT
  dsimp only [Functor.flip_obj_obj]
  exact (boundaryData A i).alphaWithFunctors_isoOnTests
    (boundaryHom A T) (L(upperStar (ModuleCat.{u + 1} A) i))
    (boundaryData_H_eq A i) (boundaryData_L_eq A i) (boundaryOmegaT A aT) K P_C
    (fun B hB ↦ hPF B hB K hK) hGDK hY

/-- The three boundary-normalization conclusions as one canonical proposition.
This is exactly invertibility of the specified alpha, the independent Hom-chain
identity, and contravariant naturality on the displayed admissible objects.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryNormalizationConclusions
    {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (P_D : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (P_C : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPF : ∀ B, P_C B → ∀ M, P_D M → IsIso (boundaryProjection A i B M))
    (K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hK : P_D K)
    (hGDK : P_C ((boundaryG A i).obj ((boundaryDT A aT).obj (op K)))) : Prop :=
    IsIso (boundaryAlpha A i (boundaryOmegaT A aT) K (hPF _ hGDK K hK)) ∧
    (∀ (B : (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hB : P_C B)
      (b : B ⟶ (boundaryG A i).obj ((boundaryDT A aT).obj (op K))),
      boundaryAlphaHomChain A i (boundaryOmegaT A aT) K B (hPF B hB K hK) b =
        b ≫ boundaryAlpha A i (boundaryOmegaT A aT) K (hPF _ hGDK K hK)) ∧
    (∀ (K' : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hK' : P_D K')
      (_hDK' : P_D ((boundaryDT A aT).obj (op K')))
      (_hiK' : P_C ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K'))
      (hGDK' : P_C ((boundaryG A i).obj ((boundaryDT A aT).obj (op K')))) (u : K ⟶ K'),
      (boundaryG A i).map ((boundaryDT A aT).map u.op) ≫
          boundaryAlpha A i (boundaryOmegaT A aT) K (hPF _ hGDK K hK) =
        boundaryAlpha A i (boundaryOmegaT A aT) K' (hPF _ hGDK' K' hK') ≫
          (boundaryDZ A i aT).map (L(upperStar (ModuleCat.{u + 1} A) i).map u).op)

/-- The three conclusions on arbitrary admissible test classes.
Source: expanded steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization). -/
private theorem boundaryAlphaNormalizationAllTests
    {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (P_D : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (P_C : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (hPF : ∀ B, P_C B → ∀ M, P_D M → IsIso (boundaryProjection A i B M))
    (K : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) (hK : P_D K)
    (_hDK : P_D ((boundaryDT A aT).obj (op K)))
    (hiK : P_C ((L(upperStar (ModuleCat.{u + 1} A) i)).obj K))
    (hGDK : P_C ((boundaryG A i).obj ((boundaryDT A aT).obj (op K))))
    (hdual : ∀ B, P_C B → P_C ((boundaryDZ A i aT).obj (op B))) :
    boundaryNormalizationConclusions A i aT P_D P_C hPF K hK hGDK := by
  unfold boundaryNormalizationConclusions
  have h := boundaryAlphaNormalizationOfTests A i aT P_D P_C hPF K hK hiK hGDK hdual
  refine ⟨h.1, h.2, ?_⟩
  intro K' hK' _hDK' _hiK' hGDK' u
  exact boundaryAlpha_natural A i aT K K'
    (hPF _ hGDK K hK) (hPF _ hGDK' K' hK') (hPF _ hGDK' K hK) u

private theorem boundaryFiniteTorBounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (Z : Scheme.{u})
    (B : DerivedCategoryModule (boundaryCoefficient l E n) Z)
    (hB : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B) :
    DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B := by
  exact hB.1

/-- Restrict the projection-formula hypothesis to finite-Tor test objects.
Source: finite-Tor objects are bounded constructible
(blueprint: lem-weil-boundary-alpha-normalization). -/
theorem boundaryPFOnFiniteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M))
    (B : DerivedCategoryModule (boundaryCoefficient l E n) Z)
    (hB : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B)
    (M : DerivedCategoryModule (boundaryCoefficient l E n) T)
    (hM : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M) :
    IsIso (boundaryProjection (boundaryCoefficient l E n) i B M) := by
  exact hPF B (boundaryFiniteTorBounded l E n Z B hB) M hM

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
/-- The evaluation-normalized closed-costalk comparison is an isomorphism, realizes
exactly the displayed Hom chain on finite-Tor constructible tests, and is contravariantly
natural in every admissible K. All functors and all arrows are the canonical etale ones.

Source: cor-weil-boundary-duality-discharge.proof.md, second paragraph;
expanded node proof steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization).

Proof:
1. Tensor-Hom adjunction on the ordinary small etale ringed sites gives the two
   currying bijections. The exceptional adjunction is on the whole ordinary derived
   category, so it applies before restricting to finite-Tor constructible test objects.
2. Write pi(B,M) for the canonical FB tensor M to F(B tensor i^*M) projection. In the
   opposite tensor order PF is symmetry, pi, and F of symmetry. Thus its inverse is
   precisely the three arrows used in boundaryAlphaQ. Projection naturality gives a
   bijection on Hom by precomposition with pi inverse.
3. Compose the two adjunctions, the currying bijections and these two symmetry changes.
   This is boundaryAlphaHomChain, independently of alpha. On b its first part is
   evaluation after the exceptional counit composed with F(b) tensor the identity.
4. Transpose r_K back through the exceptional adjunction. Naturality of symmetry
   and the projection map cancel the two signed interchanges. The result is exactly
   the previous Hom-chain value at b = identity. Naturality in b then identifies the
   chain at every b with b followed by this particular evaluation-normalized alpha.
5. Set X = G(D_T K), Y = D_Z(i^*K). Both are finite-Tor constructible by hGDK and
   hdual applied to hiK. Surjectivity of the chain at Y gives gamma with gamma alpha
   equal to identity. Injectivity of the chain at X gives alpha gamma equal to
   identity. This proves that the specified alpha is an isomorphism without testing
   on arbitrary pro-etale objects.
6. Evaluation dinaturality, projection naturality in K, and the two adjunction
   naturality identities identify the chain on G(D_T u) b with D_Z(i^*u) after the
   chain for K'. Take b = identity and use step 4. This proves the displayed
   contravariant naturality equation, with the same signed symmetry throughout.
-/
theorem boundaryAlphaNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M))
    (K : DerivedCategoryModule (boundaryCoefficient l E n) T)
    (hK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K)
    (_hDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
      ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K)))
    (_hiK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K))
    (hGDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      ((boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))))
    (_hdual : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryDZ (boundaryCoefficient l E n) i aT).obj (op B))) :
    boundaryNormalizationConclusions (boundaryCoefficient l E n) i aT
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T)
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z)
      (boundaryPFOnFiniteTor l E n i hPF) K hK hGDK := by
  exact boundaryAlphaNormalizationAllTests (boundaryCoefficient l E n) i aT
    (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T)
    (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z)
    (boundaryPFOnFiniteTor l E n i hPF) K hK _hDK _hiK hGDK _hdual

end AlgebraicGeometry.Etale
