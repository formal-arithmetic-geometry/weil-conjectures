/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Counit transposes of composite dualizing tensor maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, paragraph (2)
(blueprint: lem-sp-composite-tensor-transpose).

The helpers spell out the counit map, its Hom transpose, and the two compared arrows.
All projection isomorphisms and their coherence equations remain specified input data.
-/

@[expose] public section

set_option autoImplicit false

universe uX vX uY vY uZ vZ

namespace CategoryTheory

open MonoidalCategory BraidedCategory

section Single

variable {C : Type uX} [Category.{vX} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
  (P : D ⥤ C) (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
  (π : ∀ (M : C) (L : D), F.obj M ⊗ L ≅ F.obj (M ⊗ P.obj L))

/-- The specified map q: interchange, inverse projection, counit tensor identity, unitor.
Source: blueprint composition-factors proof (2), defining counit transpose
(blueprint: lem-sp-composite-tensor-transpose). -/
def spTensorCounit (L : D) : F.obj (P.obj L ⊗ G.obj (𝟙_ D)) ⟶ L :=
  F.map (β_ (P.obj L) (G.obj (𝟙_ D))).hom ≫
    (π (G.obj (𝟙_ D)) L).inv ≫ (adj.counit.app (𝟙_ D) ▷ L) ≫ (λ_ L).hom

/-- The adjoint transpose t of the specified counit map q.
Source: blueprint composition-factors proof (2), tensor map by adjunction
(blueprint: lem-sp-composite-tensor-transpose). -/
def spTensorCounitMate (L : D) : P.obj L ⊗ G.obj (𝟙_ D) ⟶ G.obj L :=
  adj.homEquiv _ _ (spTensorCounit P F G adj π L)

omit [SymmetricCategory C] in
private theorem spProjection_inv_natural
    (hπ : ∀ (M M' : C) (L L' : D) (m : M ⟶ M') (l : L ⟶ L'),
      (F.map m ⊗ₘ l) ≫ (π M' L').hom =
        (π M L).hom ≫ F.map (m ⊗ₘ P.map l))
    (M M' : C) (L L' : D) (m : M ⟶ M') (l : L ⟶ L') :
    F.map (m ⊗ₘ P.map l) ≫ (π M' L').inv =
      (π M L).inv ≫ (F.map m ⊗ₘ l) := by
  apply (cancel_epi (π M L).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using
    congrArg (fun t => t ≫ (π M' L').inv) (hπ M M' L L' m l).symm

private theorem spTensorCounit_natural
    (hπ : ∀ (M M' : C) (L L' : D) (m : M ⟶ M') (l : L ⟶ L'),
      (F.map m ⊗ₘ l) ≫ (π M' L').hom =
        (π M L).hom ≫ F.map (m ⊗ₘ P.map l))
    (L L' : D) (l : L ⟶ L') :
    F.map (P.map l ▷ G.obj (𝟙_ D)) ≫ spTensorCounit P F G adj π L' =
      spTensorCounit P F G adj π L ≫ l := by
  have hi := spProjection_inv_natural P F π hπ
    (G.obj (𝟙_ D)) (G.obj (𝟙_ D)) L L' (𝟙 _) l
  simp only [Functor.map_id, id_tensorHom] at hi
  simp only [spTensorCounit, Category.assoc]
  rw [← F.map_comp_assoc, braiding_naturality_left, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hi, whisker_exchange_assoc]
  dsimp only [Functor.id_obj]
  rw [leftUnitor_naturality]

private theorem spTensorCounitMate_natural
    (hπ : ∀ (M M' : C) (L L' : D) (m : M ⟶ M') (l : L ⟶ L'),
      (F.map m ⊗ₘ l) ≫ (π M' L').hom =
        (π M L).hom ≫ F.map (m ⊗ₘ P.map l))
    (L L' : D) (l : L ⟶ L') :
    (P.map l ▷ G.obj (𝟙_ D)) ≫ spTensorCounitMate P F G adj π L' =
      spTensorCounitMate P F G adj π L ≫ G.map l := by
  exact adj.homEquiv_naturality_left_square _ _ _ _
    (spTensorCounit_natural P F G adj π hπ L L' l)

private theorem spTensorCounitMate_unit [P.Monoidal]
    (hπ : ∀ M : C,
      (ρ_ (F.obj M)).hom = (π M (𝟙_ D)).hom ≫
        F.map ((M ◁ Functor.OplaxMonoidal.η P) ≫ (ρ_ M).hom)) :
    spTensorCounitMate P F G adj π (𝟙_ D) =
      (Functor.OplaxMonoidal.η P ▷ G.obj (𝟙_ D)) ≫ (λ_ (G.obj (𝟙_ D))).hom := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [spTensorCounitMate, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hi : (π (G.obj (𝟙_ D)) (𝟙_ D)).inv =
      F.map ((G.obj (𝟙_ D) ◁ Functor.OplaxMonoidal.η P) ≫
        (ρ_ (G.obj (𝟙_ D))).hom) ≫ (ρ_ (F.obj (G.obj (𝟙_ D)))).inv := by
    apply (cancel_epi (π (G.obj (𝟙_ D)) (𝟙_ D)).hom).1
    simp only [Iso.hom_inv_id]
    rw [← reassoc_of% (hπ (G.obj (𝟙_ D)))]
    simp
  have hu : (ρ_ (F.obj (G.obj (𝟙_ D)))).inv ≫
      (adj.counit.app (𝟙_ D) ▷ (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom =
        adj.counit.app (𝟙_ D) := by
    rw [unitors_equal, rightUnitor_naturality]
    simp
  simp only [spTensorCounit, hi, Category.assoc]
  rw [hu, ← F.map_comp_assoc]
  apply congrArg (fun t => F.map t ≫ adj.counit.app (𝟙_ D))
  rw [← braiding_naturality_left_assoc, braiding_rightUnitor]

omit [SymmetricCategory C] in
private theorem spProjection_inv_assoc [P.Monoidal]
    (hπ : ∀ (M : C) (L L' : D),
      (α_ (F.obj M) L L').hom ≫ (π M (L ⊗ L')).hom ≫
          F.map ((M ◁ Functor.OplaxMonoidal.δ P L L') ≫
            (α_ M (P.obj L) (P.obj L')).inv) =
        ((π M L).hom ▷ L') ≫ (π (M ⊗ P.obj L) L').hom)
    (M : C) (L L' : D) :
    F.map ((α_ M (P.obj L) (P.obj L')).hom ≫
        (M ◁ Functor.LaxMonoidal.μ P L L')) ≫
        (π M (L ⊗ L')).inv ≫ (α_ (F.obj M) L L').inv =
      (π (M ⊗ P.obj L) L').inv ≫ ((π M L).inv ▷ L') := by
  apply (cancel_epi (((π M L).hom ▷ L') ≫ (π (M ⊗ P.obj L) L').hom)).1
  conv_lhs => rw [← hπ]
  simp only [Category.assoc, ← F.map_comp_assoc, ← whiskerLeft_comp,
    Iso.inv_hom_id_assoc, Functor.Monoidal.δ_μ, whiskerLeft_id,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  simp [← comp_whiskerRight]

private theorem spTensorCounit_tensor [SymmetricCategory D] [P.Braided]
    (hn : ∀ (M M' : C) (L L' : D) (m : M ⟶ M') (l : L ⟶ L'),
      (F.map m ⊗ₘ l) ≫ (π M' L').hom =
        (π M L).hom ≫ F.map (m ⊗ₘ P.map l))
    (ha : ∀ (M : C) (L L' : D),
      (α_ (F.obj M) L L').hom ≫ (π M (L ⊗ L')).hom ≫
          F.map ((M ◁ Functor.OplaxMonoidal.δ P L L') ≫
            (α_ M (P.obj L) (P.obj L')).inv) =
        ((π M L).hom ▷ L') ≫ (π (M ⊗ P.obj L) L').hom)
    (B C' : D) :
    F.map ((α_ (P.obj B) (P.obj C') (G.obj (𝟙_ D))).inv ≫
        (Functor.LaxMonoidal.μ P B C' ▷ G.obj (𝟙_ D))) ≫
        spTensorCounit P F G adj π (B ⊗ C') =
      F.map (β_ (P.obj B) (P.obj C' ⊗ G.obj (𝟙_ D))).hom ≫
        (π (P.obj C' ⊗ G.obj (𝟙_ D)) B).inv ≫
        (spTensorCounit P F G adj π C' ▷ B) ≫ (β_ C' B).hom := by
  let O := G.obj (𝟙_ D)
  have hn₁ := spProjection_inv_natural P F π hn
    (P.obj C' ⊗ O) (O ⊗ P.obj C') B B (β_ (P.obj C') O).hom (𝟙 _)
  simp only [Functor.map_id, tensorHom_id] at hn₁
  have hn₂ := spProjection_inv_natural P F π hn O O
    (C' ⊗ B) (B ⊗ C') (𝟙 _) (β_ C' B).hom
  simp only [Functor.map_id, id_tensorHom] at hn₂
  have hu : (α_ (F.obj O) C' B).inv ≫
      ((adj.counit.app (𝟙_ D) ▷ C') ▷ B) ≫ ((λ_ C').hom ▷ B) =
        (adj.counit.app (𝟙_ D) ▷ (C' ⊗ B)) ≫ (λ_ (C' ⊗ B)).hom := by
    monoidal
  have hb :
      (α_ (P.obj B) (P.obj C') O).inv ≫
          (Functor.LaxMonoidal.μ P B C' ▷ O) ≫
          (β_ (P.obj (B ⊗ C')) O).hom =
        (β_ (P.obj B) (P.obj C' ⊗ O)).hom ≫
          ((β_ (P.obj C') O).hom ▷ P.obj B) ≫
          (α_ O (P.obj C') (P.obj B)).hom ≫
          (O ◁ Functor.LaxMonoidal.μ P C' B) ≫
          (O ◁ P.map (β_ C' B).hom) := by
    rw [← whiskerLeft_comp, Functor.LaxBraided.braided,
      whiskerLeft_comp, braiding_naturality_left]
    rw [← braiding_naturality_right_assoc]
    simp only [BraidedCategory.braiding_tensor_left_hom,
      BraidedCategory.braiding_tensor_right_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    simp only [← whiskerLeft_comp, SymmetricCategory.symmetry_assoc]
  symm
  simp only [spTensorCounit, comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% hn₁, ← F.map_comp_assoc,
    ← reassoc_of% (spProjection_inv_assoc P F π ha O C' B)]
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hu]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, ← reassoc_of% hn₂]
  simp only [← F.map_comp_assoc]
  rw [← hb]

private theorem spTensorCounitMate_transpose (L : D) :
    (adj.homEquiv _ _).symm (spTensorCounitMate P F G adj π L) =
      spTensorCounit P F G adj π L :=
  (adj.homEquiv _ _).symm_apply_apply _

end Single

section Composite

variable {X : Type uX} [Category.{vX} X] [MonoidalCategory X] [SymmetricCategory X]
  {Y : Type uY} [Category.{vY} Y] [MonoidalCategory Y] [SymmetricCategory Y]
  {Z : Type uZ} [Category.{vZ} Z] [MonoidalCategory Z] [SymmetricCategory Z]
  (Pf : Y ⥤ X) (Pg : Z ⥤ Y)
  (Ff : X ⥤ Y) (Fg : Y ⥤ Z) (Fh : X ⥤ Z)
  (Gf : Y ⥤ X) (Gg : Z ⥤ Y) (Gh : Z ⥤ X)
  (af : Ff ⊣ Gf) (ag : Fg ⊣ Gg) (ah : Fh ⊣ Gh)
  (πf : ∀ (M : X) (L : Y), Ff.obj M ⊗ L ≅ Ff.obj (M ⊗ Pf.obj L))
  (πg : ∀ (M : Y) (L : Z), Fg.obj M ⊗ L ≅ Fg.obj (M ⊗ Pg.obj L))
  (πh : ∀ (M : X) (L : Z), Fh.obj M ⊗ L ≅ Fh.obj (M ⊗ (Pg ⋙ Pf).obj L))
  (c : Gh ≅ Gg ⋙ Gf)

/-- The coefficient identification mu = rho inverse after c at the unit.
Only rho at Omega_g is required to be invertible.
Source: blueprint composition-factors proof (2), coefficient comparison
(blueprint: lem-sp-composite-tensor-transpose). -/
noncomputable def spCompositeCoefficientIso
    [IsIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))] :
    Gh.obj (𝟙_ Z) ≅ Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y) :=
  (c.app (𝟙_ Z)) ≪≫ (asIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))).symm

/-- The direct h tensor map, transported by mu inverse and c.
Source: blueprint composition-factors proof (2), first compared arrow
(blueprint: lem-sp-composite-tensor-transpose). -/
noncomputable def spCompositeTensorDirect
    [IsIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))] (K : Z) :
    (Pg ⋙ Pf).obj K ⊗ (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y)) ⟶ Gf.obj (Gg.obj K) :=
  ((Pg ⋙ Pf).obj K ◁ (spCompositeCoefficientIso Pf Ff Gf Gg Gh af πf c).inv) ≫
    spTensorCounitMate (Pg ⋙ Pf) Fh Gh ah πh K ≫ c.hom.app K

/-- The iterated tensor map, with its canonical reassociation and tensorator.
Source: blueprint composition-factors proof (2), second compared arrow
(blueprint: lem-sp-composite-tensor-transpose). -/
def spCompositeTensorIterated [Pf.Monoidal] (K : Z) :
    (Pg ⋙ Pf).obj K ⊗ (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y)) ⟶ Gf.obj (Gg.obj K) :=
  (α_ (Pf.obj (Pg.obj K)) (Pf.obj (Gg.obj (𝟙_ Z))) (Gf.obj (𝟙_ Y))).inv ≫
    (Functor.LaxMonoidal.μ Pf (Pg.obj K) (Gg.obj (𝟙_ Z)) ▷ Gf.obj (𝟙_ Y)) ≫
    (Pf.map (spTensorCounitMate Pg Fg Gg ag πg K) ▷ Gf.obj (𝟙_ Y)) ≫
    spTensorCounitMate Pf Ff Gf af πf (Gg.obj K)

/-- The common composite-adjunction transpose: symmetry, the two inverse projections,
then s tensor identity and the left unitor, where s is the composite counit on W.
Source: blueprint composition-factors proof (2), common counit transpose
(blueprint: lem-sp-composite-tensor-transpose). -/
def spCompositeTensorTranspose (K : Z) :
    (Ff ⋙ Fg).obj
      ((Pg ⋙ Pf).obj K ⊗ (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y))) ⟶ K :=
  (Ff ⋙ Fg).map
      (β_ ((Pg ⋙ Pf).obj K) (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y))).hom ≫
    Fg.map (πf (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y)) (Pg.obj K)).inv ≫
    (πg (Ff.obj (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y))) K).inv ≫
    ((Fg.map (spTensorCounit Pf Ff Gf af πf (Gg.obj (𝟙_ Z))) ≫
      ag.counit.app (𝟙_ Z)) ▷ K) ≫ (λ_ K).hom

omit [SymmetricCategory Y] [SymmetricCategory Z] in
private theorem spCompositeTensorDirect_transpose
    [Pf.Monoidal]
    (α : Ff ⋙ Fg ≅ Fh)
    (hc : ∀ K : Z,
      (Ff ⋙ Fg).map (c.hom.app K) ≫ (af.comp ag).counit.app K =
        α.hom.app (Gh.obj K) ≫ ah.counit.app K)
    (hf_natural : ∀ (M M' : X) (L L' : Y) (m : M ⟶ M') (l : L ⟶ L'),
      (Ff.map m ⊗ₘ l) ≫ (πf M' L').hom =
        (πf M L).hom ≫ Ff.map (m ⊗ₘ Pf.map l))
    (hg_natural : ∀ (M M' : Y) (L L' : Z) (m : M ⟶ M') (l : L ⟶ L'),
      (Fg.map m ⊗ₘ l) ≫ (πg M' L').hom =
        (πg M L).hom ≫ Fg.map (m ⊗ₘ Pg.map l))
    (hπ : ∀ (M : X) (L : Z),
      (α.hom.app M ▷ L) ≫ (πh M L).hom =
        (πg (Ff.obj M) L).hom ≫ Fg.map (πf M (Pg.obj L)).hom ≫
          α.hom.app (M ⊗ (Pg ⋙ Pf).obj L))
    [IsIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))] (K : Z) :
    ((af.comp ag).homEquiv _ K).symm
        (spCompositeTensorDirect Pf Pg Ff Fh Gf Gg Gh af ah πf πh c K) =
      spCompositeTensorTranspose Pf Pg Ff Fg Gf Gg af ag πf πg K := by
  let W := Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y)
  let j : W ⟶ Gh.obj (𝟙_ Z) :=
    (spCompositeCoefficientIso Pf Ff Gf Gg Gh af πf c).inv
  have hj : j ≫ c.hom.app (𝟙_ Z) =
      spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)) := by
    simp [j, spCompositeCoefficientIso]
  have he : (Ff ⋙ Fg).map j ≫ α.hom.app (Gh.obj (𝟙_ Z)) ≫
      ah.counit.app (𝟙_ Z) =
        Fg.map (spTensorCounit Pf Ff Gf af πf (Gg.obj (𝟙_ Z))) ≫
          ag.counit.app (𝟙_ Z) := by
    rw [← hc, ← (Ff ⋙ Fg).map_comp_assoc, hj]
    simp only [Adjunction.comp_counit_app, Functor.comp_map, ← Fg.map_comp_assoc]
    rw [show Ff.map (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z))) ≫
        af.counit.app (Gg.obj (𝟙_ Z)) =
          spTensorCounit Pf Ff Gf af πf (Gg.obj (𝟙_ Z)) from
      (af.homEquiv _ _).symm_apply_apply _]
  have hp (M : X) :
      α.hom.app (M ⊗ (Pg ⋙ Pf).obj K) ≫ (πh M K).inv =
        Fg.map (πf M (Pg.obj K)).inv ≫ (πg (Ff.obj M) K).inv ≫
          (α.hom.app M ▷ K) := by
    apply (cancel_mono (πh M K).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hπ]
    simp only [← Fg.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_assoc]
  have hfn := spProjection_inv_natural Pf Ff πf hf_natural
    W (Gh.obj (𝟙_ Z)) (Pg.obj K) (Pg.obj K) j (𝟙 _)
  simp only [Functor.map_id, tensorHom_id] at hfn
  have hgn := spProjection_inv_natural Pg Fg πg hg_natural
    (Ff.obj W) (Ff.obj (Gh.obj (𝟙_ Z))) K K (Ff.map j) (𝟙 _)
  simp only [Functor.map_id, tensorHom_id] at hgn
  change ((af.comp ag).homEquiv _ K).symm
    ((_ ◁ j) ≫ spTensorCounitMate (Pg ⋙ Pf) Fh Gh ah πh K ≫ c.hom.app K) = _
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hc, α.hom.naturality_assoc]
  rw [← Adjunction.homEquiv_counit]
  simp only [spTensorCounitMate, Equiv.symm_apply_apply, spTensorCounit]
  simp only [← α.hom.naturality_assoc]
  erw [reassoc_of% (hp (Gh.obj (𝟙_ Z)))]
  simp only [Functor.comp_map]
  rw [← Fg.map_comp_assoc, ← Ff.map_comp, braiding_naturality_right,
    Ff.map_comp, Fg.map_comp]
  simp only [Category.assoc]
  have hfn' := congrArg (fun t => Fg.map t) hfn
  simp only [Fg.map_comp] at hfn'
  erw [reassoc_of% hfn', reassoc_of% hgn]
  simp only [← comp_whiskerRight_assoc]
  simp only [Functor.comp_map] at he
  rw [he]
  rfl

omit [SymmetricCategory Z] in
private theorem spCompositeTensorIterated_transpose
    [Pf.Braided]
    (hf_natural : ∀ (M M' : X) (L L' : Y) (m : M ⟶ M') (l : L ⟶ L'),
      (Ff.map m ⊗ₘ l) ≫ (πf M' L').hom =
        (πf M L).hom ≫ Ff.map (m ⊗ₘ Pf.map l))
    (hf_assoc : ∀ (M : X) (L L' : Y),
      (α_ (Ff.obj M) L L').hom ≫ (πf M (L ⊗ L')).hom ≫
          Ff.map ((M ◁ Functor.OplaxMonoidal.δ Pf L L') ≫
            (α_ M (Pf.obj L) (Pf.obj L')).inv) =
        ((πf M L).hom ▷ L') ≫ (πf (M ⊗ Pf.obj L) L').hom)
    (hg_natural : ∀ (M M' : Y) (L L' : Z) (m : M ⟶ M') (l : L ⟶ L'),
      (Fg.map m ⊗ₘ l) ≫ (πg M' L').hom =
        (πg M L).hom ≫ Fg.map (m ⊗ₘ Pg.map l)) (K : Z) :
    ((af.comp ag).homEquiv _ K).symm
        (spCompositeTensorIterated Pf Pg Ff Fg Gf Gg af ag πf πg K) =
      spCompositeTensorTranspose Pf Pg Ff Fg Gf Gg af ag πf πg K := by
  rw [Adjunction.comp_homEquiv]
  change (ag.homEquiv _ K).symm ((af.homEquiv _ _).symm
    (spCompositeTensorIterated Pf Pg Ff Fg Gf Gg af ag πf πg K)) = _
  simp only [spCompositeTensorIterated]
  rw [af.homEquiv_naturality_left_symm,
    af.homEquiv_naturality_left_symm,
    af.homEquiv_naturality_left_symm, spTensorCounitMate_transpose]
  rw [spTensorCounit_natural Pf Ff Gf af πf hf_natural]
  simp only [← Category.assoc]
  rw [ag.homEquiv_naturality_left_symm, spTensorCounitMate_transpose]
  simp only [← Ff.map_comp]
  rw [spTensorCounit_tensor Pf Ff Gf af πf hf_natural hf_assoc]
  have hn := spProjection_inv_natural Pg Fg πg hg_natural
    (Ff.obj (Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y))) (Gg.obj (𝟙_ Z)) K K
    (spTensorCounit Pf Ff Gf af πf (Gg.obj (𝟙_ Z))) (𝟙 _)
  simp only [Functor.map_id, tensorHom_id] at hn
  simp only [spTensorCounit, Fg.map_comp, Category.assoc]
  have hb : Fg.map (β_ (Gg.obj (𝟙_ Z)) (Pg.obj K)).hom ≫
      Fg.map (β_ (Pg.obj K) (Gg.obj (𝟙_ Z))).hom = 𝟙 _ := by
    simp [← Fg.map_comp]
  rw [reassoc_of% hb]
  erw [reassoc_of% hn]
  simp only [← comp_whiskerRight_assoc]
  rfl

/-- Both displayed maps have the specified common composite-adjunction transpose,
and hence agree; each single tensor map is unital and natural in every coefficient.

Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-tensor-transpose).

Proof, following the eight DAG steps:
1. Use lem-weil-pbc-adjunction-of-natural-bijection to write the inverse Hom map as
   F of the arrow followed by the counit. Apply this twice for the composite adjunction.
2. Naturality of symmetry, inverse projections, tensor and the unitor makes q natural.
   Apply lem-sfb-adjunction-transpose-square to obtain naturality of t.
3. Expand projection associativity to express q at B tensor C by q at C followed by
   the inverse projection at B. Naturality and the hexagon identify the permutation.
4. Inverse-transpose the iterated arrow: the defining transpose of t_f and naturality
   of q_f give q_g after F_g(q_f at B tensor C).
5. Insert step 3; cancel the two interchanges and use inverse-projection naturality.
   The resulting arrow is exactly spCompositeTensorTranspose, with s as displayed.
6. Put j = mu inverse. The definition gives c_1 after j = rho. Counit compatibility
   and the defining transpose of rho identify the direct coefficient counit with s.
7. Inverse-transpose the direct arrow using counit compatibility. Move alpha through
   the symmetry, use projection compatibility, and move j through the two inverse
   projections. Step 6 yields the same common transpose as in step 5.
8. Injectivity of the composite Hom bijection gives equality. Projection unitality,
   symmetry at the unit, and the unitor equations reduce q at 1 to the counit after
   F of the canonical unit identification; its transpose is that identification.
   Combine this with step 2. No t at another coefficient is assumed invertible. -/
theorem spCompositeTensorTranspose_eq
    [Pf.Braided] [Pg.Braided]
    (α : Ff ⋙ Fg ≅ Fh)
    (hc : ∀ K : Z,
      (Ff ⋙ Fg).map (c.hom.app K) ≫ (af.comp ag).counit.app K =
        α.hom.app (Gh.obj K) ≫ ah.counit.app K)
    (hf_natural : ∀ (M M' : X) (L L' : Y) (m : M ⟶ M') (l : L ⟶ L'),
      (Ff.map m ⊗ₘ l) ≫ (πf M' L').hom =
        (πf M L).hom ≫ Ff.map (m ⊗ₘ Pf.map l))
    (hf_unit : ∀ M : X,
      (ρ_ (Ff.obj M)).hom = (πf M (𝟙_ Y)).hom ≫
        Ff.map ((M ◁ Functor.OplaxMonoidal.η Pf) ≫ (ρ_ M).hom))
    (hf_assoc : ∀ (M : X) (L L' : Y),
      (α_ (Ff.obj M) L L').hom ≫ (πf M (L ⊗ L')).hom ≫
          Ff.map ((M ◁ Functor.OplaxMonoidal.δ Pf L L') ≫
            (α_ M (Pf.obj L) (Pf.obj L')).inv) =
        ((πf M L).hom ▷ L') ≫ (πf (M ⊗ Pf.obj L) L').hom)
    (hg_natural : ∀ (M M' : Y) (L L' : Z) (m : M ⟶ M') (l : L ⟶ L'),
      (Fg.map m ⊗ₘ l) ≫ (πg M' L').hom =
        (πg M L).hom ≫ Fg.map (m ⊗ₘ Pg.map l))
    (hg_unit : ∀ M : Y,
      (ρ_ (Fg.obj M)).hom = (πg M (𝟙_ Z)).hom ≫
        Fg.map ((M ◁ Functor.OplaxMonoidal.η Pg) ≫ (ρ_ M).hom))
    (hg_assoc : ∀ (M : Y) (L L' : Z),
      (α_ (Fg.obj M) L L').hom ≫ (πg M (L ⊗ L')).hom ≫
          Fg.map ((M ◁ Functor.OplaxMonoidal.δ Pg L L') ≫
            (α_ M (Pg.obj L) (Pg.obj L')).inv) =
        ((πg M L).hom ▷ L') ≫ (πg (M ⊗ Pg.obj L) L').hom)
    (hh_natural : ∀ (M M' : X) (L L' : Z) (m : M ⟶ M') (l : L ⟶ L'),
      (Fh.map m ⊗ₘ l) ≫ (πh M' L').hom =
        (πh M L).hom ≫ Fh.map (m ⊗ₘ (Pg ⋙ Pf).map l))
    (hh_unit : ∀ M : X,
      (ρ_ (Fh.obj M)).hom = (πh M (𝟙_ Z)).hom ≫
        Fh.map ((M ◁ Functor.OplaxMonoidal.η (Pg ⋙ Pf)) ≫ (ρ_ M).hom))
    (hh_assoc : ∀ (M : X) (L L' : Z),
      (α_ (Fh.obj M) L L').hom ≫ (πh M (L ⊗ L')).hom ≫
          Fh.map ((M ◁ Functor.OplaxMonoidal.δ (Pg ⋙ Pf) L L') ≫
            (α_ M ((Pg ⋙ Pf).obj L) ((Pg ⋙ Pf).obj L')).inv) =
        ((πh M L).hom ▷ L') ≫ (πh (M ⊗ (Pg ⋙ Pf).obj L) L').hom)
    (hπ : ∀ (M : X) (L : Z),
      (α.hom.app M ▷ L) ≫ (πh M L).hom =
        (πg (Ff.obj M) L).hom ≫ Fg.map (πf M (Pg.obj L)).hom ≫
          α.hom.app (M ⊗ (Pg ⋙ Pf).obj L))
    [IsIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))] :
    (∀ K : Z,
      ((af.comp ag).homEquiv _ K).symm
          (spCompositeTensorDirect Pf Pg Ff Fh Gf Gg Gh af ah πf πh c K) =
        spCompositeTensorTranspose Pf Pg Ff Fg Gf Gg af ag πf πg K ∧
      ((af.comp ag).homEquiv _ K).symm
          (spCompositeTensorIterated Pf Pg Ff Fg Gf Gg af ag πf πg K) =
        spCompositeTensorTranspose Pf Pg Ff Fg Gf Gg af ag πf πg K ∧
      spCompositeTensorDirect Pf Pg Ff Fh Gf Gg Gh af ah πf πh c K =
        spCompositeTensorIterated Pf Pg Ff Fg Gf Gg af ag πf πg K) ∧
    (spTensorCounitMate Pf Ff Gf af πf (𝟙_ Y) =
      (Functor.OplaxMonoidal.η Pf ▷ Gf.obj (𝟙_ Y)) ≫ (λ_ (Gf.obj (𝟙_ Y))).hom) ∧
    (∀ (L L' : Y) (l : L ⟶ L'),
      (Pf.map l ▷ Gf.obj (𝟙_ Y)) ≫ spTensorCounitMate Pf Ff Gf af πf L' =
        spTensorCounitMate Pf Ff Gf af πf L ≫ Gf.map l) ∧
    (spTensorCounitMate Pg Fg Gg ag πg (𝟙_ Z) =
      (Functor.OplaxMonoidal.η Pg ▷ Gg.obj (𝟙_ Z)) ≫ (λ_ (Gg.obj (𝟙_ Z))).hom) ∧
    (∀ (L L' : Z) (l : L ⟶ L'),
      (Pg.map l ▷ Gg.obj (𝟙_ Z)) ≫ spTensorCounitMate Pg Fg Gg ag πg L' =
        spTensorCounitMate Pg Fg Gg ag πg L ≫ Gg.map l) ∧
    (spTensorCounitMate (Pg ⋙ Pf) Fh Gh ah πh (𝟙_ Z) =
      (Functor.OplaxMonoidal.η (Pg ⋙ Pf) ▷ Gh.obj (𝟙_ Z)) ≫ (λ_ (Gh.obj (𝟙_ Z))).hom) ∧
    (∀ (L L' : Z) (l : L ⟶ L'),
      ((Pg ⋙ Pf).map l ▷ Gh.obj (𝟙_ Z)) ≫ spTensorCounitMate (Pg ⋙ Pf) Fh Gh ah πh L' =
        spTensorCounitMate (Pg ⋙ Pf) Fh Gh ah πh L ≫ Gh.map l)  := by
  refine ⟨?_, spTensorCounitMate_unit Pf Ff Gf af πf hf_unit,
    spTensorCounitMate_natural Pf Ff Gf af πf hf_natural,
    spTensorCounitMate_unit Pg Fg Gg ag πg hg_unit,
    spTensorCounitMate_natural Pg Fg Gg ag πg hg_natural,
    spTensorCounitMate_unit (Pg ⋙ Pf) Fh Gh ah πh hh_unit,
    spTensorCounitMate_natural (Pg ⋙ Pf) Fh Gh ah πh hh_natural⟩
  intro K
  have hd := spCompositeTensorDirect_transpose Pf Pg Ff Fg Fh Gf Gg Gh af ag ah
    πf πg πh c α hc hf_natural hg_natural hπ K
  have hi := spCompositeTensorIterated_transpose Pf Pg Ff Fg Gf Gg af ag
    πf πg hf_natural hf_assoc hg_natural K
  have _ := hg_assoc
  have _ := hh_assoc
  exact ⟨hd, hi, ((af.comp ag).homEquiv _ K).symm.injective (hd.trans hi.symm)⟩

end Composite

end CategoryTheory
