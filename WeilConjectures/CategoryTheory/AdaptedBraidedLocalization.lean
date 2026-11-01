/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Normalized.NormalizedBraidedLocalization
import all WeilConjectures.CategoryTheory.Normalized.NormalizedBraidedLocalization

/-! # Braided localization with simultaneous adapted representatives

Source: Stacks Project, Tags 06YS, 06YT and 0FPT.
(blueprint: lem-zl-adapted-braided-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Category MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory

variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory A] [BraidedCategory B] [BraidedCategory D] [BraidedCategory E]
  (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
  [Q.LaxBraided] [L.LaxBraided] [F.Braided] (e : Q ⋙ G ≅ F ⋙ L)

/-- A strong braided functor descends along localization using any resolving class on
which both tensor comparisons are invertible. The class can impose simultaneous
conditions on a representative and its image, instead of preservation of every K-flat
object.

Source: Stacks Project, Tags 06YS, 06YT and 0FPT; the normalized localization-square
argument (blueprint: lem-zl-adapted-braided-localization).

Proof: derive the two tensor bifunctors using the specified adapted subcategory. Their
counits agree after the natural localization factorization. Uniqueness of left-derived
bifunctors supplies an invertible comparison. The lax-square construction transfers
associativity and units, and invertibility makes the comparison strong. Its defining
square makes the factorization monoidal, including its unit. On adapted representatives,
cancel the invertible source tensorator in the braided square of the composite. Every
localized object has such a representative, so naturality transports this equation to
all objects. -/
theorem adaptedBraidedLocalization (W : MorphismProperty A) (S : ObjectProperty A)
    [W.ContainsIdentities] [W.RespectsIso] [Q.IsLocalization W]
    [(LocalizerMorphism.ofEq (F := S.ι) (W₂ := W) rfl).IsLeftDerivabilityStructure]
    [IsIso (ε Q)] [IsIso (ε L)]
    (hmodels : ∀ X : D, ∃ a, S a ∧ Nonempty (Q.obj a ≅ X))
    (hQ : ∀ a b, S b → IsIso (μ Q a b))
    (hL : ∀ (x : B) b, S b → IsIso (μ L x (F.obj b))) :
    ∃ b : G.Braided, letI := b
      NatTrans.IsMonoidal e.hom := by
  let T := (((whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E)
  let U := (postcompose₂.obj G).obj (curriedTensor D)
  let α := squareTargetCounit Q L F G e
  let β := squareSourceCounit Q L F G e
  have : T.IsLeftDerivedFunctor₂ α W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (LocalizerMorphism.ofEq (F := S.ι) (W₂ := W) rfl) α
    intro a b
    have := hL (F.obj a) b.obj b.property
    dsimp only [α, LocalizerMorphism.id_functor, Functor.id_obj]
    rw [squareTargetCounit_app]
    change IsIso ((e.hom.app a ⊗ₘ e.hom.app b.obj) ≫ μ L (F.obj a) (F.obj b.obj))
    infer_instance
  have : U.IsLeftDerivedFunctor₂ β W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (LocalizerMorphism.ofEq (F := S.ι) (W₂ := W) rfl) β
    intro a b
    have := hQ a b.obj b.property
    change IsIso (G.map (μ Q a b.obj) ≫ e.hom.app _ ≫ L.map (δ F _ _))
    infer_instance
  let t : U ≅ T := leftDerived₂NatIso T α W W U β (Iso.refl _)
  have ht (X Y : A) : (t.hom.app (Q.obj X)).app (Q.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) =
      G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y) := by
    have hh := leftDerived₂NatTrans_app_app T α W W U β (𝟙 _) X Y
    rw [show (α.app X).app Y =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) from
        squareTargetCounit_app Q L F G e X Y] at hh
    change (t.hom.app (Q.obj X)).app (Q.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) =
        (β.app X).app Y ≫ 𝟙 _ at hh
    exact hh.trans (Category.comp_id _)
  let : G.OplaxMonoidal := .ofLaxSquare t.hom (fun a ↦ e.hom.app a)
    (fun _ _ f ↦ e.hom.naturality f) ht S hmodels hL
  have (X Y : D) : IsIso (δ G X Y) :=
    inferInstanceAs (IsIso ((t.hom.app X).app Y))
  have : IsIso (η G) := by
    change IsIso (G.map (ε Q) ≫ e.hom.app _ ≫ L.map (η F) ≫ inv (ε L))
    infer_instance
  let : G.Monoidal := .ofOplaxMonoidal G
  have hm : NatTrans.IsMonoidal e.hom :=
    square_monoidal Q L F G e rfl ht
  have hi : NatTrans.IsMonoidal e.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.inv)
  let lb : (Q ⋙ G).LaxBraided := Functor.LaxBraided.ofNatIso e.symm
  have hb (a b : A) (ha : S a) :
      μ G (Q.obj a) (Q.obj b) ≫ G.map (β_ (Q.obj a) (Q.obj b)).hom =
        (β_ (G.obj (Q.obj a)) (G.obj (Q.obj b))).hom ≫ μ G (Q.obj b) (Q.obj a) := by
    have := hQ b a ha
    apply (cancel_mono (G.map (μ Q b a))).1
    have hh := lb.braided a b
    change (μ G (Q.obj a) (Q.obj b) ≫ G.map (μ Q a b)) ≫
      G.map (Q.map (β_ a b).hom) =
        (β_ (G.obj (Q.obj a)) (G.obj (Q.obj b))).hom ≫
          μ G (Q.obj b) (Q.obj a) ≫ G.map (μ Q b a) at hh
    rw [assoc, ← G.map_comp, Functor.LaxBraided.braided (F := Q), G.map_comp] at hh
    simpa only [assoc] using hh
  refine ⟨{ toMonoidal := inferInstance, braided := ?_ }, hm⟩
  intro X Y
  obtain ⟨a, ha, ⟨ia⟩⟩ := hmodels X
  obtain ⟨b, hb', ⟨ib⟩⟩ := hmodels Y
  apply (cancel_epi (G.map ia.hom ⊗ₘ G.map ib.hom)).1
  rw [μ_natural_assoc, ← G.map_comp, BraidedCategory.braiding_naturality,
    G.map_comp, ← assoc, hb a b ha, assoc, ← μ_natural,
    BraidedCategory.braiding_naturality_assoc]

end CategoryTheory
