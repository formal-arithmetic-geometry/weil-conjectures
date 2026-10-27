/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.VaryingSiteAbelianSystems
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.VaryingSiteFreeEvaluationCoherence
import Sheaf.CategoryTheory.VaryingSiteCofreeEvaluationCoherence
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Adjoints to evaluation on varying-site abelian systems

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, arrow-indexed product;
spaces-simplicial.tex, Tag 09WG (5)-(7), free evaluation construction
(blueprint: lem-per-varying-site-evaluation-adjoints).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.CoherentSitePseudofunctor

variable {I : Type u} [Category.{v} I]
  {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)
  [∀ (i j : I) (a : i ⟶ j), (D.abelianInverse a).Additive]

/-- Presentation of both evaluation adjoints, including every specified normalization.
The component isomorphisms are natural in the sheaf argument. The transition equations
are tested on the pulled-back coprojections, respectively the product projections;
they never require inverse image to preserve an infinite product. The four last
fields specify both directions of both Hom bijections, including identity transports.
Source: Stacks 0EXZ and 09WG (5)-(7)
(blueprint: lem-per-varying-site-evaluation-adjoints). -/
structure AbelianEvaluationAdjoints (i : I) where
  left : D.abelianFibre i ⥤ D.AbelianSystem
  right : D.abelianFibre i ⥤ D.AbelianSystem
  [left_additive : left.Additive]
  [right_additive : right.Additive]
  leftAdjunction : left ⊣ D.abelianEvaluation i
  rightAdjunction : D.abelianEvaluation i ⊣ right
  leftComponent : ∀ (A : D.abelianFibre i) (j : I),
    (left.obj A).obj j ≅ ∐ (fun a : j ⟶ i => (D.abelianInverse a).obj A)
  rightComponent : ∀ (A : D.abelianFibre i) (j : I),
    (right.obj A).obj j ≅ ∏ᶜ (fun a : i ⟶ j => (D.abelianDirect a).obj A)
  left_naturality : ∀ {A B : D.abelianFibre i} (h : A ⟶ B) (j : I),
    (left.map h).val j ≫ (leftComponent B j).hom =
      (leftComponent A j).hom ≫ Limits.Sigma.map (fun a => (D.abelianInverse a).map h)
  right_naturality : ∀ {A B : D.abelianFibre i} (h : A ⟶ B) (j : I),
    (right.map h).val j ≫ (rightComponent B j).hom =
      (rightComponent A j).hom ≫ Limits.Pi.map (fun a => (D.abelianDirect a).map h)
  left_transition : ∀ (A : D.abelianFibre i) {j k : I} (c : k ⟶ j) (a : j ⟶ i),
    (D.abelianInverse c).map
        (Sigma.ι (fun a : j ⟶ i => (D.abelianInverse a).obj A) a ≫
          (leftComponent A j).inv) ≫ (left.obj A).transition c =
      (D.abelianInverseComp c a).hom.app A ≫
        Sigma.ι (fun a : k ⟶ i => (D.abelianInverse a).obj A) (c ≫ a) ≫
          (leftComponent A k).inv
  right_transition : ∀ (A : D.abelianFibre i) {j k : I} (c : k ⟶ j) (b : i ⟶ k),
    (right.obj A).transition c ≫ (rightComponent A k).hom ≫
        Pi.π (fun b : i ⟶ k => (D.abelianDirect b).obj A) b =
      (D.abelianInverse c).map
        ((rightComponent A j).hom ≫
          Pi.π (fun a : i ⟶ j => (D.abelianDirect a).obj A) (b ≫ c) ≫
            (D.abelianDirectComp b c).inv.app A) ≫
              (D.abelianAdjunction c).counit.app ((D.abelianDirect b).obj A)
  left_hom : ∀ (A : D.abelianFibre i) (X : D.AbelianSystem) (h : left.obj A ⟶ X),
    leftAdjunction.homEquiv A X h =
      (D.abelianInverseId i).inv.app A ≫
        Sigma.ι (fun a : i ⟶ i => (D.abelianInverse a).obj A) (𝟙 i) ≫
          (leftComponent A i).inv ≫ h.val i
  left_hom_inverse : ∀ (A : D.abelianFibre i) (X : D.AbelianSystem)
    (h : A ⟶ X.obj i) (j : I) (a : j ⟶ i),
    Sigma.ι (fun a : j ⟶ i => (D.abelianInverse a).obj A) a ≫
        (leftComponent A j).inv ≫ ((leftAdjunction.homEquiv A X).symm h).val j =
      (D.abelianInverse a).map h ≫ X.transition a
  right_hom : ∀ (X : D.AbelianSystem) (A : D.abelianFibre i) (h : X ⟶ right.obj A),
    (rightAdjunction.homEquiv X A).symm h =
      h.val i ≫ (rightComponent A i).hom ≫
        Pi.π (fun a : i ⟶ i => (D.abelianDirect a).obj A) (𝟙 i) ≫
          (D.abelianDirectId i).hom.app A
  right_hom_inverse : ∀ (X : D.AbelianSystem) (A : D.abelianFibre i)
    (h : X.obj i ⟶ A) (j : I) (a : i ⟶ j),
    (rightAdjunction.homEquiv X A h).val j ≫ (rightComponent A j).hom ≫
        Pi.π (fun a : i ⟶ j => (D.abelianDirect a).obj A) a =
      (D.abelianAdjunction a).homEquiv (X.obj j) A (X.transition a ≫ h)

private abbrev freeSystem (i : I) (A : D.abelianFibre i) : D.AbelianSystem where
  obj := D.abelianFreeFamily i A
  transition := D.abelianFreeTransition i A
  transition_id := (D.abelianFreeEvaluation_coherence i A).1
  transition_comp := (D.abelianFreeEvaluation_coherence i A).2.1

omit [∀ (i j : I) (a : i ⟶ j), (D.abelianInverse a).Additive] in
private lemma free_ext {i j k : I} (A : D.abelianFibre i) (c : k ⟶ j)
    {B : D.abelianFibre k}
    (f g : (D.abelianInverse c).obj (D.abelianFreeFamily i A j) ⟶ B)
    (h : ∀ a : j ⟶ i,
      (D.abelianInverse c).map
          (Sigma.ι (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A) a) ≫ f =
        (D.abelianInverse c).map
          (Sigma.ι (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A) a) ≫ g) : f = g := by
  let : PreservesColimitsOfSize.{v, v} (D.abelianInverse c) :=
    (D.abelianAdjunction c).leftAdjoint_preservesColimits
  exact Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit (D.abelianInverse c)
      (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A)) f g h

private abbrev freeMap (i : I) {A B : D.abelianFibre i} (h : A ⟶ B) :
    freeSystem D i A ⟶ freeSystem D i B :=
  ⟨fun j ↦ Limits.Sigma.map (fun a : j ⟶ i ↦ (D.abelianInverse a).map h), by
    intro j k c
    apply free_ext D A c
    intro a
    dsimp only [freeSystem]
    rw [← Functor.map_comp_assoc, Sigma.ι_map, Functor.map_comp]
    simp only [Category.assoc, abelianFreeTransition_ι_assoc,
      abelianFreeTransition_ι, Sigma.ι_map]
    simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj,
      abelianFreeFamily, Sigma.ι_desc, Sigma.ι_desc_assoc] using congrArg (fun f ↦ f ≫
      Sigma.ι (fun t : j ⟶ i ↦ (D.abelianInverse t).obj B) (c ≫ a))
        ((D.abelianInverseComp c a).hom.naturality h)⟩

private abbrev freeFunctor (i : I) : D.abelianFibre i ⥤ D.AbelianSystem where
  obj := freeSystem D i
  map := freeMap D i
  map_id A := by
    apply Subtype.ext
    funext j
    change Limits.Sigma.map (fun a : j ⟶ i ↦ (D.abelianInverse a).map (𝟙 A)) = 𝟙 _
    simp only [Functor.map_id, Limits.Sigma.map_id]
  map_comp h k := by
    apply Subtype.ext
    funext j
    change Limits.Sigma.map (fun a : j ⟶ i ↦ (D.abelianInverse a).map (h ≫ k)) =
      Limits.Sigma.map (fun a : j ⟶ i ↦ (D.abelianInverse a).map h) ≫
        Limits.Sigma.map (fun a : j ⟶ i ↦ (D.abelianInverse a).map k)
    simp only [Functor.map_comp, Limits.Sigma.map_comp_map]

private abbrev freeExtension (i : I) (A : D.abelianFibre i) (X : D.AbelianSystem)
    (h : A ⟶ X.obj i) : freeSystem D i A ⟶ X :=
  ⟨fun j ↦ Sigma.desc (fun a : j ⟶ i ↦ (D.abelianInverse a).map h ≫ X.transition a), by
    intro j k c
    apply free_ext D A c
    intro a
    dsimp only [freeSystem]
    rw [← Functor.map_comp_assoc, Sigma.ι_desc, Functor.map_comp]
    simp only [Category.assoc, abelianFreeTransition_ι_assoc]
    rw [← X.transition_comp c a]
    simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj,
      abelianFreeFamily, Sigma.ι_desc, Sigma.ι_desc_assoc] using
      congrArg (fun f ↦ f ≫ X.transition (c ≫ a))
      ((D.abelianInverseComp c a).hom.naturality h)⟩

private abbrev freeHomEquiv (i : I) (A : D.abelianFibre i) (X : D.AbelianSystem) :
    (freeSystem D i A ⟶ X) ≃ (A ⟶ X.obj i) where
  toFun h := (D.abelianInverseId i).inv.app A ≫
    Sigma.ι (fun a : i ⟶ i ↦ (D.abelianInverse a).obj A) (𝟙 i) ≫ h.val i
  invFun := freeExtension D i A X
  left_inv h := by
    apply Subtype.ext
    funext j
    apply Sigma.hom_ext
    intro a
    dsimp only [freeExtension]
    rw [Sigma.ι_desc, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [h.property a]
    change _ = Sigma.ι _ a ≫ h.val j
    rw [← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, (D.abelianFreeEvaluation_coherence i A).2.2 j a]
  right_inv h := by
    dsimp only [freeExtension]
    rw [Sigma.ι_desc, X.transition_id]
    have hn := (D.abelianInverseId i).hom.naturality h
    dsimp only [Functor.id_obj, Functor.id_map] at hn
    rw [hn]
    simp

private def freeAdjunction (i : I) : freeFunctor D i ⊣ D.abelianEvaluation i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := freeHomEquiv D i
    homEquiv_naturality_left_symm := by
      intro A B X h k
      apply Subtype.ext
      funext j
      apply Sigma.hom_ext
      intro a
      change Sigma.ι _ a ≫ Sigma.desc _ =
        Sigma.ι _ a ≫ Limits.Sigma.map _ ≫ Sigma.desc _
      simp [Functor.map_comp]
    homEquiv_naturality_right := by
      intro A X Y h k
      change (D.abelianInverseId i).inv.app A ≫
          Sigma.ι (fun a : i ⟶ i ↦ (D.abelianInverse a).obj A) (𝟙 i) ≫
            (h.val i ≫ k.val i) =
        ((D.abelianInverseId i).inv.app A ≫
          Sigma.ι (fun a : i ⟶ i ↦ (D.abelianInverse a).obj A) (𝟙 i) ≫ h.val i) ≫
            k.val i
      simp only [Category.assoc] }

private abbrev cofreeSystem (i : I) (A : D.abelianFibre i) : D.AbelianSystem where
  obj := D.abelianCofreeFamily i A
  transition := D.abelianCofreeTransition i A
  transition_id := (D.abelianCofreeEvaluation_coherence i A).1
  transition_comp := (D.abelianCofreeEvaluation_coherence i A).2.1

private abbrev cofreeExtension (i : I) (X : D.AbelianSystem) (A : D.abelianFibre i)
    (h : X.obj i ⟶ A) : X ⟶ cofreeSystem D i A :=
  ⟨D.abelianCofreeExtension i X A h,
    (D.abelianCofreeEvaluation_coherence i A).2.2.2.2 X h⟩

private def cofreeRestriction (i : I) (A : D.abelianFibre i)
    (X : D.AbelianSystem) (h : X ⟶ cofreeSystem D i A) : X.obj i ⟶ A :=
  h.val i ≫ Pi.π (fun a : i ⟶ i ↦ (D.abelianDirect a).obj A) (𝟙 i) ≫
    (D.abelianDirectId i).hom.app A

private abbrev cofreeHomEquiv (i : I) (X : D.AbelianSystem) (A : D.abelianFibre i) :
    (X.obj i ⟶ A) ≃ (X ⟶ cofreeSystem D i A) where
  toFun := cofreeExtension D i X A
  invFun := cofreeRestriction D i A X
  left_inv h := by
    dsimp only [cofreeRestriction, cofreeExtension, abelianCofreeExtension]
    rw [Pi.lift_π_assoc, X.transition_id]
    exact (D.abelianCofreeEvaluation_coherence i A).2.2.1 (X.obj i) h
  right_inv h := by
    apply Subtype.ext
    funext j
    apply Pi.hom_ext
    intro a
    dsimp only [cofreeExtension, abelianCofreeExtension]
    rw [Pi.lift_π]
    dsimp only [cofreeRestriction]
    rw [← Category.assoc, ← h.property a]
    simp only [Category.assoc]
    rw [(D.abelianAdjunction a).homEquiv_naturality_left]
    change h.val j ≫ _ = _
    rw [(D.abelianCofreeEvaluation_coherence i A).2.2.2.1 j a]

private def cofreeMap (i : I) {A B : D.abelianFibre i} (h : A ⟶ B) :
    cofreeSystem D i A ⟶ cofreeSystem D i B :=
  cofreeExtension D i (cofreeSystem D i A) B
    (Pi.π (fun a : i ⟶ i ↦ (D.abelianDirect a).obj A) (𝟙 i) ≫
      (D.abelianDirectId i).hom.app A ≫ h)

private lemma cofreeMap_val (i : I) {A B : D.abelianFibre i} (h : A ⟶ B) (j : I) :
    (cofreeMap D i h).val j =
      Limits.Pi.map (fun a : i ⟶ j ↦ (D.abelianDirect a).map h) := by
  apply Pi.hom_ext
  intro a
  dsimp only [cofreeMap, cofreeExtension, abelianCofreeExtension, cofreeSystem]
  rw [Pi.lift_π, Pi.map_π]
  have hn := (D.abelianAdjunction a).homEquiv_naturality_right
    (D.abelianCofreeTransition i A a ≫
      Pi.π (fun t : i ⟶ i ↦ (D.abelianDirect t).obj A) (𝟙 i) ≫
        (D.abelianDirectId i).hom.app A) h
  dsimp only [Functor.id_obj] at hn
  rw [(D.abelianCofreeEvaluation_coherence i A).2.2.2.1 j a] at hn
  simpa only [Category.assoc] using hn

private abbrev cofreeFunctor (i : I) : D.abelianFibre i ⥤ D.AbelianSystem where
  obj := cofreeSystem D i
  map := cofreeMap D i
  map_id A := by
    apply Subtype.ext
    funext j
    change (cofreeMap D i (𝟙 A)).val j = 𝟙 _
    rw [cofreeMap_val]
    simp only [Functor.map_id, Limits.Pi.map_id]
  map_comp h k := by
    apply Subtype.ext
    funext j
    change (cofreeMap D i (h ≫ k)).val j =
      (cofreeMap D i h).val j ≫ (cofreeMap D i k).val j
    simp [cofreeMap_val, Functor.map_comp, Limits.Pi.map_comp_map]

private def cofreeAdjunction (i : I) : D.abelianEvaluation i ⊣ cofreeFunctor D i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := cofreeHomEquiv D i
    homEquiv_naturality_left_symm := by
      intro X Y A h k
      change (h.val i ≫ k.val i) ≫ Pi.π _ (𝟙 i) ≫
          (D.abelianDirectId i).hom.app A =
        h.val i ≫ k.val i ≫ Pi.π _ (𝟙 i) ≫ (D.abelianDirectId i).hom.app A
      simp only [Category.assoc]
    homEquiv_naturality_right := by
      intro X A B h k
      apply Subtype.ext
      funext j
      apply Pi.hom_ext
      intro a
      change D.abelianCofreeExtension i X B (h ≫ k) j ≫ Pi.π _ a =
        (D.abelianCofreeExtension i X A h j ≫ (cofreeMap D i k).val j) ≫ Pi.π _ a
      rw [cofreeMap_val]
      simp only [abelianCofreeExtension, Category.assoc, Pi.map_π, Pi.lift_π,
        Pi.lift_π_assoc]
      simpa only [Category.assoc] using
        (D.abelianAdjunction a).homEquiv_naturality_right (X.transition a ≫ h) k }

/-- Evaluation on all compatible varying-site systems has the additive free and
cofree adjoints with exactly the displayed components, transitions and Hom formulas.
Source: Stacks 0EXZ (product construction) and 09WG (5)-(7) (free construction),
generalized to the stipulated small coherent diagram
(blueprint: lem-per-varying-site-evaluation-adjoints).

Proof: (1) Products of abelian sheaves are sectionwise; sheafifying sectionwise
presheaf sums gives their coproducts. These include the empty product and sum,
both zero. Left adjoints preserve the sums and right adjoints preserve products.
(2) Write Q_a for inverse image and P_a for direct image. Adjunction transposes
u to P_a(u) eta_a; naturality and the composite adjunction give the composite
transpose formula, with the canonical mate comparisons inserted.
(3) At j form the sum over a:j→i of Q_a A. For c:k→j its transition sends the
pulled-back a-summand to the ca-summand through the mate compositor. Coproduct
uniqueness and coherence give identities and cocycles. On morphisms use Q_a(h)
on each summand; this is an additive functor.
(4) A map h:A→X_i induces the map with a-summand Q_a(h) followed by phi_a.
The system cocycle proves compatibility; restriction to the identity summand
recovers h. Conversely compatibility with a recovers every summand of a system
map from its identity restriction. These constructions are natural.
(5) At j form the product over a:i→j of P_a A. For c:k→j define t_c:D_j→P_c D_k
using its b:i→k projection rho_(bc), transported by the direct-image compositor;
P_c preserves products, so this defines t_c uniquely. Its adjunct sigma_c has
the asserted projection formula by counit naturality.
(6) Test t_(dc)=P_c(t_d)t_c on every product projection. Both are the same
rho_(bdc), by coherence. Transposition proves the cocycle; identity projections
prove the identity law. (7) P_a(h) on factors defines the additive right functor.
(8) Transposing a system's transitions gives theta_a, satisfying the direct-image
cocycle. A component family q is compatible exactly when theta_c q_j=P_c(q_k)theta_c.
(9) Given h:X_i→A define q_j with a-projection P_a(h)theta_a, equivalently the
adjunct of phi_a followed by h. The theta cocycle proves compatibility.
(10) Projection to the identity factor recovers h by the identity comparison.
Conversely compatibility with a, projected onto its identity factor, recovers
every a-projection of q, including all nonidentity endomorphisms. Product uniqueness
proves the inverse identity. (11) The summand and factor formulas commute with
pre- and postcomposition, so the natural Hom bijections give both adjunctions.
Componentwise addition gives additivity of evaluation and of both adjoints.
Dependencies: sheafification-exact, presheaf-colimits-sectionwise, sheafification,
left-adjoint-preserves-colimits, right-adjoint-preserves-limits,
adjunction-of-natural-bijection, composite-adjunction and site-morphism-composition. -/
theorem varyingSite_evaluation_adjoints
    {I : Type u} [Category.{v} I]
    {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)
    [∀ (i j : I) (a : i ⟶ j), (D.abelianInverse a).Additive]
    [∀ (i j : I) (a : i ⟶ j), (D.abelianDirect a).Additive]
    (siteMorphism : ∀ {i j : I} (a : i ⟶ j),
      PreservesFiniteLimits (D.inverseImage a)) (i : I) :
    Nonempty (D.AbelianEvaluationAdjoints i) := by
  have _ := siteMorphism (𝟙 i)
  refine ⟨{
    left := freeFunctor D i
    right := cofreeFunctor D i
    left_additive := (freeAdjunction D i).left_adjoint_additive
    right_additive := (cofreeAdjunction D i).right_adjoint_additive
    leftAdjunction := freeAdjunction D i
    rightAdjunction := cofreeAdjunction D i
    leftComponent := fun _ _ ↦ Iso.refl _
    rightComponent := fun _ _ ↦ Iso.refl _
    left_naturality := ?_
    right_naturality := ?_
    left_transition := ?_
    right_transition := ?_
    left_hom := ?_
    left_hom_inverse := ?_
    right_hom := ?_
    right_hom_inverse := ?_ }⟩
  · intro A B h j
    simp [freeFunctor]
  · intro A B h j
    simp [cofreeFunctor, cofreeMap_val]
  · intro A j k c a
    simpa only [Iso.refl_inv, Category.comp_id, Functor.map_comp, Functor.map_id]
      using D.abelianFreeTransition_ι i A c a
  · intro A j k c b
    simpa only [Iso.refl_hom, Category.id_comp]
      using D.abelianCofreeTransition_π i A c b
  · intro A X h
    simp only [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      Iso.refl_inv, Category.id_comp]
    rfl
  · intro A X h j a
    simp only [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    simp [freeHomEquiv, freeExtension]
  · intro X A h
    simp only [cofreeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    simp [cofreeHomEquiv, cofreeRestriction]
  · intro X A h j a
    simp only [cofreeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    simp [cofreeHomEquiv, cofreeExtension, abelianCofreeExtension]

end CategoryTheory.CoherentSitePseudofunctor
