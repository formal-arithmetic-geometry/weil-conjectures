/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided

/-!
# The composition isomorphisms of the derived pullbacks of bounded constructible complexes are
monoidal

The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`) commutes with the tensor comparisons
of the strong monoidal pullbacks
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_hom_app_tensor_δ`). It is the
restriction of the corresponding statement on the ambient derived categories
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory

lemma eqToHom_comp_of_self {C : Type*} [Category C] {A B : C} (p : A = A) (x : A ⟶ B) :
    eqToHom p ≫ x = x := by
  simp

end CategoryTheory

namespace CategoryTheory.ObjectProperty

lemma tensorHom_hom' {C : Type*} [Category C] [MonoidalCategory C] {P : ObjectProperty C}
    [P.IsMonoidal] {A B A' B' : P.FullSubcategory} (a : A ⟶ A') (b : B ⟶ B') :
    (a ⊗ₘ b).hom = a.hom ⊗ₘ b.hom :=
  rfl

end CategoryTheory.ObjectProperty

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)

set_option maxHeartbeats 1000000 in
-- comparing the tensor comparisons unfolds the restricted `ℚ̲̄_ℓ`-functors, which is expensive
lemma δ_boundedConstructibleUpperStar_hom (K M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M).hom =
      ((leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj ℓ) f.left).app K.obj).app M.obj :=
  rfl

set_option maxHeartbeats 1000000 in
-- `(f ≫ g).left` is unfolded to `f.left ≫ g.left`
/-- **The composition isomorphism of the derived pullbacks of bounded constructible complexes is
monoidal**: it commutes with the tensor comparisons. -/
lemma boundedConstructibleUpperStarComp_hom_app_tensor_δ (K M :
    Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)) K M ≫
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app M) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app (K ⊗ M) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (δ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) _ _ := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_boundedConstructibleUpperStar_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    ObjectProperty.tensorHom_hom']
  have key := leftDerivedUpperStarTensor_comp_of_eq (Profinite.padicAlgClRingObj ℓ) f.left g.left
      (Over.comp_left _ _ _ f g)
    K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

set_option maxHeartbeats 1000000 in
-- comparing the tensor comparisons unfolds the restricted `ℚ̲̄_ℓ`-functors, which is expensive
variable (X) in
/-- **The identity isomorphism of the derived pullback of bounded constructible complexes is
monoidal**: `L(𝟙 X)^*(K ⊗ M) ⟶ L(𝟙 X)^* K ⊗ L(𝟙 X)^* M ⟶ K ⊗ M` is the identity isomorphism. -/
lemma boundedConstructibleUpperStarId_hom_app_tensor_δ (K M :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)) K M ≫
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app M) =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app (K ⊗ M) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, δ_boundedConstructibleUpperStar_hom,
    boundedConstructibleUpperStarId_hom_app_hom, ObjectProperty.tensorHom_hom']
  have key := leftDerivedUpperStarTensor_id_of_eq (Profinite.padicAlgClRingObj ℓ) X.left
      (Over.id_left X) K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

section Braided

attribute [local instance] boundedConstructibleBraiding

lemma boundedConstructible_braiding_hom_hom (K M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β_ K M).hom.hom =
      (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K.obj M.obj).hom :=
  rfl

set_option maxHeartbeats 1000000 in
-- comparing the tensor comparisons unfolds the restricted `ℚ̲̄_ℓ`-functors, which is expensive
/-- **The derived pullback of bounded constructible complexes is braided** for the Koszul
braidings: `Lf^* β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{Lf^* K, Lf^* M}`. -/
lemma boundedConstructibleUpperStar_map_braiding_hom_δ (K M :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (β_ K M).hom ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) M K =
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M ≫
        (β_ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).hom := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, δ_boundedConstructibleUpperStar_hom,
    boundedConstructibleUpperStar_map_hom, boundedConstructible_braiding_hom_hom]
  exact leftDerivedUpperStarTensor_braiding (Profinite.padicAlgClRingObj ℓ) f.left K.obj M.obj

end Braided

end AlgebraicGeometry.ProEtale.CondensedRing
