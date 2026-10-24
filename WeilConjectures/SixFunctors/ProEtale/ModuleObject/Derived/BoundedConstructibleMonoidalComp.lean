/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

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

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsEllAdicFinitenessCoefficient ℓ Λ]
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)

lemma δ_boundedConstructibleUpperStar_hom (K M : Dᵇc(Y.left)⟦Λ⟧) :
    (δ (boundedConstructibleUpperStar Λ ℓ f) K M).hom =
      ((leftDerivedUpperStarTensor Λ f.left).app K.obj).app M.obj :=
  rfl

set_option maxHeartbeats 1000000 in
-- `(f ≫ g).left` is unfolded to `f.left ≫ g.left`
/-- **The composition isomorphism of the derived pullbacks of bounded constructible complexes is
monoidal**: it commutes with the tensor comparisons. -/
lemma boundedConstructibleUpperStarComp_hom_app_tensor_δ (K M : Dᵇc(Z.left)⟦Λ⟧) :
    δ (boundedConstructibleUpperStar Λ ℓ (f ≫ g)) K M ≫
        ((boundedConstructibleUpperStarComp Λ ℓ f g).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app M) =
      (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app (K ⊗ M) ≫
        (boundedConstructibleUpperStar Λ ℓ f).map (δ (boundedConstructibleUpperStar Λ ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar Λ ℓ f) _ _ := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_boundedConstructibleUpperStar_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    ObjectProperty.tensorHom_hom']
  have key := leftDerivedUpperStarTensor_comp_of_eq Λ f.left g.left (Over.comp_left _ _ _ f g)
    K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing
