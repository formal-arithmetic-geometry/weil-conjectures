/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp

/-!
# The composition isomorphisms of the derived pullbacks of bounded constructible complexes are
monoidal

The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`) commutes with the tensor comparisons
of the strong monoidal pullbacks
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_hom_app_tensor_δ`). It is the
restriction of the corresponding statement on the ambient derived categories
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_comp`).

The statements are proved once for a coefficient ring `Λ` that is a variable, and then
specialised to `ℚ̲̄_ℓ`: unifying them directly at the concrete ring unfolds the restricted
functors. The braiding statements are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalCompBraided`,
which this module imports.
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

/-! ### The statements for a general coefficient ring -/

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The monoidal structure of the restricted pullback, with the body of
`monoidal_boundedConstructibleUpperStar`, for a coefficient ring `Λ` whose bounded constructible
complexes form monoidal subcategories. -/
private noncomputable abbrev monoidalAux {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] [(boundedConstructible (condensedRingObj Λ X.left)).IsMonoidal]
    [(boundedConstructible (condensedRingObj Λ Y.left)).IsMonoidal] (f : X ⟶ Y) :
    (boundedConstructibleUpperStar Λ ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

/-- The braiding of `Dᵇc(T)⟦Λ⟧`, with the body of `boundedConstructibleBraiding`. -/
private noncomputable abbrev braidedAux (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    [(boundedConstructible (condensedRingObj Λ T.left)).IsMonoidal] :
    BraidedCategory (Dᵇc(T.left)⟦Λ⟧) :=
  ObjectProperty.fullBraidedSubcategory _

variable [(boundedConstructible (condensedRingObj Λ X.left)).IsMonoidal]
  [(boundedConstructible (condensedRingObj Λ Y.left)).IsMonoidal]
  [(boundedConstructible (condensedRingObj Λ Z.left)).IsMonoidal]

attribute [local instance] monoidalAux

private lemma δ_hom_aux (K M : Dᵇc(Y.left)⟦Λ⟧) :
    (δ (boundedConstructibleUpperStar Λ ℓ f) K M).hom =
      ((leftDerivedUpperStarTensor Λ f.left).app K.obj).app M.obj :=
  rfl

private lemma braiding_hom_hom_aux (K M : Dᵇc(X.left)⟦Λ⟧) :
    (@BraidedCategory.braiding _ _ _ (braidedAux Λ X) K M).hom.hom =
      (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K.obj M.obj).hom :=
  rfl

private lemma map_braiding_hom_δ_aux (K M : Dᵇc(Y.left)⟦Λ⟧) :
    letI := braidedAux Λ Y
    letI := braidedAux Λ X
    (boundedConstructibleUpperStar Λ ℓ f).map (β_ K M).hom ≫
        δ (boundedConstructibleUpperStar Λ ℓ f) M K =
      δ (boundedConstructibleUpperStar Λ ℓ f) K M ≫
        (β_ ((boundedConstructibleUpperStar Λ ℓ f).obj K)
          ((boundedConstructibleUpperStar Λ ℓ f).obj M)).hom := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  -- `rw` and not `simp`, and the braidings rewritten before `exact`: comparing the braiding of
  -- `Dᵇc(-)⟦Λ⟧` with that of `DerivedCategory.braidedCategory'` by unfolding is expensive for the
  -- kernel, see `braiding_hom_hom_aux`.
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    δ_hom_aux, δ_hom_aux, boundedConstructibleUpperStar_map_hom, braiding_hom_hom_aux,
    braiding_hom_hom_aux]
  exact leftDerivedUpperStarTensor_braiding Λ f.left K.obj M.obj

private lemma comp_tensor_δ_aux (K M : Dᵇc(Z.left)⟦Λ⟧) :
    δ (boundedConstructibleUpperStar Λ ℓ (f ≫ g)) K M ≫
        ((boundedConstructibleUpperStarComp Λ ℓ f g).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app M) =
      (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app (K ⊗ M) ≫
        (boundedConstructibleUpperStar Λ ℓ f).map (δ
            (boundedConstructibleUpperStar Λ ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar Λ ℓ f) _ _ := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_hom_aux, boundedConstructibleUpperStarComp_hom_app_hom, ObjectProperty.tensorHom_hom']
  have key := leftDerivedUpperStarTensor_comp_of_eq Λ f.left g.left
      (Over.comp_left _ _ _ f g)
    K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

private lemma id_tensor_δ_aux (K M : Dᵇc(X.left)⟦Λ⟧) :
    δ (boundedConstructibleUpperStar Λ ℓ (𝟙 X)) K M ≫
        ((boundedConstructibleUpperStarId Λ ℓ X).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarId Λ ℓ X).hom.app M) =
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app (K ⊗ M) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, δ_hom_aux,
    boundedConstructibleUpperStarId_hom_app_hom, ObjectProperty.tensorHom_hom']
  have key := leftDerivedUpperStarTensor_id_of_eq Λ X.left (Over.id_left X) K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

end General

/-! ### The coefficient ring `ℚ̲̄_ℓ` -/

-- `with_reducible_and_instances`: the statement for a general `Λ` agrees with the goal up to the
-- instances of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` and of `Lf^*`; at the default transparency the unifier unfolds the
-- restricted `ℚ̲̄_ℓ`-functors instead.
lemma δ_boundedConstructibleUpperStar_hom (K M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M).hom =
      ((leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj ℓ) f.left).app K.obj).app
        M.obj := by
  have h := δ_hom_aux ℓ f (Λ := Profinite.padicAlgClRingObj ℓ) K M
  with_reducible_and_instances exact h

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
  have h := comp_tensor_δ_aux ℓ f g (Λ := Profinite.padicAlgClRingObj ℓ) K M
  exact h

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

omit [IsSeparated X.hom] in
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
