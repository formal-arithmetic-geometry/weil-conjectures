/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaOfCompactification
public import WeilConjectures.PoincareDuality.ProjectionRefinementAbstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!

# The projection formula of an open immersion

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

set_option profiler true in
/-- The inverse of the composition isomorphism of the trivial compactification `(j, 𝟙)` of an
open immersion is `Lj^*` of the identity isomorphism `L(𝟙 Y)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarCompactificationIso_ofIsOpenImmersion_inv_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsOpenImmersion j)).inv.app M =
      (L((j)^*⟦Λ⟧)).map ((leftDerivedUpperStarId Λ Y).hom.app M) := by
  have h := leftDerivedUpperStarComp_id_right_app Λ j M
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ j (𝟙 Y)).hom.app M), h]
  simp only [leftDerivedUpperStarCompactificationIso, Iso.trans_inv, NatTrans.comp_app,
    eqToIso.inv, eqToHom_app]
  exact Iso.hom_inv_id_app_assoc _ _ _

end General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

set_option profiler true in
/-- The inverse of the composition isomorphism of the trivial compactification `(j, 𝟙)` of an
open immersion is `Lj^*` of the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`. -/
lemma ι_map_upperStar_map_upperStarId_hom_app (B : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ (Compactification.ofIsOpenImmersion j.left).overI).map
        ((boundedConstructibleUpperStarId _ ℓ X).hom.app B)) =
      (leftDerivedUpperStarOverCompactificationIso _
        (Compactification.ofIsOpenImmersion j.left)).inv.app B.obj := by
  rw [leftDerivedUpperStarOverCompactificationIso,
    leftDerivedUpperStarCompactificationIso_ofIsOpenImmersion_inv_app,
    ← boundedConstructibleUpperStarId_hom_app_hom _ ℓ (X := X) B]
  rfl

set_option profiler true in
/-- **The projection formula of the trivial compactification** `(j, 𝟙)` of an open immersion:
through `R(𝟙 X)_* ≅ 𝟭`, the exceptional projection morphism followed by the projection comparison
of `j_! ⊣ Lj^*` is the identification. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion
    (K : Dᵇc(U.left)⟦𝐐⟧) (B : Dᵇc(X.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B))
        (exceptionalProjectionMorphismOfCompactification _
          (Compactification.ofIsOpenImmersion j.left) K.obj B.obj) ≫
      (boundedConstructibleLowerStarId ℓ X).hom.app _ ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          j).projectionComparison K B =
      (boundedConstructibleLowerStarId ℓ X).hom.app _ ▷ B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ _ K B _
    (ι_map_upperStar_map_upperStarId_hom_app ℓ j B)]
  exact Adjunction.trivial_exceptionalProjection_comp_projectionComparison _ _ _
    (fun X' Y' ↦ boundedConstructibleUpperStarId_hom_app_tensor_δ ℓ X X' Y') K B

end AlgebraicGeometry.ProEtale.CondensedRing
