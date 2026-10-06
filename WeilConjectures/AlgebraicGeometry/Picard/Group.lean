/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The group law on the Picard group

The Picard group `Pic Y` of a scheme `Y` is a commutative group under the tensor product of
invertible modules: the unit is the class of `𝒪_Y`, the inverse of the class of `ℒ` is the class
of its dual `ℒᵛ`, and pulling back along a morphism of schemes is a group homomorphism.

For a morphism `f : X ⟶ S` with a section `σ`, the `σ`-normalized Picard functor `Pic_{X/S,σ}` is
the kernel of `σ_T^* : Pic (X_T) ⟶ Pic T`, so it is a presheaf of groups; this is
`AlgebraicGeometry.picardFunctorNormalizedGrp`, whose underlying presheaf of sets is
`AlgebraicGeometry.picardFunctorNormalized`.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic.instCommGroup`: the group law on `Pic Y`.
- `AlgebraicGeometry.Scheme.Pic.mapHom`: the pullback `Pic Y →* Pic X` along `X ⟶ Y`.
- `AlgebraicGeometry.picardFunctorNormalizedGrp`: the `σ`-normalized Picard functor as a presheaf
  of groups (blueprint `rem-pc-group-structure`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Pic

variable {X Y : Scheme.{u}}

/-- The chosen representative of a class in the Picard group is invertible. -/
instance isInvertible_fromSkeleton (L : Y.Pic) :
    Modules.IsInvertible ((fromSkeleton Y.Modules).obj L.val) :=
  have := L.isInvertible
  Modules.IsInvertible.of_sheafOfModules _

/-- The class of a module which is invertible in the sense of
`AlgebraicGeometry.Scheme.Modules.IsInvertible`. -/
noncomputable def ofIsInvertible (M : Y.Modules) [Modules.IsInvertible M] : Y.Pic :=
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  mk M

/-- The representative of `ofIsInvertible M` is isomorphic to `M`. -/
noncomputable def ofIsInvertibleIso (M : Y.Modules) [Modules.IsInvertible M] :
    (fromSkeleton Y.Modules).obj (ofIsInvertible M).val ≅ M :=
  fromSkeletonToSkeletonIso M

/-- A class is `ofIsInvertible M` if and only if its representative is isomorphic to `M`. -/
lemma eq_ofIsInvertible_iff (L : Y.Pic) (M : Y.Modules) [Modules.IsInvertible M] :
    L = ofIsInvertible M ↔ Nonempty ((fromSkeleton Y.Modules).obj L.val ≅ M) :=
  eq_iff_nonempty_iso.trans
    ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ ofIsInvertibleIso M⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ (ofIsInvertibleIso M).symm⟩⟩

noncomputable instance : One Y.Pic :=
  ⟨ofIsInvertible (𝟙_ Y.Modules)⟩

noncomputable instance : Mul Y.Pic :=
  ⟨fun L L' ↦ ofIsInvertible
    ((fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val)⟩

noncomputable instance : Inv Y.Pic :=
  ⟨fun L ↦ ofIsInvertible ((fromSkeleton Y.Modules).obj L.val)ᵛ⟩

lemma one_def : (1 : Y.Pic) = ofIsInvertible (𝟙_ Y.Modules) :=
  rfl

lemma mul_def (L L' : Y.Pic) : L * L' =
    ofIsInvertible ((fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val) :=
  rfl

lemma inv_def (L : Y.Pic) : L⁻¹ = ofIsInvertible ((fromSkeleton Y.Modules).obj L.val)ᵛ :=
  rfl

/-- The unit of the Picard group is the class of the structure sheaf. -/
lemma one_eq_mk_unit : (1 : Y.Pic) = mk (SheafOfModules.unit Y.ringCatSheaf) :=
  rfl

/-- The representative of `L * L'` is the tensor product of the representatives. -/
noncomputable def mulIso (L L' : Y.Pic) :
    (fromSkeleton Y.Modules).obj (L * L').val ≅
      (fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val :=
  ofIsInvertibleIso _

/-- The representative of `1` is the structure sheaf. -/
noncomputable def oneIso : (fromSkeleton Y.Modules).obj (1 : Y.Pic).val ≅ 𝟙_ Y.Modules :=
  ofIsInvertibleIso _

/-- **The group law on the Picard group**, induced by the tensor product of invertible modules.
The inverse of a class is the class of the dual module. -/
noncomputable instance instCommGroup : CommGroup Y.Pic where
  mul_assoc L L' L'' := by
    refine eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerRightIso (mulIso _ _) _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (mulIso _ _).symm ≪≫ (mulIso _ _).symm⟩
  one_mul L := by
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerRightIso oneIso _ ≪≫ λ_ _⟩
  mul_one L := by
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerLeftIso _ oneIso ≪≫ ρ_ _⟩
  inv_mul_cancel L := by
    obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit ((fromSkeleton Y.Modules).obj L.val)
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerRightIso (ofIsInvertibleIso _) _ ≪≫ β_ _ _ ≪≫ d ≪≫ oneIso.symm⟩
  mul_comm L L' := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ β_ _ _ ≪≫ (mulIso _ _).symm⟩

/-- Pulling back along `g` commutes with the tensor product of invertible modules. -/
lemma map_mul (g : X ⟶ Y) (L L' : Y.Pic) : map g (L * L') = map g L * map g L' := by
  obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso g ((fromSkeleton Y.Modules).obj L.val)
    ((fromSkeleton Y.Modules).obj L'.val)
  exact eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Modules.pullback g).mapIso (mulIso L L') ≪≫ t ≪≫
    ((fromSkeletonToSkeletonIso _).symm ⊗ᵢ (fromSkeletonToSkeletonIso _).symm) ≪≫
    (mulIso (map g L) (map g L')).symm⟩

lemma map_one (g : X ⟶ Y) : map g (1 : Y.Pic) = 1 :=
  map_mk_unit g

/-- The pullback `g^* : Pic Y →* Pic X` along a morphism of schemes `g : X ⟶ Y`, as a group
homomorphism. -/
noncomputable def mapHom (g : X ⟶ Y) : Y.Pic →* X.Pic :=
  MonoidHom.mk' (map g) (map_mul g)

@[simp]
lemma mapHom_apply (g : X ⟶ Y) (L : Y.Pic) : mapHom g L = map g L :=
  rfl

end Scheme.Pic

variable {X S : Scheme.{u}}

/-- **The `σ`-normalized Picard functor is a presheaf of groups.** For `f : X ⟶ S` with a
section `σ`, the `σ`-normalized classes form the kernel of the group homomorphism
`σ_T^* : Pic (X_T) ⟶ Pic T`, and pulling back along `X_{T'} ⟶ X_T` is a group homomorphism.
The underlying presheaf of sets is `AlgebraicGeometry.picardFunctorNormalized`
(`AlgebraicGeometry.picardFunctorNormalizedGrp_comp_forget`).

The group law is the tensor product of invertible modules; it is what gives the scheme
representing the Picard functor its group scheme structure.

(blueprint: `rem-pc-group-structure`) -/
noncomputable def picardFunctorNormalizedGrp (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (Pic.mapHom (sectionBaseChange f σ hσ T.unop)).ker
  map φ := GrpCat.ofHom
    { toFun L := ⟨Pic.map (baseChangeMap f φ.unop) L.1,
        (picardFunctorNormalized f σ hσ).map φ L.2⟩
      map_one' := Subtype.ext (Pic.map_one _)
      map_mul' L L' := Subtype.ext (Pic.map_mul _ L.1 L'.1) }
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (𝟙 T).unop) L.1 = L.1
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (φ ≫ ψ).unop) L.1 =
      Pic.map (baseChangeMap f ψ.unop) (Pic.map (baseChangeMap f φ.unop) L.1)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- The underlying presheaf of sets of `picardFunctorNormalizedGrp` is
`picardFunctorNormalized`. -/
lemma picardFunctorNormalizedGrp_comp_forget (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{u + 1} =
      (picardFunctorNormalized f σ hσ).toFunctor :=
  rfl

end AlgebraicGeometry
