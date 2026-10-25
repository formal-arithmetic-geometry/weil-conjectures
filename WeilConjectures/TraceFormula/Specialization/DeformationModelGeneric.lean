/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.TraceFormula.Specialization.ZeroSection

/-!

# The geometric generic fibre of the deformation to the normal cone of a point

Let `x` be a rational point of a `k`-scheme `X` and let `𝒳 = D_x X ×_{𝔸¹_k} Spec k'⟦t⟧` be the
deformation to the normal cone of `x` over the trait (`ProEtale.CondensedRing.deformationModel`).
Over the punctured line `𝔾_m ⊆ 𝔸¹_k` the deformation space is `X × 𝔾_m`
(`Scheme.Hom.isPullback_deformationSpaceGeneric`), and the geometric generic point
`Spec Ω ⟶ Spec k'⟦t⟧ ⟶ 𝔸¹_k` lands in `𝔾_m`, since `t` is invertible in `Ω`. Hence the geometric
generic fibre of `𝒳` is the base change `X_Ω = X ×_k Spec Ω` of `X` along `Spec Ω ⟶ Spec k`, with
`ε : 𝒳_Ω ⟶ X` the first projection
(`ProEtale.CondensedRing.isPullback_deformationModel_ε`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The geometric generic point `Spec Ω ⟶ Spec k'⟦t⟧ ⟶ 𝔸¹_k` lies in the punctured line: the
coordinate `t` is a nonzero element of the field `Ω`. -/
noncomputable def traitGenericPointToPuncturedLine :
    Spec (.of (traitGenericField k')) ⟶ Scheme.Hom.puncturedLine (Spec (.of k)) :=
  IsOpenImmersion.lift (Scheme.Hom.puncturedLine (Spec (.of k))).ι
    (traitGenericPoint k' ≫ traitToAffineLine k k') (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      change y ∈ (traitGenericPoint k' ≫ traitToAffineLine k k') ⁻¹ᵁ
        Scheme.Hom.puncturedLine (Spec (.of k))
      rw [Scheme.preimage_basicOpen_top, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        traitToAffineLine, AffineSpace.homOfVector_appTop_coord, traitGenericPoint,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
        Scheme.basicOpen_of_isUnit]
      · trivial
      refine IsUnit.map _ (Ne.isUnit ?_)
      change algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X ≠ 0
      rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
      refine (map_ne_zero _).2 ?_
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero)))

@[reassoc (attr := simp)]
lemma traitGenericPointToPuncturedLine_ι :
    traitGenericPointToPuncturedLine k k' ≫ (Scheme.Hom.puncturedLine (Spec (.of k))).ι =
      traitGenericPoint k' ≫ traitToAffineLine k k' :=
  IsOpenImmersion.lift_fac _ _ _

namespace ProEtale.CondensedRing

variable {k} {X : Over (Spec (.of k))} (x : RationalPoint X)

/-- The structure morphism `𝒳_Ω ⟶ Spec Ω` of the geometric generic fibre of the deformation to
the normal cone over the trait. -/
noncomputable def deformationGenericToPoint (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
    (k' : Type u) [Field k'] [Algebra k k'] :
    deformationGeneric X I k' ⟶ Spec (.of (traitGenericField k')) :=
  pullback.snd _ _

/-- **The geometric generic fibre of the deformation to the normal cone of a point is the base
change of `X`**: the square formed by `ε : 𝒳_Ω ⟶ X`, the structure morphisms `𝒳_Ω ⟶ Spec Ω` and
`X ⟶ Spec k`, and `Spec Ω ⟶ Spec k'⟦t⟧ ⟶ Spec k`, is a pullback. -/
theorem isPullback_deformationModel_ε :
    IsPullback (deformationModel X x.left.ker k').ε
      (deformationGenericToPoint X x.left.ker k') X.hom
      (traitGenericPoint k' ≫ traitToBase k k') := by
  -- the generic fibre is the pullback of `D_x X ⟶ 𝔸¹_k` along `Spec Ω ⟶ 𝔸¹_k`
  have h₁ : IsPullback (deformationGenericToTotal X x.left.ker k' ≫
      deformationTotalToSpace X x.left.ker k')
      (deformationGenericToPoint X x.left.ker k')
      (Scheme.Hom.deformationSpaceProj X.hom x.left)
      (traitGenericPoint k' ≫ traitToAffineLine k k') :=
    (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_deformationTotal X x.left.ker k')
  have h₂ := Scheme.Hom.isPullback_deformationSpaceGeneric X.hom x.left
  -- it factors through the punctured trivialisation `X × 𝔾_m`
  have h₃ : IsPullback (h₂.lift (deformationGenericToTotal X x.left.ker k' ≫
      deformationTotalToSpace X x.left.ker k')
      (deformationGenericToPoint X x.left.ker k' ≫
        traitGenericPointToPuncturedLine k k') (by
          simpa using h₁.w))
      (deformationGenericToPoint X x.left.ker k')
      (pullback.snd _ _) (traitGenericPointToPuncturedLine k k') := by
    refine IsPullback.of_right ?_ (h₂.lift_snd _ _ _) h₂
    rw [h₂.lift_fst, traitGenericPointToPuncturedLine_ι]
    exact h₁
  have h₄ := h₃.paste_horiz (IsPullback.of_hasPullback X.hom
    ((Scheme.Hom.puncturedLine (Spec (.of k))).ι ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘
      Spec (.of k)))
  have key : ∀ {a a' : deformationGeneric X x.left.ker k' ⟶ X.left}
      {b b' : Spec (.of (traitGenericField k')) ⟶ Spec (.of k)}, a = a' → b = b' →
      IsPullback a (deformationGenericToPoint X x.left.ker k') X.hom b →
      IsPullback a' (deformationGenericToPoint X x.left.ker k') X.hom b' := by
    rintro _ _ _ _ rfl rfl h
    exact h
  refine key ?_ ?_ h₄
  · change _ = deformationGenericToTotal X x.left.ker k' ≫ deformationTotalToBase X x.left.ker k'
    rw [← Scheme.Hom.deformationSpaceGeneric_toBase, h₂.lift_fst_assoc, deformationTotalToBase,
      Category.assoc]
  · rw [traitGenericPointToPuncturedLine_ι_assoc, traitToAffineLine_over]

end ProEtale.CondensedRing

end AlgebraicGeometry
