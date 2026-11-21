/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProfiniteCoefficientCohomology

/-!
# The pro-étale sheaf of continuous maps to a finite product

For a scheme `S` and a topological abelian group `A`, the pro-étale sheaf `C(-, ι → A)` is the
product of `ι` copies of `C(-, A)`. Hence, for `ι` finite, its cohomology is the product of `ι`
copies of the cohomology of `C(-, A)`. We also show that `C(-, A)` only depends on `A` up to
isomorphism of topological groups.

## Main statements

- `AlgebraicGeometry.ProEtale.continuousSheafMapIso`: the isomorphism `C(-, A) ≅ C(-, B)`
  induced by an isomorphism `A ≃ₜ+ B` of topological groups.
- `AlgebraicGeometry.ProEtale.isLimitContinuousSheafFan`: `C(-, ι → A)` is the product of the
  sheaves `C(-, A)`.
- `AlgebraicGeometry.ProEtale.continuousSheafPiHAddEquiv`:
  `Hⁿ(S_proét, C(-, ι → A)) ≃+ (ι → Hⁿ(S_proét, C(-, A)))` for `ι` finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (S : Scheme.{u}) {A B : Type} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- The isomorphism of sheaves `C(-, A) ≅ C(-, B)` on `S_proét` induced by an isomorphism of
topological groups `A ≃ₜ+ B`. -/
@[simps]
noncomputable def continuousSheafMapIso (e : A ≃ₜ+ B) :
    continuousSheaf S A ≅ continuousSheaf S B where
  hom := continuousSheafMap S (e : ContinuousAddMonoidHom A B)
  inv := continuousSheafMap S (e.symm : ContinuousAddMonoidHom B A)
  hom_inv_id := by
    ext V x
    exact congrArg ULift.up (ContinuousMap.ext fun t ↦ e.symm_apply_apply _)
  inv_hom_id := by
    ext V x
    exact congrArg ULift.up (ContinuousMap.ext fun t ↦ e.apply_symm_apply _)

/-- The fan `C(-, ι → A) ⟶ C(-, A)` given by the projections. -/
noncomputable def continuousSheafFan (ι : Type) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : Fan fun _ : ι ↦ continuousSheaf S A :=
  Fan.mk (continuousSheaf S (ι → A)) fun i ↦
    continuousSheafMap S ⟨Pi.evalAddMonoidHom (fun _ ↦ A) i, continuous_apply i⟩

/-- **`C(-, ι → A)` is the product of the `C(-, A)`**: a continuous map to `ι → A` is a family of
continuous maps to `A`. -/
noncomputable def isLimitContinuousSheafFan (ι : Type) (A : Type) [TopologicalSpace A]
    [AddCommGroup A] [IsTopologicalAddGroup A] : IsLimit (continuousSheafFan S ι A) := by
  refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun V ↦ ?_)
  refine isLimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1}) ?_
  refine Classical.choice ((Types.isLimit_iff _).2 fun s _ ↦ ?_)
  let g (i : ι) : C(V.unop.left, A) := (s ⟨i⟩ : ULift.{u + 1} C(V.unop.left, A)).down
  refine ⟨ULift.up (ContinuousMap.pi g), fun ⟨i⟩ ↦ rfl, fun x hx ↦ ?_⟩
  refine congrArg ULift.up (ContinuousMap.ext fun t ↦ funext fun i ↦ ?_)
  exact congrArg (fun y : ULift.{u + 1} C(V.unop.left, A) ↦ y.down t) (hx ⟨i⟩)

/-- **Cohomology of `C(-, ι → A)`**: for `ι` finite, `Hⁿ(S_proét, C(-, ι → A))` is the product of
`ι` copies of `Hⁿ(S_proét, C(-, A))`, via the maps induced by the projections. -/
noncomputable def continuousSheafPiHAddEquiv {ι : Type} [Finite ι] (n : ℕ) :
    Sheaf.H (continuousSheaf S (ι → A)) n ≃+ (ι → Sheaf.H (continuousSheaf S A) n) :=
  have := Abelian.hasFiniteBiproducts
    (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  AddEquiv.ofBijective
    (AddMonoidHom.pi fun i ↦
      Sheaf.H.map
        (continuousSheafMap S ⟨Pi.evalAddMonoidHom (fun _ ↦ A) i, continuous_apply i⟩) n)
    (Abelian.Ext.bijective_comp_mk₀_proj _ (isLimitContinuousSheafFan S ι A) n)

/-- The `i`-th component of `continuousSheafPiHAddEquiv` is induced by the `i`-th projection. -/
lemma continuousSheafPiHAddEquiv_apply {ι : Type} [Finite ι] (n : ℕ)
    (x : Sheaf.H (continuousSheaf S (ι → A)) n) (i : ι) :
    continuousSheafPiHAddEquiv S n x i =
      Sheaf.H.map
        (continuousSheafMap S ⟨Pi.evalAddMonoidHom (fun _ ↦ A) i, continuous_apply i⟩) n x :=
  rfl

end AlgebraicGeometry.ProEtale
