/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Infinitesimal points with values in a scheme

Let `G` be a group scheme over `S` and `X` a scheme over `S`. The thickening `X[ε]` is a scheme
over `S` through `X[ε] ⟶ X ⟶ S` (`AlgebraicGeometry.overDualNumbers`). The *infinitesimal points
of `G` with values in `X`* are the points `v : X[ε] ⟶ G` over `S` with `v|_X = 1`
(`AlgebraicGeometry.GrpObj.infPointsAt`); for `X = S` these are the infinitesimal points of `G`.
They are functorial in `X`, carry the rescalings `ε ↦ cε` by global functions `c` of `X`, and the
`X`-points `x` of `G` act on them by conjugation `v ↦ x v x⁻¹`: this is the adjoint action of `G`
on `Lie(G) ⊗ Γ(X, 𝒪_X)`.

Over a field `k`, a tangent vector `y ∈ Lie(G)` gives the infinitesimal point
`y_X : X[ε] ⟶ (Spec k)[ε] ⟶ G` with values in any `k`-scheme `X`
(`AlgebraicGeometry.GrpObj.lieAt`); `y ↦ y_X` turns addition into the group law and scalars
`c ∈ k` into rescalings.

## Main definitions

- `AlgebraicGeometry.overDualNumbers`: the thickening `X[ε]` of a scheme `X` over `S`, as a
  scheme over `S`, with `overDualNumbersι`, `overDualNumbersProj`, `overDualNumbersMap`,
  `overDualNumbersScale` and `overDualNumbersFold`.
- `AlgebraicGeometry.GrpObj.infPointsAt`: the infinitesimal points of `G` with values in `X`.
- `AlgebraicGeometry.GrpObj.infPointsAtMap`, `AlgebraicGeometry.GrpObj.infPointsAtScale`,
  `AlgebraicGeometry.GrpObj.infPointsAtConj`: base change, rescaling and conjugation.
- `AlgebraicGeometry.GrpObj.lieAt`: the infinitesimal point `y_X` of a tangent vector `y`.

## Blueprint

- `sk-p-comparison`: the adjoint representation, through its action on infinitesimal points.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### The thickening of a scheme over a base -/

section OverDualNumbers

variable {S : Scheme.{u}} (X : Over S)

/-- The thickening `X[ε]` of a scheme `X` over `S`, as a scheme over `S` through
`X[ε] ⟶ X ⟶ S`. -/
noncomputable def overDualNumbers : Over S :=
  Over.mk (X.left.dualNumbersProj ≫ X.hom)

@[simp]
theorem overDualNumbers_left : (overDualNumbers X).left = X.left.dualNumbers :=
  rfl

@[simp]
theorem overDualNumbers_hom : (overDualNumbers X).hom = X.left.dualNumbersProj ≫ X.hom :=
  rfl

/-- The closed immersion `X ⟶ X[ε]`, `ε ↦ 0`, over `S`. -/
noncomputable def overDualNumbersι : X ⟶ overDualNumbers X :=
  Over.homMk X.left.dualNumbersι (by simp)

/-- The projection `X[ε] ⟶ X` over `S`. -/
noncomputable def overDualNumbersProj : overDualNumbers X ⟶ X :=
  Over.homMk X.left.dualNumbersProj rfl

/-- Rescaling the infinitesimal `ε ↦ cε` by a global function `c` of `X`, over `S`. -/
noncomputable def overDualNumbersScale (c : Γ(X.left, ⊤)) :
    overDualNumbers X ⟶ overDualNumbers X :=
  Over.homMk (X.left.dualNumbersScale c) (by simp)

/-- The map `X[ε] ⟶ X[ε][δ]`, `ε, δ ↦ ε`, over `S`. -/
noncomputable def overDualNumbersFold : overDualNumbers X ⟶ overDualNumbers (overDualNumbers X) :=
  Over.homMk X.left.dualNumbersFold (by simp)

variable {X} in
/-- The thickening `X[ε] ⟶ Y[ε]` of a morphism `φ : X ⟶ Y` over `S`. -/
noncomputable def overDualNumbersMap {Y : Over S} (φ : X ⟶ Y) :
    overDualNumbers X ⟶ overDualNumbers Y :=
  Over.homMk φ.left.dualNumbers (by simp [Over.w φ])

@[simp]
theorem overDualNumbersι_left : (overDualNumbersι X).left = X.left.dualNumbersι :=
  rfl

@[simp]
theorem overDualNumbersProj_left : (overDualNumbersProj X).left = X.left.dualNumbersProj :=
  rfl

@[simp]
theorem overDualNumbersScale_left (c : Γ(X.left, ⊤)) :
    (overDualNumbersScale X c).left = X.left.dualNumbersScale c :=
  rfl

@[simp]
theorem overDualNumbersFold_left : (overDualNumbersFold X).left = X.left.dualNumbersFold :=
  rfl

@[simp]
theorem overDualNumbersMap_left {Y : Over S} (φ : X ⟶ Y) :
    (overDualNumbersMap φ).left = φ.left.dualNumbers :=
  rfl

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_proj : overDualNumbersι X ≫ overDualNumbersProj X = 𝟙 X := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_map {Y : Over S} (φ : X ⟶ Y) :
    overDualNumbersι X ≫ overDualNumbersMap φ = φ ≫ overDualNumbersι Y := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_scale (c : Γ(X.left, ⊤)) :
    overDualNumbersι X ≫ overDualNumbersScale X c = overDualNumbersι X := by
  ext1
  simp

end OverDualNumbers

/-! ### Infinitesimal points with values in a scheme -/

namespace GrpObj

section InfPointsAt

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (X : Over S)

/-- The infinitesimal points of a group scheme `G` over `S` with values in a scheme `X` over `S`:
the points `v : X[ε] ⟶ G` over `S` with `v|_X = 1`, the kernel of `G(X[ε]) → G(X)`.
(blueprint: `sk-p-comparison`) -/
noncomputable def infPointsAt : Subgroup (overDualNumbers X ⟶ G) :=
  (pointsPrecomp G (overDualNumbersι X)).ker

variable {G X}

theorem mem_infPointsAt {v : overDualNumbers X ⟶ G} :
    v ∈ infPointsAt G X ↔ overDualNumbersι X ≫ v = 1 :=
  MonoidHom.mem_ker

theorem ι_comp_infPointsAt (v : infPointsAt G X) : overDualNumbersι X ≫ v.1 = 1 :=
  mem_infPointsAt.1 v.2

/-- Base change of infinitesimal points along a morphism `φ : Y ⟶ X` over `S`: `v ↦ φ[ε] ≫ v`. -/
noncomputable def infPointsAtMap {Y : Over S} (φ : Y ⟶ X) : infPointsAt G X →* infPointsAt G Y :=
  ((pointsPrecomp G (overDualNumbersMap φ)).comp (infPointsAt G X).subtype).codRestrict _
    fun v ↦ by
      rw [mem_infPointsAt, MonoidHom.comp_apply, pointsPrecomp_apply,
        overDualNumbersι_comp_map_assoc, Subgroup.coe_subtype, ι_comp_infPointsAt,
        MonObj.comp_one]

@[simp]
theorem coe_infPointsAtMap {Y : Over S} (φ : Y ⟶ X) (v : infPointsAt G X) :
    (infPointsAtMap φ v : overDualNumbers Y ⟶ G) = overDualNumbersMap φ ≫ v.1 :=
  rfl

variable (X) in
/-- The rescaling `v ↦ v(cε)` of infinitesimal points by a global function `c` of `X`. -/
noncomputable def infPointsAtScale (c : Γ(X.left, ⊤)) : infPointsAt G X →* infPointsAt G X :=
  ((pointsPrecomp G (overDualNumbersScale X c)).comp (infPointsAt G X).subtype).codRestrict _
    fun v ↦ by
      rw [mem_infPointsAt, MonoidHom.comp_apply, pointsPrecomp_apply,
        overDualNumbersι_comp_scale_assoc, Subgroup.coe_subtype, ι_comp_infPointsAt]

@[simp]
theorem coe_infPointsAtScale (c : Γ(X.left, ⊤)) (v : infPointsAt G X) :
    (infPointsAtScale X c v : overDualNumbers X ⟶ G) = overDualNumbersScale X c ≫ v.1 :=
  rfl

/-- The conjugation `v ↦ x v x⁻¹` of infinitesimal points with values in `X` by an `X`-point `x`
of `G`, pulled back to `X[ε]`. This is the adjoint action of `x` on `Lie(G) ⊗ Γ(X, 𝒪_X)`.
(blueprint: `sk-p-comparison`) -/
noncomputable def infPointsAtConj (x : X ⟶ G) : infPointsAt G X →* infPointsAt G X where
  toFun v := ⟨(overDualNumbersProj X ≫ x) * v.1 * (overDualNumbersProj X ≫ x)⁻¹, by
    rw [mem_infPointsAt, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      overDualNumbersι_comp_proj_assoc, ι_comp_infPointsAt, mul_one, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp]
theorem coe_infPointsAtConj (x : X ⟶ G) (v : infPointsAt G X) :
    (infPointsAtConj x v : overDualNumbers X ⟶ G) =
      (overDualNumbersProj X ≫ x) * v.1 * (overDualNumbersProj X ≫ x)⁻¹ :=
  rfl

end InfPointsAt

/-! ### Tangent vectors as infinitesimal points with values in a scheme -/

section LieAt

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

/-- The map `X[ε] ⟶ (Spec k)[ε] ≅ Spec k[ε]` over `k` of a scheme `X` over `k`. -/
noncomputable def overDualNumbersToSpec (X : Over (Spec (.of k))) :
    overDualNumbers X ⟶ (Spec (.of (DualNumber k))).asOver (Spec (.of k)) :=
  Over.homMk (X.hom.dualNumbers ≫ Scheme.dualNumbersToSpec (.of k))
    ((Category.assoc _ _ _).trans ((congrArg (X.hom.dualNumbers ≫ ·)
      (Scheme.dualNumbersToSpec_comp_specMap (.of k))).trans
        (Scheme.Hom.dualNumbers_comp_proj X.hom)))

theorem overDualNumbersι_comp_toSpec (X : Over (Spec (.of k))) :
    overDualNumbersι X ≫ overDualNumbersToSpec X =
      CartesianMonoidalCategory.toUnit X ≫ Scheme.dualNumbersιOver (Spec (.of k)) ≫
        dualNumbersToSpecOver := by
  ext1
  simp [overDualNumbersToSpec, dualNumbersToSpecOver, Over.toUnit_left]

variable (X : Over (Spec (.of k)))

theorem overDualNumbersToSpec_comp_tangentPoint_mem (y : Lie G) :
    overDualNumbersToSpec X ≫ tangentPoint y ∈ infPointsAt G X := by
  rw [mem_infPointsAt, ← Category.assoc, overDualNumbersι_comp_toSpec, Category.assoc,
    Category.assoc, (mem_infPoints G).1
      (dualNumbersToSpecOver_comp_mem_infPoints G (tangentPoint_mem_tangentGroup y)),
    MonObj.comp_one]

/-- The infinitesimal point `y_X : X[ε] ⟶ (Spec k)[ε] ⟶ G` with values in a scheme `X` over `k`
of a tangent vector `y ∈ Lie(G)`. (blueprint: `sk-p-comparison`) -/
noncomputable def lieAt (y : Lie G) : infPointsAt G X :=
  ⟨overDualNumbersToSpec X ≫ tangentPoint y, overDualNumbersToSpec_comp_tangentPoint_mem X y⟩

@[simp]
theorem coe_lieAt (y : Lie G) :
    (lieAt X y : overDualNumbers X ⟶ G) = overDualNumbersToSpec X ≫ tangentPoint y :=
  rfl

end LieAt

end GrpObj

end AlgebraicGeometry
