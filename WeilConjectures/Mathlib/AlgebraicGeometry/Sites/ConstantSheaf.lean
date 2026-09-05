/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.Mathlib.Topology.ContinuousMap.Algebra

/-!
# The presheaf of rings of continuous functions

For a topological ring `R`, this file constructs the presheaf of rings `U ↦ C(U, R)` on
schemes and shows that it is an fpqc sheaf. This is the ring-valued analogue of
`AlgebraicGeometry.continuousMapPresheafAb`, and it is the coefficient sheaf of the
`ℓ`-adic formalism: for `R = 𝒪_E` a complete discrete valuation ring finite over `ℤ_[ℓ]`,
the restriction of `U ↦ C(U, 𝒪_E)` to the pro-étale site is the completed coefficient
sheaf `lim_n 𝒪_E/ϖ^n`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- `continuousMapPresheaf` as a presheaf of rings, for a topological ring `R`. -/
@[simps]
def continuousMapPresheafRing (R : Type v) [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] : Scheme.{u}ᵒᵖ ⥤ RingCat.{max v u} where
  obj U := RingCat.of C(U.unop, R)
  map {U V} f := RingCat.ofHom (ContinuousMap.compRightRingHom f.unop.base.hom)

variable (R : Type v) [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

/-- `continuousMapPresheafRing` viewed as a type-valued presheaf is
`continuousMapPresheaf`. -/
def continuousMapPresheafRingForgetIso :
    continuousMapPresheafRing.{v, u} R ⋙ CategoryTheory.forget RingCat ≅
      continuousMapPresheaf R :=
  Iso.refl _

lemma isSheaf_fpqcTopology_continuousMapPresheafRing :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheafRing.{v, u} R) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget RingCat.{max v u})
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

end AlgebraicGeometry
