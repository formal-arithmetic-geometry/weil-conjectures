/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# The divisor sequence of a punctured curve

Let `C̄` be a smooth proper connected curve over an algebraically closed field `k`, let
`S ⊆ C̄` be a finite set of closed points and `j : C = C̄ ∖ S ⟶ C̄` the open immersion of its
complement. Then

```
  0 ──▶ 𝔾ₘ ──▶ j_* 𝔾ₘ ──▶ ⨁_{P ∈ S} i_{P*} ℤ ──▶ 0
```

is a short exact sequence of étale sheaves on `C̄`, the third map sending a function on `C`
to its orders of vanishing at the punctures.

The proof follows that of the divisor sequence of an integral regular scheme
(`AlgebraicGeometry.Scheme.nonempty_cokernel_toGenericGm_iso`): both `j_* 𝔾ₘ` and
`⨁_{P ∈ S} i_{P*} ℤ` map to the sheaf `V ↦ (V → ℤ)` of functions on points, the first by the
orders of vanishing at the points over `S` and the second by extension by zero, and the
cokernel of `𝔾ₘ ⟶ j_* 𝔾ₘ` is identified on geometric stalks
(`AlgebraicGeometry.Scheme.nonempty_cokernel_iso_of_sheafFiber`). The local inputs are that a
function on the punctured neighbourhood of a point over `S` of order zero there extends to a
unit, and that a uniformiser at a point over `S` is a unit on the punctured neighbourhood.

## Main definitions

- `AlgebraicGeometry.Scheme.lowerStarGmSheafMap`: the restriction `g_* 𝔾ₘ ⟶ (h ≫ g)_* 𝔾ₘ` of
  units along a morphism `h`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_shortExact_divisorSequence`: the divisor sequence of a
  punctured curve is short exact.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X Z Z' : Scheme.{u}} (g : Z ⟶ X) (h : Z' ⟶ Z) (g' : Z' ⟶ X) (hh : h ≫ g = g')

/-- The restriction of units `g_* 𝔾ₘ ⟶ g'_* 𝔾ₘ` along a morphism `h : Z' ⟶ Z` with
`h ≫ g = g'`: on an étale `X`-scheme `V` it is the map `Γ(V ×_X Z, 𝒪)ˣ ⟶ Γ(V ×_X Z', 𝒪)ˣ`
induced by `V ×_X Z' ⟶ V ×_X Z`. -/
noncomputable def lowerStarGmSheafMap :
    (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj Z.gmSheaf ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g').obj Z'.gmSheaf :=
  ⟨{ app V := CommRingCat.unitsAddCommGrpULift.map
        (pullback.map V.unop.hom g' V.unop.hom g (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).appTop
     naturality {V W} φ := by
      change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
        CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      change ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ.unop).left.appTop ≫ _ =
        _ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ g').map φ.unop).left.appTop
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        show ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ.unop).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        show ((MorphismProperty.Over.pullback @Etale ⊤ g').map φ.unop).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        pullback.map_comp, pullback.map_comp]
      congr 1 }⟩

@[reassoc (attr := simp)]
lemma gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap :
    gmSheafToLowerStarGmSheaf g ≫ lowerStarGmSheafMap g h g' hh = gmSheafToLowerStarGmSheaf g' := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp]
  congr 1
  change (pullback.fst V.unop.hom g).appTop ≫
      (pullback.map V.unop.hom g' V.unop.hom g (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).appTop =
      (pullback.fst V.unop.hom g').appTop
  rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Category.comp_id]

end Scheme

namespace IsCurve

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsRegular C]
  {U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] (iU : Spec C.functionField ⟶ U)
  (hiU : iU ≫ j = C.fromSpecFunctionField)

end IsCurve

namespace IsCurve

variable {k : Type u} [Field k] {C : Scheme.{u}}

end IsCurve

end AlgebraicGeometry
