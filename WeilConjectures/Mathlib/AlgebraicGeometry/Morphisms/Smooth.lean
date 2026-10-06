/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# The étale-local normal form of a smooth morphism

A smooth morphism of relative dimension `d` is, étale-locally on the source, the
projection of an affine space: if `g : X ⟶ Y` is smooth of relative dimension `d` and
`x : X`, then there are affine open neighbourhoods `V` of `x` and `U` of `g.base x` with
`V ≤ g ⁻¹ᵁ U` such that the restricted morphism `g.resLE U V` factors as an étale morphism
`V ⟶ 𝔸(d; U)` followed by the structure morphism `𝔸(d; U) ↘ U`.

The index type of the affine space is `ULift.{u} (Fin d)`, since
`AlgebraicGeometry.AffineSpace` takes an index type in the same universe as the scheme.

## Main statements

- `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`: the étale-local normal form of a
  smooth morphism of relative dimension `d`.
- `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`: an irreducible
  scheme smooth over a field is smooth of relative dimension `n` if and only if it has
  dimension `n`.
- `AlgebraicGeometry.topologicalKrullDim_le_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has dimension at most `n`.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over`: the affine space `𝔸(n; S)` in
  finitely many variables is smooth of relative dimension `#n` over `S`.
- `AlgebraicGeometry.smoothOfRelativeDimension_pullback_fst`,
  `AlgebraicGeometry.smoothOfRelativeDimension_pullback_snd`: smoothness of relative dimension `n`
  is inherited by the projections of a fibre product.

## References

- Stacks Project, Tag `054L`, <https://stacks.math.columbia.edu/tag/054L>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Limits in
instance smoothOfRelativeDimension_pullback_fst {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n g] :
    SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ inferInstance

open Limits in
instance smoothOfRelativeDimension_pullback_snd {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

/-- Let `g : X ⟶ Y` be smooth of relative dimension `d` and let `x : X`. After replacing
`X` and `Y` by affine open neighbourhoods `V ∋ x` and `U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U`,
the morphism `g` factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection
`𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```
-/
@[stacks 054L]
theorem Smooth.exists_etale_to_affineSpace {X Y : Scheme.{u}} (g : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d g] (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU :=
  sorry

/-- An irreducible scheme `X` smooth over a field `K` is smooth of relative dimension `n` over
`K` if and only if `X` has dimension `n`: the relative dimension of a smooth morphism at a point
is the dimension of the fibre at that point, and an irreducible scheme locally of finite type
over a field has the same dimension at all of its points. -/
theorem smoothOfRelativeDimension_iff_topologicalKrullDim_eq {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] [IrreducibleSpace X] (n : ℕ) :
    SmoothOfRelativeDimension n f ↔ topologicalKrullDim X = n :=
  sorry

/-- A scheme smooth of relative dimension `n` over a field has dimension at most `n`. It is
normal and locally noetherian, so its connected components are open and irreducible; each of
them is smooth of relative dimension `n`, hence of dimension `n` by
`AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`. -/
theorem topologicalKrullDim_le_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n :=
  sorry

open Limits in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine space `𝔸(n; S)` over `S` in finitely many variables is smooth of relative
dimension `#n` over `S`. -/
instance AffineSpace.smoothOfRelativeDimension_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := Nat.card n)
  MorphismProperty.pullback_fst _ _ <| by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension (Nat.card n)),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card n))]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (R := ULift.{u} ℤ)
    (S := MvPolynomial n (ULift.{u} ℤ)) (n := Nat.card n)).2
      (MvPolynomial.isStandardSmoothOfRelativeDimension _ _)

end AlgebraicGeometry
