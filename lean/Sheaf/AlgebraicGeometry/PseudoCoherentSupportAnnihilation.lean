/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Perfect annihilator for a map to a supported complex

Source: Stacks Project, perfect.tex, Tag 0A9C
(blueprint: lem-sc-pseudo-coherent-support-annihilation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- A map `α : P → Q` in D_QCoh(Y), from a perfect complex, or from a pseudo-coherent
complex into a bounded below one, with `Q` supported on `T = Y \ V`, is killed by the tensor
action of a perfect `I → 𝒪_Y[0]` that is an isomorphism over `V`. The tensor is the derived
tensor `schemeDerivedTensorMonoidal` (def-pc-scheme-derived-tensor-structure), with unit
`𝒪_Y[0]`; support on `T` means every cohomology sheaf of `Q` has zero stalks at the points
of `V`. Source: Stacks Project, Tag 0A9C
(blueprint: lem-sc-pseudo-coherent-support-annihilation).

Proof, following the five steps of the node:
1. Set K = RHom(P,Q). It is quasi-coherent, supported outside V, and in case (ii)
   bounded below, by lem-sc-rhom-supported-qcoherent. Tensor-Hom adjunction takes α
   to a map a : 𝒪_Y[0] → K.
2. Use lem-sc-supported-derived-generated-perfect to express K as the sequential
   homotopy colimit of Kₙ, starting with zero, with successive cones sums of shifts
   of a supported perfect generator E. The unit is compact by
   lem-pc-perfect-object-compact; lem-pc-compact-hom-hocolim factors a through some Kₙ.
3. If n = 0, use the zero factor. Otherwise rotate the cone triangles and apply
   lem-sc-supported-factor-through-thick to factor through a finite thick object Q'.
   The generator is compact by lem-pc-perfect-object-compact; Q' is perfect by
   lem-pc-perfect-thick-closure. Shifts, sums, cones and retracts preserve support,
   so Q' is supported outside V.
4. Complete 𝒪_Y[0] → Q' to a triangle I → 𝒪_Y[0] → Q' → I[1]. Perfect thick closure
   makes I perfect; restriction to V makes I → 𝒪_Y[0] an isomorphism. Its composite
   with a is zero because a factors through Q'.
5. Under the tensor-Hom adjunction the map I → K is the composite
   I ⊗ᴸ P → 𝒪_Y[0] ⊗ᴸ P ≅ P → Q, which is therefore zero. -/
theorem exists_perfect_annihilator
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (V : Y.Opens) [CompactSpace (V : Set Y)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (P Q : schemeDerivedQCohCategory Y) (α : P ⟶ Q)
    (hcase : Scheme.IsPerfect Y P.obj ∨ Scheme.IsPseudoCoherent Y P.obj ∧
      ∃ n : ℤ, ∀ k : ℤ, k < n → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj))
    (hQ : ∀ (k : ℤ) (x : Y), x ∈ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf x))) :
    ∃ (I : schemeDerivedCategory Y) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y)),
      Scheme.IsPerfect Y I ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
        V).mapDerivedCategory.map i) ∧
      i ▷ P.obj ≫ (λ_ P.obj).hom ≫ α.hom = 0 := by
  sorry

end AlgebraicGeometry
