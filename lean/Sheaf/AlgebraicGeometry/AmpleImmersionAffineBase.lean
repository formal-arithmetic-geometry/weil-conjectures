/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback

/-! # An ample module gives an immersion into projective space over an affine base

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph, and Lemma 01VT
(blueprint: lem-weil-pbc-ample-very-ample-immersion-affine-base).

The node's `P_n = Proj(A[x₀,…,xₙ])` over `Spec A` is `ℙ(ULift (Fin (n + 1)); Spec A)`, the
projective space `ℙⁿ_{Spec A}` (identified with `Proj(A[x₀,…,xₙ])` over `Spec A` by Stacks,
Constructions, Lemma 01O3), with structure morphism `ℙ(…; Spec A) ↘ Spec A` and twisting
module `ProjectiveSpace.twist` (the recorded declaration of `def-pc-projective-space-twist`),
as in `IsHProjective` and `IsVeryAmple`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module on a scheme locally of finite type over `Spec A` has a
positive tensor power obtained by pulling back `𝒪(1)` along an immersion into projective
space `ℙⁿ_{Spec A} = Proj(A[x₀,…,xₙ])` over `Spec A`.
Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph; Lemma 01VT (1) ⇒ (5)
(blueprint: lem-weil-pbc-ample-very-ample-immersion-affine-base).

Proof:
1. Ampleness (`def-weil-pbc-ample-invertible-module`) gives quasi-compactness and a finite
   affine cover by nonvanishing loci of sections of positive powers. The scheme is separated
   by `lem-weil-pbc-ample-scheme-separated`. Raise the sections to powers to put them all in
   one power `L^m`; their nonvanishing loci stay the same by the local rank-one calculation
   (`def-sc-invertible-module`, `def-pur-sheaf-tensor-product`). If `X` is empty, choose
   `d = 1`, `n = 0`, and the empty immersion; the modules are uniquely isomorphic.
2. By `lem-weil-pbc-lft-affine-pairs`, each affine piece has a finitely generated `A`-algebra
   of functions. Choose a finite set of generators for each piece.
3. By `lem-pc-section-clearing-denominators`, express these generators as quotients of global
   sections by powers of the covering sections. Choose one sufficiently large common power
   `L^d`, and multiply numerators and denominators to obtain sections `b_k`, `b_kl` with
   `b_kl / b_k` equal to the chosen generators. Tensor exponent laws identify these powers.
4. The sections generate `L^d`, so `lem-weil-pbc-sections-morphism-to-proj-polynomial-ring`
   gives `j` over `Spec A`, an isomorphism `j^*𝒪(1) ≅ L^d`, and the prescribed coordinate
   ratios and inverse images of standard opens.
5. Let `U` be the union of the standard opens indexed by the covering sections. Factor `j`
   through `U` by `lem-weil-pbc-morphism-factors-through-open-subscheme`. The coordinate
   ratios generate the affine-piece rings, so the induced ring maps are surjective.
   By `lem-weil-pbc-closed-immersion-affine-cover-criterion` this factor is a closed immersion.
   Following it by the open inclusion gives an immersion (`def-weil-closed-immersion`,
   `def-weil-open-immersion`).
6. Set `i = j` and invert the module isomorphism from step 4. This supplies all conclusions.
-/
theorem IsAmple.exists_immersion_affine_base (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (L : X.Modules) [L.IsInvertible]
    (hL : IsAmple X L) :
    ∃ (d : ℕ) (hd : 0 < d) (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))),
      IsImmersion i ∧
      i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A) = f ∧
      Nonempty (SheafOfModules.positiveTensorPower X.sheaf L d hd ≅
        (tensorPullback i).obj
          (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) 1)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
