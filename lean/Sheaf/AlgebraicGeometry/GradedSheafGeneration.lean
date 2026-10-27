/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Mathlib.LinearAlgebra.Span.Defs

/-! # Generation of graded sheaf algebras and modules

Source: Grothendieck, Bourbaki Expose 221, Lemma 3.4, printed pp.262--263
(blueprint: def-sfb-graded-sheaf-generation).

These sectionwise local spanning conditions express generation as sheaves, rather
than surjectivity on sections over every open. Module generators may have different
nonnegative degrees. No bound on their degrees is fixed in advance.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Generation by degree one, when the structural unit identifies degree zero with O_X.
Every section in degree n+1 is locally in the O_X-span of products from degrees 1 and n.
Iterating this condition gives the usual degree-one monomials.
Source: Bourbaki Expose 221, Lemma 3.4
(blueprint: def-sfb-graded-sheaf-generation). -/
def GradedSheafAlgebra.IsGeneratedInDegreeOne {X : Scheme.{u}}
    {B : ℕ → X.Modules} (A : GradedSheafAlgebra B) : Prop :=
  ∀ (n : ℕ) (U : X.Opens) (y : (B (n + 1)).val.obj (op U))
    (p : X) (_hp : p ∈ U),
    ∃ (V : X.Opens) (hVU : V ≤ U) (_hpV : p ∈ V),
      (B (n + 1)).val.map (homOfLE hVU).op y ∈
        Submodule.span Γ(X, V)
          {z | ∃ (a : (B 1).val.obj (op V)) (b : (B n).val.obj (op V)),
            HEq z (A.mul 1 n V a b)}

/-- Local finite generation by homogeneous sections in arbitrary nonnegative degrees.
Near each point choose finitely many sections s_i of degrees d_i. A section of degree n
is locally in the O_X-span of a_i s_i, with d_i <= n and a_i of degree n-d_i.
The empty family is allowed and generates exactly the zero graded module.
Source: Bourbaki Expose 221, Lemma 3.4
(blueprint: def-sfb-graded-sheaf-generation). -/
def GradedSheafModule.IsLocallyFinitelyGenerated {X : Scheme.{u}}
    {B K : ℕ → X.Modules} {A : GradedSheafAlgebra B}
    (M : GradedSheafModule A K) : Prop :=
  ∀ p : X, ∃ (U : X.Opens) (_hp : p ∈ U) (t : ℕ) (d : Fin t → ℕ)
    (s : (i : Fin t) → (K (d i)).val.obj (op U)),
    ∀ (V : X.Opens) (hVU : V ≤ U) (n : ℕ) (y : (K n).val.obj (op V))
      (q : X) (_hq : q ∈ V),
      ∃ (W : X.Opens) (hWV : W ≤ V) (_hqW : q ∈ W),
        (K n).val.map (homOfLE hWV).op y ∈
          Submodule.span Γ(X, W)
            {z | ∃ i : Fin t, d i ≤ n ∧
              ∃ a : (B (n - d i)).val.obj (op W),
                HEq z (M.act (n - d i) (d i) W a
                  ((K (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))}

end AlgebraicGeometry
