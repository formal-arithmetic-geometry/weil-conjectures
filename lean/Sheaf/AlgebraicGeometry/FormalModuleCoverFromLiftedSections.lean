/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # A completed cover from liftable generating sections

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0885,
the paragraph constructing a quotient of a completed finite sum of negative twists.
(blueprint: lem-weil-pbc-formal-module-cover-from-lifted-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite generating family at the first level, together with vanishing of first
cohomology of every twisted transition kernel, gives a map from a completed coherent
module whose first component is epi. No algebraization or full faithfulness is assumed.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0885
(lemma-existence-projective), the paragraph beginning "We first show".
(blueprint: lem-weil-pbc-formal-module-cover-from-lifted-sections).

Proof:
1. Every transition of F is a quotient projection followed by an isomorphism, hence
   is epi. Tensoring with the invertible module L^d is an equivalence, so preserves
   its kernel and gives a short exact sequence of twisted modules at each level.
2. The cohomology long exact sequence and the assumed H^1 vanishing imply that
   global sections of the twisted transition maps are surjective. Starting with
   each member of σ, choose a lift successively at each level. Recursive choice
   gives a compatible family indexed by the same finite set as σ.
3. Put P = L^d and let P inverse be its dual. The tensor equivalence identifies
   a section of F_n tensor P with a map P inverse to F_n. The lifted sections
   therefore define compatible maps from the finite direct sum G of P inverse
   to the terms of F. Invertible modules and their finite sums are coherent on
   a Noetherian scheme, so G is an object of CoherentModules X.
4. The n-th term of F is annihilated by K^(n+1). Each map from G thus kills the
   image of multiplication by that ideal and factors uniquely through
   G/K^(n+1)G. Uniqueness and compatibility of the original maps imply
   naturality of these factorizations, giving α from completion of G to F.
5. At the first level, tensoring the original map with P gives the evaluation
   map of σ, which is epi. The tensor equivalence reflects epimorphisms, so
   the original first-level map is epi. It factors through the quotient
   projection G to G/KG; consequently the induced first component of α is epi.
-/
theorem formalModule_cover_from_lifted_sections
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (F : CoherentFormalModule X K) (L : X.Modules) [L.IsInvertible] (d : ℕ)
    (hvan : ∀ k : ℕ,
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (Scheme.Modules.tensorObj (kernel (F.obj.map (homOfLE (Nat.le_succ k)).op))
          (L.tensorPow d))))
    (σ : (Scheme.Modules.tensorObj (F.obj.obj (op 0)) (L.tensorPow d)).GeneratingSections)
    (hσ : σ.IsFiniteType) :
    ∃ G : CoherentModules X, ∃ α : (completion X K).obj G ⟶ F,
      Epi (α.hom.app (op 0)) := by
  sorry

end AlgebraicGeometry
