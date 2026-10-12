/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Split extensions by shifted free complexes

Source: Stacks Project, Differential Graded Algebra, Tag 09KM, finite-filtration argument.
(blueprint: lem-pc-filtered-free-kprojective-step).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A degreewise split extension of a K-projective complex by shifted free complexes
is K-projective.
Source: Stacks Project, Tag 09KM, finite-filtration argument, with the algebra concentrated
in degree zero; admissible exact sequences give triangles by Tag 09KJ.
(blueprint: lem-pc-filtered-free-kprojective-step).

Proof: let `Q` be the cokernel of `f`. The degreewise retractions make `f` a monomorphism,
so `0 → K → L → Q → 0` is a short exact sequence split on underlying graded modules.
It therefore gives a distinguished triangle in the homotopy category.
For an acyclic complex `N`, a map from a single rank-one free complex in degree `d`
is determined by the image of its generator, a cycle in degree `d` of `N`. Acyclicity
provides a primitive in degree `d - 1`, which defines a null homotopy. The same argument
works after every shift of `N`. For a coproduct of such single complexes, choose these
primitives independently on each generator. The universal property of the coproduct
assembles the resulting homotopies, even when the degrees are unbounded. Transfer this
vanishing across the given isomorphism for `Q`. In the exact sequence obtained by applying
`Hom(-, N)` to the triangle, the groups for `Q` and `K` vanish, the latter by `hprev`.
Thus the group for `L` vanishes, giving the null homotopy required by `IsKProjective`.
An empty coproduct gives the zero quotient; the proof also covers zero rings and complexes
with no boundedness hypothesis. All choices and coproducts use `Type (max u v)`. -/
theorem isKProjective_of_filtered_free_step {A : Type u} [CommRing A]
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ L) (hprev : K.IsKProjective)
    (hsplit : ∀ k : ℤ, ∃ r : L.X k ⟶ K.X k,
      f.f k ≫ r = 𝟙 (K.X k))
    (hquot : ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel f ≅ ∐ (fun i : I ↦
        (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
          (ModuleCat.of A (ULift.{v} A))))) :
    L.IsKProjective := by sorry

end CochainComplex
