/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Right derived functors computed on adapted complexes

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
in Situation 05S8, with the universal comparison of Definition 05S9 and
`equation-everywhere` (blueprint: lem-sf-right-derived-from-adapted-complexes).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory

namespace CategoryTheory.Functor

/-- An exact functor on the homotopy category has a total right derived functor computed
on any class admitting right quasi-isomorphism replacements on which it inverts
quasi-isomorphisms. The class is a set of objects of the homotopy category, whose objects
are complexes; no invariance or closure condition on the class is required.
`IsRightDerivedFunctor` is the universal property: for every `T` and `β : G ⟶ Qh ⋙ T`,
there is a unique `u : RG ⟶ T` such that `α ≫ whiskerLeft Qh u = β`.

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
right-derived assertion in Situation 05S8; Definition 05S9 and `equation-everywhere`
(blueprint: lem-sf-right-derived-from-adapted-complexes).

Proof:
1. Quasi-isomorphisms in the homotopy category admit a left calculus of fractions
   (`lem-pc-quasi-isomorphisms-multiplicative-system`) and satisfy two out of three,
   as can be checked on every cohomology functor. Choose replacements `r_K : K ⟶ I_K`
   with `I_K` in the class. These choices need not be functorial.
2. A derived morphism between adapted objects is a left fraction `(a : I ⟶ P, b : J ⟶ P)`
   with `b` a quasi-isomorphism (`lem-pc-left-localization-fraction-representation`).
   Replace its common target to make `P` adapted, and assign `G.map a ≫ inv (G.map b)`.
3. Equal fractions have common postcompositions with equal numerators and denominators
   (`lem-pc-left-localization-fraction-equality`). Two out of three makes these
   postcompositions quasi-isomorphisms. Replace the common target again; all resulting
   objects are adapted, so cancellation of the invertible images proves independence.
   The fraction `(f, identity)` shows that actual arrows are sent to `G.map f`.
4. For composable fractions, the left Ore axiom gives a common square for the middle
   denominator and numerator. Replace its target by an adapted object. The square,
   functoriality of `G`, and cancellation of the two invertible denominator images show
   compatibility with composition. Thus the assignment is a functor on localized Hom
   sets between adapted objects; denote it by `Gbar`.
5. Put `H(K) = G(I_K)` and send `f : K ⟶ L` to the value of `Gbar` on
   `inv (Qh.map r_K) ≫ Qh.map f ≫ Qh.map r_L`. This functor inverts quasi-isomorphisms.
   An Ore square for `r_K` and `f ≫ r_L`, followed by an adapted replacement, proves
   naturality of `α0_K = G.map r_K`. Its components at adapted objects are invertible,
   and `H.map r_K = α0_(I_K)` by the actual-arrow computation in Step 3.
6. Localize `H` using `lem-weil-pbc-localization-universal-property` to obtain `RG`
   and `φ : Qh ⋙ RG ≅ H`. Set `α_K = α0_K ≫ φ.inv.app K`. Its components on the
   adapted class are isomorphisms.
7. For arbitrary `T` and `β : G ⟶ Qh ⋙ T`, set
   `v_K = β.app I_K ≫ inv (T.map (Qh.map r_K))`. The Ore square in Step 5 and
   naturality of `β` at its two adapted arrows prove that `v : H ⟶ Qh ⋙ T` is natural.
   Naturality at `r_K` gives `α0_K ≫ v_K = β.app K`. Lift `φ.hom ≫ v` through
   localization to obtain `u : RG ⟶ T` with `α ≫ whiskerLeft Qh u = β`.
8. If `u'` has the same compatibility, put `w_K = φ.inv.app K ≫ u'.app (Qh.obj K)`.
   Naturality at `r_K`, together with `H.map r_K = α0_(I_K)`, forces
   `w_K = β.app I_K ≫ inv (T.map (Qh.map r_K)) = v_K`. Hence `u'` and `u` agree
   after precomposition by `Qh`; uniqueness for localization makes them equal.
-/
theorem exists_rightDerivedFunctor_of_adapted_complexes
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B)
    [G.CommShift ℤ] [G.IsTriangulated]
    (𝓘 : Set (HomotopyCategory A (ComplexShape.up ℤ)))
    (h_replacements : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (I : HomotopyCategory A (ComplexShape.up ℤ)) (r : K ⟶ I),
        I ∈ 𝓘 ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
    (h_inverts : ∀ (I J : HomotopyCategory A (ComplexShape.up ℤ)),
      I ∈ 𝓘 → J ∈ 𝓘 → ∀ (s : I ⟶ J),
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s → IsIso (G.map s)) :
    ∃ (RG : DerivedCategory A ⥤ DerivedCategory B)
      (α : G ⟶ (DerivedCategory.Qh (C := A)) ⋙ RG),
      RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
        ∀ (I : HomotopyCategory A (ComplexShape.up ℤ)), I ∈ 𝓘 → IsIso (α.app I) := by
  sorry

end CategoryTheory.Functor
