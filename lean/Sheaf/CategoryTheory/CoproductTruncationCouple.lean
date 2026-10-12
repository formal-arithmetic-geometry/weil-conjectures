/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.DerivedCoupleFunctoriality
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.CategoryTheory.TruncationRawExact
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification
import Sheaf.CategoryTheory.ExactCouple
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # A coproduct comparison of truncation exact couples

Source: Stacks Project, Tags 015J, 05TC and 08DZ; the exact-couple construction and
coproduct glue of lem-pc-bounded-below-coproduct-filtration, Steps 1 and 2
(blueprint: lem-pc-coproduct-truncation-couple).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A family of bounded-below derived morphisms gives a morphism from the coproduct
of its truncation couples to the target truncation couple, with natural comparisons
on both the initial E terms and D at first index zero. This asserts construction and
naturality only; no initial-page or abutment isomorphism hypothesis is imposed.

Source: Stacks Project, Tag 015J (the natural hypercohomology second page and abutment),
Tag 05TC (derived lower bounds and truncation comparison), and Tag 08DZ (the direct-sum reduction).
(blueprint: lem-pc-coproduct-truncation-couple).

Proof:
1. Use canonical lower truncation and K-injective representatives for K_i and S,
with the common cohomological lower bound a. For each representative apply the
truncation hypercohomology theorem. Its D terms are H^{p+r}(RF(tau_le_r K_i));
its E terms are H^{p+r}(RF(H^r(K_i)[-r])). Apply the same construction to S.
The canonical truncation triangle is functorial in a derived morphism. Applying
RF and homology to its naturality squares gives maps of these exact couples for
u_i, including commutation with the connecting maps. Equivalently represent u_i
by maps between K-injectives and use naturality of the truncation triangles there.
2. Form X by taking the coproduct of the summands' D and E objects at every
bidegree, and the maps induced by their structure maps. Grothendieck exactness of
small coproducts preserves the three exact sequences defining an exact couple,
so these maps give an exact couple. Let Y be the target couple. The maps to Y are
the coproduct descents of the individual couple maps. Precomposing each required
square with every coproduct inclusion reduces it to the individual square; this
gives T. When r<a, each truncated complex is zero, hence each summand D term and
the target D term vanish. Their coproduct vanishes too. Left exactness of F makes
RF of an object in degree zero connective, so both E terms vanish when p<0.
3. At p=0 the truncation inclusion induces an isomorphism on H^n after RF:
the cone is cohomologically at least n+1, and RF preserves that lower bound.
These maps give the individual D-to-abutment isomorphisms. Their coproduct gives
eX; the target gives eY. Naturality of truncation inclusion gives the displayed
D square; check it after precomposing with each coproduct inclusion.
4. For p>=0, the single-functor shift, RF shift commutation, and homology shift
isomorphisms identify each E^{p,r} with H^p(RF(H^r(K_i)[0])). These isomorphisms
are natural, as are their counterparts for S. Taking their coproduct gives s;
the target comparison gives t. Naturality and the coproduct universal property
prove the displayed E equation. No comparison is asserted to be invertible.
For an empty family X is the zero exact couple and the same universal-property
proofs apply. Choices made here witness an existential theorem and define no
library data. -/
theorem exists_coproduct_truncation_couple
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type v) (K : I → DerivedCategory A) (S : DerivedCategory A)
    (u : ∀ i, K i ⟶ S) (a : ℤ)
    (hK : ∀ (i : I) (r : ℤ), r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (K i)))
    (hS : ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj S)) :
    ∃ (X Y : BigradedExactCouple B 0) (T : BigradedExactCouple.CoupleMorphism X Y),
      (∀ p r : ℤ, r < a → IsZero (X.D p r)) ∧
      (∀ p r : ℤ, r < a → IsZero (Y.D p r)) ∧
      (∀ p r : ℤ, p < 0 → IsZero (X.E p r)) ∧
      (∀ p r : ℤ, p < 0 → IsZero (Y.E p r)) ∧
      ∃ (eX : ∀ n : ℤ, X.D 0 n ≅
          ∐ (fun i ↦ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
            (K i)))
        (eY : ∀ n : ℤ, Y.D 0 n ≅
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj S),
        (∀ n : ℤ, Sigma.desc (fun i ↦
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map (u i)) =
            (eX n).inv ≫ T.tD 0 n ≫ (eY n).hom) ∧
        ∀ (p : ℕ) (r : ℤ),
          ∃ (s : X.E p r ≅ ∐ (fun i ↦
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).obj
                  ((DerivedCategory.homologyFunctor A r).obj (K i))))
            (t : Y.E p r ≅
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).obj
                  ((DerivedCategory.homologyFunctor A r).obj S)),
            T.tE p r = s.hom ≫ Sigma.desc (fun i ↦
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).map
                  ((DerivedCategory.homologyFunctor A r).map (u i))) ≫ t.inv := by sorry

end CategoryTheory
