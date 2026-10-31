/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AcyclicHeartEdge
public import WeilConjectures.CategoryTheory.LeftExactHomologyEdge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.DerivedCategory.ShiftIdentification
import WeilConjectures.CategoryTheory.KInjectiveComputes
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # Acyclic-heart edge and the comparison on a complex

Source: Stacks Project, sites-cohomology.tex, Tag 0D7U, lemma-equivalence-bounded;
agent-written normalization of its canonical truncation edge on a bounded-below complex.
(blueprint: lem-fd-acyclic-edge-complex-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]

/-- The unique edge supplied by the acyclic-heart edge theorem.
Source: Stacks Tag 0D7U (blueprint: lem-fd-acyclic-edge-complex-comparison). -/
noncomputable def canonicalAcyclicHeartEdge (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] : F.AcyclicHeartEdgeFamily :=
  Classical.choose (exists_acyclicHeartEdge F)

/-- The canonical acyclic-heart edge composed with the comparison on complexes is the
cycles/cokernel edge of the left exact functor. The comparison is the bounded-below
right-derived unit itself, followed by its canonical compatibility with the unbounded
resolution model used by the edge. No termwise acyclicity is required.
Source: Stacks Tag 0D7U, lemma-equivalence-bounded, its acyclic-cohomology spectral sequence;
canonical truncation normalization (blueprint: lem-fd-acyclic-edge-complex-comparison).

Proof:
1. Put T = tau_{<=q} X and S = H^q(X)[-q]. The truncation inclusion t and quotient j
   are actual chain maps of bounded-below complexes (lem-weil-pbc-truncation-triangle).
   The truncation spectral sequence (thm-sp-truncation-e2) identifies H^q(RG(t)) with
   an isomorphism c and H^q(RG(j)) with g. Compute these maps using injective
   representatives (lem-weil-pbc-dplus-injective-representative and
   lem-sp-kinjective-computes). Naturality of the derived comparison alpha identifies
   them with the maps for the specified derived pair; its value on a bounded-below
   injective complex is invertible (lem-weil-pbc-right-derived-plus-injective).
2. All nonzero columns vanish by cohomological acyclicity. In the derived exact couple,
   g_{r+1}(alpha_r y) is the class of g_r(y). Induction through a common stable page
   shows that the quotient-to-gr^0 and Theta edge satisfies e c = b g, where b is
   the degree-zero single-object comparison. These are equalities of induced maps:
   precompose with the image epimorphisms at each page. Thus there is no elementwise
   assumption on the abelian category and no connecting-map sign.
3. Resolve M = H^q(X) by an injective resolution in nonnegative degrees, then shift
   by -q. Enough injectives and the degree-zero augmentation theorem identify
   H^q(alpha_S) with G(M) -> H^0(GI). The specified b is its inverse. The canonical
   shift comparisons cancel (lem-sp-shift-identification and
   lem-sp-derived-functor-single-identification), so b H^q(alpha_S) = 1.
4. Put u = H^q(Gt), v = H^q(Gj). Kernel preservation identifies the degree-q term
   of GT with the cycles of GX and identifies their incoming boundaries. Hence u
   is invertible even when the terms of X are not G-acyclic. Precomposing v u^{-1}
   with the cycle quotient gives G(pi_X) k_X, the defining equation of
   ShortComplex.leftExactHomologyEdge. Cancel that epimorphism to get v u^{-1} = h_G.
5. Naturality of alpha gives H^q(alpha_X) u = c H^q(alpha_T) and
   g H^q(alpha_T) = H^q(alpha_S) v. Steps 2 and 3 imply
   e H^q(alpha_X) u = v. Cancel u and use Step 4. The canonical localization/homology
   and bounded/unbounded comparison isomorphisms in the signature express precisely
   these identifications. Only Step 2 uses acyclicity, on cohomology objects. -/
theorem acyclicHeartEdge_comp_complexComparison
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (X : CochainComplex.Plus A)
    (hX : ∀ (j : ℤ) (p : ℕ), 0 < p → IsZero ((F.rightDerived p).obj (X.obj.homology j)))
    (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctorObjQIso (F.mapCochainComplexPlus.obj X) q).inv ≫
      (DerivedCategory.Plus.homologyFunctor B q).map
        (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj X)) ≫
      (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Q.obj X)).hom ≫
      canonicalAcyclicHeartEdge F (DerivedCategory.Plus.Q.obj X)
        (fun j p hp ↦ (hX j p hp).of_iso
          ((F.rightDerived p).mapIso (DerivedCategory.Plus.homologyFunctorObjQIso X j))) q ≫
      F.map (DerivedCategory.Plus.homologyFunctorObjQIso X q).hom =
    ShortComplex.leftExactHomologyEdge F (X.obj.sc q) := by
  sorry

end CategoryTheory.Functor
