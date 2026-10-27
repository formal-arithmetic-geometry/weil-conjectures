/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.SupportedProjectiveChern
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace

/-! # Supported infinity class in ordinary comparison coordinates
Source: supported Cartier Kummer normalization and the divisor O(1).
(blueprint: lem-pur-supported-projective-chern-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The supported infinity class, before applying the projective adjunction, is
comparison of the ordinary Kummer class of O(1).
Source: CartierKummerChern, blueprint def-amb-p1-trace, and Stacks 03PL, 0A45, 099R.
(blueprint: lem-pur-supported-projective-chern-comparison).

Proof:
1. On the chart containing infinity its ideal has frame t, where t is the
   coordinate vanishing there; on the other chart it has frame 1. Dual frames
   t^-1 and 1 have the transition of O(1). Thus O(infinity) is O(1), and forgetting
   the normalized supported Cartier boundary gives the positive Kummer class.
2. CartierKummerChern supplies an ordinary Ext class k and a root-normalized
   comparison q. Its forgetful class, precomposed with the integral generator,
   is this supported Kummer Chern class. The bijective ordinaryFiniteClass map
   on the qcqs scheme P1_S and the datum's Chern specification identify k.hom
   with the Chern arrow of projectiveLineTraceDatum.
3. Apply finiteTate_local_root_tensors_hom_ext to q.hom and twistComparison.hom.
   Their normalizations send each locally lifted scalar root tensor to the same
   pro-etale generator. The maps, hence the isomorphisms, are equal.
4. Apply Ext.hom to the realization equation in CartierKummerChern. Compatibility
   with composition and the exact comparison functor identifies its left side
   with the constant comparison, supported unit and cartierKummerMap, and its
   right side with comparison of k.hom followed by the shifted comparison of q.
   Substitute steps 2 and 3, and postcompose with twistDerived.inv. Cancelling
   the derived comparison and its inverse gives the equation below.
All steps hold over a Noetherian base with l invertible. Empty bases and zero
coefficient rings use the same equations; scalar extension needs no flatness. -/
theorem supportedProjectiveChern_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    projectiveChern l E n S hS hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).chern := by
  sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
