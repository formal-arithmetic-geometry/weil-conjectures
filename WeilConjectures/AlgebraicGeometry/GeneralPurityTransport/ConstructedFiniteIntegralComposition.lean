/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.ConstructedCompositionTrace

/-! # Constructed counit composition for finite and integral coefficients

Source: sk-prop-sp-composition.proof.md, finite orientations, finite tensor maps,
towers, and the application of total derived inverse limit
(blueprint: lem-pur-general-constructed-finite-integral-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open AlgebraicGeometry.ProEtale.PurityTransport

namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

/-- Transitivity of the constructed finite and integral counits over the full
standing field domain. The family is the one fixed by finite diagonal normalization
and scalar compatibility before composition is considered.

Source: sk-prop-sp-composition.proof.md, finite orientations, finite tensor maps,
towers, and the application of total derived inverse limit
(blueprint: lem-pur-general-constructed-finite-integral-composition).

Proof. For Z/ell^n, choose compatible smooth coordinate covers for g and then f.
The composite chart orders the g coordinates before the f coordinates. Recursive
affine integration forgets the last coordinate first, so integration for the
composite is integration for f followed by integration for g. Diagonal/Rees
orientation normalization identifies both inverse orientations with this same
map on the chart. Remove their common twist and shift; they are morphisms of
rank-one sheaves in degree zero. Uniqueness of sheaf Hom gluing gives equality.
The general finite-ring orientation is extension of this orientation along
Z/ell^n to A. The counit-normalized coefficient comparisons preserve the support
compositor and the orientation, so the equality holds for every finite A.

For the tensor maps, transpose through the composite adjunction. Both transposes
apply the projection formula and counit for f, then those for g. Proper/open
projection coherence identifies these with the projection and counit for the
composite. The finite etale/pro-etale comparison applies to every constructible
finite-Tor input. Transport through the normalized section-action tensor and Tate
comparisons in ConstructionFiniteNormalized. Its finite source comparison is
the root-normalized sourceComp, including the even-shift symmetry. Transposing
back, or applying support and the counit, gives the displayed trace equation.

In the actual normalized tower category, the same orientation argument is an
equality of rank-one sheaf towers, tested componentwise after untwisting. Compare
tensor maps by the tower adjunction Hom bijection and projection coherence there.
Apply the reduction/total-limit equivalence to this entire morphism equality.
The integral adjunction's counit-preserving comparisons identify the resulting
counits with those of constructionFamily; its construction normalization and
uniqueness fix this family before any composition condition. The proper/open
comparison and its refinement cocycle identify the support compositor with H,
for arbitrary ch. Root normalization makes the line coordinates unique, so the
equation holds for every p. The base integral presentation gives integers; the
same tower construction gives every O_E, including ramified E. Empty schemes,
zero rings, and zero coordinate blocks require no exceptions. Equality of
arbitrary derived tower morphisms is never inferred merely from evaluations. -/
theorem constructedFiniteIntegralComposition
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] (hk : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (ell : k)) :
    (∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hA : (ell ^ (n + 1) : A) = 0),
      ConstructedCompositionTrace ell k hk hEll (.finite A fin n hA)) ∧
    ConstructedCompositionTrace ell k hk hEll .integers ∧
    ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      ConstructedCompositionTrace ell k hk hEll (.integral E) := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
