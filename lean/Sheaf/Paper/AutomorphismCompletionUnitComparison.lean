/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.PbcAutomorphismTransport
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Paper.WeilCompletedKoszulLimitComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Automorphisms commute with intrinsic completed-coefficient completion

Source: blueprint main-20261015, def-wf-tensor-product, tensor Frobenius sentence;
Stacks Tags 099N, 099M, 0A0E and 03D7.
(blueprint: lem-sf-automorphism-completion-unit-comparison).
The ordinary derived functors and their adjunction are the published tensor-formula
pullback and module direct image. Completion uses the actual completed coefficient
ring, the specified Koszul fiber, and its specified (u,0) unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Ordinary pullback by an automorphism and its actual right adjoint preserve the
complete full subcategory; their specified adjoint equivalence restricts to it.
On every pair of complex representatives there is exactly one completion comparison
isomorphism carrying the pulled-back intrinsic unit to the intrinsic unit.

Source: blueprint main-20261015, def-wf-tensor-product, tensor Frobenius sentence;
Stacks Tags 099N, 099M, 0A0E and 03D7.
(blueprint: lem-sf-automorphism-completion-unit-comparison).

Proof: (1) the site equivalence preserves the limit of finite constant coefficient
sheaves. Its coefficient comparison is the map defined by their projections and
fixes every constant scalar a_j. Apply lem-weil-proetale-isomorphism-inverse-image
and def-weil-pbc-completed-pullback, including the inverse automorphism.
(2) The tensor-normalized scalar-extension isomorphism identifies module pullback
with site relabeling and transported action. Inverse relabeling is its exact inverse.
The actual module adjunction identifies that inverse with module direct image
(lem-weil-sheaf-scalar-extension-ring-iso and
lem-weil-pbc-ringed-topoi-module-adjunction).
(3) Descend this exact adjunction termwise to unbounded derived categories using
lem-sf-exact-functor-derived-triangulated. Its unit and counit remain invertible.
(4) On the exterior basis of every finite Koszul factor, pullback fixes all entries
0 and plus or minus a_j^m, the subset transition products, and the degree-zero unit.
Thus it identifies the strict tensor towers, with their signed differentials.
(5) The module equivalence preserves products. The projection comparison beta
commutes with 1-shift. On the two fiber summands beta in degrees i and i-1 gives
an isomorphism of the specified signed mapping fibers.
(6) Projection to each Koszul level gives beta T(u_C) = u_TC; the zero second
component stays zero. Hence the resulting comparison preserves the actual (u,0)
unit. It is natural in chain maps and descends through quasi-isomorphisms, for any
specified source and target representatives (def-weil-pbc-intrinsic-completion).
(7) This square preserves invertibility of the unit. Repeat for the inverse
scheme automorphism to get preservation by direct image. The strict-limit bridge
lem-weil-pbc-completed-fiber-strict-limit-comparison and the ringed reflector
identify intrinsic completeness with local derived completeness, so it is invariant
under isomorphism. Restrict the actual Hom transpose to the full subcategory;
its unit, counit and triangle identities give the restricted adjoint equivalence.
(8) The same bridge transports the reflector's Hom bijection to these intrinsic
units. For complete N, its direct image is complete. Taking adjuncts therefore
makes precomposition by H(eta_M) injective on maps H(LM) to N. Apply this with
N = L(HM) to obtain uniqueness of the comparison. The argument uses no boundedness
or constructibility and works for every generating tuple, including an empty one. -/
theorem automorphism_completion_unit_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (e : Aut X) :
    (∀ M : PbcCompletedDerived X d,
      IsIso (((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
        (pbcIsoOrdinaryDerivedComparison e.hom d)).unit.app M)) ∧
    (∀ M : PbcCompletedDerived X d,
      IsIso (((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
        (pbcIsoOrdinaryDerivedComparison e.hom d)).counit.app M)) ∧
    (∃ (hH : ∀ M : WfCompleteCategory X d r a ha,
          WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M.obj))
        (hG : ∀ M : WfCompleteCategory X d r a ha,
          WfIsComplete X d r a ha ((pbcActualDerivedPush e.hom d).obj M.obj)),
      ∃ adj :
          ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.hom d) hH ⊣
          ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcActualDerivedPush e.hom d) hG,
        (∀ (M N : WfCompleteCategory X d r a ha)
          (f : (ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙
              pbcIsoAmbientPullback e.hom d) hH).obj M ⟶ N),
          (adj.homEquiv M N f).hom =
            ((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
              (pbcIsoOrdinaryDerivedComparison e.hom d)).homEquiv M.obj N.obj f.hom) ∧
        (∀ M : WfCompleteCategory X d r a ha, IsIso (adj.unit.app M)) ∧
        (∀ M : WfCompleteCategory X d r a ha, IsIso (adj.counit.app M))) ∧
    ∀ (M : PbcCompletedDerived X d)
      (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (real : DerivedCategory.Q.obj C ≅ M)
      (D : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (realH : DerivedCategory.Q.obj D ≅ (pbcIsoAmbientPullback e.hom d).obj M),
      ∃! c : (pbcIsoAmbientPullback e.hom d).obj
          (intrinsicCompletion X d r a ha M C real) ≅
        intrinsicCompletion X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) D realH,
        (pbcIsoAmbientPullback e.hom d).map (intrinsicCompletionUnit X d r a ha M C real) ≫
            c.hom =
          intrinsicCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) D realH := by
  sorry

end AlgebraicGeometry.Scheme
