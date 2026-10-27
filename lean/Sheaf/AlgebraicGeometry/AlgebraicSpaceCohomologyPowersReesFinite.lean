/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerReesData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.Blowup.Affine.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite Rees modules of ideal-power cohomology on proper algebraic spaces

Source: Stacks Project, Spaces Cohomology, Lemma 08AW, in Situation 08AV
(blueprint: lem-sfb-space-cohomology-powers-rees-finite).

The conclusion includes the ideal-power submodules, their normalized multiplication
maps, the induced A-linear cohomology maps, and the convolution action. Finiteness is
asserted for that action on the actual additive-sheaf cohomology groups.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

namespace AlgebraicGeometry.AlgebraicSpace

/-- Ideal-power cohomology is finite for the specified Rees action.
Source: Stacks Project, Spaces Cohomology, Lemma 08AW and Situation 08AV
(blueprint: lem-sfb-space-cohomology-powers-rees-finite).

Proof:
1. The power subsheaf is the image of the sum of copies of F indexed by I^r,
   sending the a-th copy by multiplication by a. Local generators give exactly the
   range condition, also for r = 0. Quasi-coherence of images and sums is
   lem-sfb-space-qcoh-kernels-colimits; the affine chart identification is
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.
2. Multiplication by a in I^k carries these generators into the (r+k)-th power.
   Injectivity of the inclusions uniquely determines the multiplication maps.
   Addition, multiplication and the degree-zero scalar formulas hold on sections.
   Functorial additive cohomology preserves these formulas by
   lem-weil-pbc-right-derived-universal-delta-functor, giving A-linear maps and
   the degree-zero normalization. Extend the action by the displayed finite sum.
3. Put B = Rees_A(I) and use the pulled-back algebra f^* tilde(B), without identifying
   it with the image Rees algebra. Tensor pullback and its balancing relation, from
   def-trf-space-etale-module-functors, give its action on the direct sum of powers.
   On every Noetherian affine etale chart choose finite generators of F in degree
   zero. They generate all powers over the pulled-back Rees algebra. Such charts
   cover X: finite type over Spec A makes the etale chart schemes locally Noetherian
   by pqf-lem-locnoeth-lft and def-sfb-space-morphism-properties.
4. Noetherianity makes I finitely generated, so prop-nagata-rees-finite-generation
   makes B finite type over A. Apply lem-sfb-space-graded-cohomology-finite to this
   finite type graded module on the proper space. Its homogeneous maps are exactly
   those fixed in step 2, hence its convolution action and scalar normalization
   are precisely those in the conclusion. No flatness assumption is used. -/
theorem cohomology_powers_rees_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (hf : MapIsProper f) (F : X.Modules) (hF : F.IsQuasicoherent)
    (hfinite : ∀ (T : X.EtaleSite), IsAffine (X.etaleForget.obj T) →
      IsNoetherianRing Γ(X.etaleForget.obj T, ⊤) →
        Module.Finite Γ(X.etaleForget.obj T, ⊤) Γ((X.schemeRestriction T).obj F, ⊤))
    (q : ℕ) :
    ∃ d : IdealPowerReesCohomologyData X I F q,
      @Module.Finite (reesAlgebra I)
        (⨁ r : ℕ, ((idealPowerCohomologyFunctor X q).obj (d.obj r) : Type u))
        _ _ d.reesModule := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
