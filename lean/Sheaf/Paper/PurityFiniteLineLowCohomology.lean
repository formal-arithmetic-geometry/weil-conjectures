/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneSectionData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

import Sheaf.AlgebraicGeometry.KummerAffineLine
import Sheaf.Paper.PurityTopDerivedRightExact
import Sheaf.Paper.PurityFiniteModuleGenerator
import Sheaf.Paper.PurityKummerCoefficientGenerator
import Sheaf.Paper.PurityKummerTwistRightExact
import Sheaf.Paper.PurityFiniteLineHighCohomology
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Low-degree finite-module Kummer cohomology of the two geometric lines

Source: Milne, Lectures on Etale Cohomology, Sections 14 and 16; blueprint
sk-prop-a1-kummer, Coefficients and Degrees 0 and 1.
(blueprint: lem-pur-finite-line-low-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

/-- Kummer cohomology with arbitrary finite coefficient modules, retaining the actual
coordinate class and affine-line degree-one vanishing.
Source: Milne, Sections 14 and 16; blueprint sk-prop-a1-kummer, Coefficients and
Degrees 0 and 1; thm-pur-rank-one-local-calculation, Steps 1--3.
(blueprint: lem-pur-finite-line-low-cohomology).

Proof: set R=ULift(Z/ell^N). First transport the free rank-one R computation from the
polynomial and Laurent spectra to the affine-space model and its coordinate basic open.
The canonical scheme isomorphisms and open-site comparison preserve the Kummer extension,
its coefficient insertion and the normalized evaluation/Ext comparison. The free calculation
therefore gives affine-line H1=0 and the punctured-line generator for coefficient R itself.

For each of these two objects, let G(M) be H1 of mu_(ell^N) tensor the constant R-module M.
This is an additive functor. Twisting preserves finite colimits: the constant-presheaf
functor, tensoring, and sheafification preserve them, as proved in
kummerModuleTwist_preservesFiniteColimits. Degree-one cohomology on either
object preserves finite colimits by rightDerived_preservesFiniteColimits_of_succ_isZero:
every R-module sheaf has H2=0 by finite_line_high_cohomology. Thus G preserves finite
colimits, without any flatness or freeness assumption on M.

On the punctured line define tau_M(a) as the coefficient image of the Kummer boundary of t.
The proved kummer_coefficient_generator_bijective packages additivity and naturality
of the actual insertion maps and their extension to all finite modules. It uses a natural
transformation from the underlying additive-group functor to G, so no choice of an
R-linear presentation of the cohomology functor is needed. Its component at R is an
isomorphism by the rank-one computation. The finite-module criterion used here is
ModuleCat.isIso_app_of_rankOne_of_finite: finite free modules
are finite coproducts of R. The free module on the elements of M and the free module on its
kernel give a finite free presentation. Preservation of its cokernel extends the isomorphism
to M. Apply
the same theorem to the transformation from the zero functor to affine-line H1; its
rank-one component is an isomorphism because that cohomology group is zero.

Take M to be the underlying R-module of A, which is finite. The explicit scalar-extension
and tensor comparison identifies the twisted abelian sheaf with the underlying sheaf of
the published finite Tate line, taking x tensor a to the specified coefficient insertion.
Naturality of tau under multiplication by each element of A makes tau_A A-linear for the
actual module-cohomology action. It sends one to the actual coordinate class. Its inverse
is the required normalized A-linear isomorphism. The argument includes A=0, N=1, ramified
coefficient rings, and arbitrarily large annihilating N; it never assumes A is free over R. -/
theorem finite_line_low_cohomology (A : Type (u + 1)) [CommRing A] [Finite A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓΩ : IsUnit (ℓ : Ω)) (hN : 1 ≤ N)
    (hA : ((ℓ ^ N : ℕ) : A) = 0)
    (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(Line (Spec (CommRingCat.of Ω)), ⊤))) :
    let S := Spec (CommRingCat.of Ω)
    let X := Line S
    let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
    let H := ((sections X.smallEtaleTopology A (openObject S)).rightDerived 1).obj F
    ∃ e : H ≅ ModuleCat.of A A,
      e.hom (kummerClass A X (openObject S) F (ℓ ^ N) hm
        (Etale.ordinaryFiniteRootMap A (ℓ ^ N) hA X) (coordinateUnit S)) = 1 ∧
      IsZero (((sections X.smallEtaleTopology A
        (Scheme.Etale.mk (𝟙 X))).rightDerived 1).obj F) := by
  sorry

end WeilConjectures.PurityFiniteSetting.RankOne
