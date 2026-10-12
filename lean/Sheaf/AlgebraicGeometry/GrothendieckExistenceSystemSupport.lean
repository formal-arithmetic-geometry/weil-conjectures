/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary
import Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
import Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective
import Sheaf.AlgebraicGeometry.FormalSystemsPushPull
import Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel

/-! # Proper closed support for a coherent thickening system

Source: Stacks Project, Tags 088E and 088F
(blueprint: lem-weil-pbc-grothendieck-existence-system-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A coherent system whose first term has proper support has one proper closed subscheme
annihilating all its pushed-forward terms.
Source: Stacks, Theorem 088E, proof after the first paragraph, in the form of Remark 088F.
(blueprint: lem-weil-pbc-grothendieck-existence-system-support).

Proof:
1. The thickening-systems dictionary pushes the terms to a coherent formal module on X;
its first support is proper over A. Finite type over Noetherian A makes X Noetherian.
2. If the support assertion fails, Noetherian ACC chooses a maximal failing ideal K.
Closed-immersion equivalence replaces X by V(K). The zero system has empty proper support;
thus this replacement is nonempty, and every nonzero ideal satisfies the assertion.
3. Chow's lemma and the closed-model construction give a proper modification Y → X,
an isomorphism over a dense open U, and an open immersion Y → Y' with Y' projective over A.
Pull the system to Y. Its terms have the same support as its first term, by Nakayama on
V(I), and pullback preserves support. This support is proper and its image in Y' is closed.
Extension by zero along Y → Y' is coherent, so gives a coherent formal system on Y'.
4. Projective existence algebraizes that system on Y'. The algebraization has support
inside Y: otherwise the proper image of its support outside Y is a nonempty closed subset
of Spec A, hence meets V(I), since I lies in the Jacobson radical. Reduction modulo I
identifies the intersection with the support of the first term, already inside Y,
a contradiction. Restrict the algebraization to Y.
5. Proper pushforward gives a coherent module H on X. The push-pull comparison from the
original system to the completion of H has kernel and cokernel killed by K_U^t for t ≥ 1,
where K_U cuts out the reduced complement of U. Each power is nonzero: it restricts to
the unit ideal on the nonempty dense open U. The image of the proper support on Y is
proper on X, so H has proper support and its completion is supported on a proper closed
subscheme, by the module-support characterization.
6. The proper-support formal modules form a Serre subcategory, so the kernel and cokernel
have proper first support. The induction hypothesis applies to K_U^t and supports both
on proper closed subschemes. The systems supported on proper closed subschemes also form
a Serre subcategory; applying this to the two short exact sequences of the comparison
supports the original system on one proper closed subscheme. This contradicts maximality.
7. Translate back by the dictionary: annihilation of each pushed term by the closed
subscheme's ideal is precisely the sectionwise equation below. -/
theorem grothendieckExistence_system_support
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (hproper : Scheme.Modules.HasSupportProperOver (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) (F 0)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
      IsProper (j ≫ f) ∧ ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0 := by sorry

end AlgebraicGeometry
