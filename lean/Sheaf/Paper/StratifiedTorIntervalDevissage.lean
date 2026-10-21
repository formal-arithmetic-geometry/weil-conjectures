/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CartesianCoefficients
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# A fixed Tor interval across constructible strata

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
`sk-def-localizing-closure-ctf-equals-bc.proof.md`, Strata paragraph
(blueprint: lem-sfb-stratified-tor-interval-devissage).

The coefficient list uses the finite-subextension-valued algebraic closure.
All modules in the Tor conditions are placed in degree zero. Constructibility uses
finite constructible locally closed scheme strata, without a reducedness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A uniform Tor interval for all finite constant local models is also a uniform
Tor interval for all constructible modules on qcqs schemes. The six coefficient cases
are finite discrete rings killed by a power of `ℓ`, `ℤ_ℓ`, `𝒪_E`, `ℚ_ℓ`, `E`, and
finite-subextension-valued `ℚ̄_ℓ`, with `E` a finite subextension of the fixed `PadicAlgCl ℓ`.

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof, Strata paragraph
(blueprint: lem-sfb-stratified-tor-interval-devissage).

Proof plan:
1. Choose the finite constructible locally closed scheme stratification of `M` from
   sk-def-sfb-constructible. Apply lem-fix-constructible-open-closed-refinement to this
   partition. It supplies a finite rooted binary tree of qcqs schemes, with root `X`,
   complementary quasi-compact open and closed children, and an actual factorization
   of every nonempty leaf map through one original scheme stratum. Do not infer a
   scheme-theoretic factorization from set-theoretic containment alone.
2. For such a leaf, pull the scalar-matrix presentations of the model on its stratum
   back along the supplied factorization. Base change preserves pro-etale covers by
   def-weil-proetale-inverse-image. The exact module pullback and canonical coefficient
   isomorphism of sk-prop-sfb-cartesian-coefficients preserve the cokernel and the same
   scalar entries. The composition comparison def-sfb-module-upper-star-comp identifies
   this with the restriction of `M`. The matrix criterion of
   det-def-sfb-constructible-local-model gives a finite constant local model on the leaf.
3. Apply the uniform hypothesis at every nonempty leaf. On an empty leaf or empty root,
   the empty family is a pro-etale cover by def-weil-pbc-proetale-covering, so the same
   local-model definition holds vacuously. Apply the hypothesis there too; this needs
   no assumption that zero belongs to the interval.
4. Induct upwards on the height of the finite tree. At each vertex, the two induction
   hypotheses give the unchanged interval `[c,d]` for the restrictions to its children.
   The composition comparison and cartesian coefficient isomorphisms identify these
   with the inverse-image-ring restrictions required by
   lem-sfb-tor-interval-local-detection(ii). The open child is quasi-compact, so that
   lemma gives the same interval at the vertex. Use isomorphism invariance from
   det-def-sfb-constructible-tor-amplitude throughout. At the root this gives the
   assertion for `M`; the interval never grows with the number of strata. -/
theorem torAmplitudeIn_of_constructible_of_uniform_local_model
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (c d : ℤ) (_hcd : c ≤ d)
    (hlocal : ∀ (S : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)),
      HasFiniteConstantLocalModel Λ.X S N →
        DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj N))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M) :
    DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale
