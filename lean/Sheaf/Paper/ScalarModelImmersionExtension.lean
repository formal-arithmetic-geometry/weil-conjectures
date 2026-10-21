/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Constructible

/-!
# Immersion extensions and finite constant scalar models

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-integral-models-operations.proof.md, paragraph (3)
(blueprint: lem-sfb-scalar-model-immersion-extension).

The assertion includes exactness, preservation of constructibility, and the extended
adapted stratifications. Isomorphisms on the old strata retain every chosen covering
and scalar presentation; the complementary stratum has the zero model.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The open and closed extension assertions for one condensed coefficient ring.
The two existential stratifications contain exactly the original strata and one
complementary stratum, as schemes over the target, and are adapted to the extension.
The stratum isomorphisms retain the original covers and finitely presented scalar modules.
`IsZero` on the additional stratum specifies the zero scalar model, using the identity
cover and the zero presentation over the point.

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md, paragraph (3)
(blueprint: lem-sfb-scalar-model-immersion-extension). -/
def ScalarModelImmersionExtensionAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) : Prop :=
  PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
  PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
  PreservesFiniteLimits (CondensedRing.lowerStar Λ i) ∧
  PreservesFiniteColimits (CondensedRing.lowerStar Λ i) ∧
  (∀ F : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
    IsConstantModelConstructible Λ U F →
      IsConstantModelConstructible Λ T
        ((CondensedRing.openImmersionLowerShriek Λ j).obj F)) ∧
  (∀ G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z),
    IsConstantModelConstructible Λ Z G →
      IsConstantModelConstructible Λ T ((CondensedRing.lowerStar Λ i).obj G)) ∧
  (∀ (F : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
      (S : Scheme.Stratification U),
    (∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj F)) →
    (∃ (R : Scheme.Stratification T) (e : Fin R.n ≃ Option (Fin S.n)),
      (∀ b : Fin R.n, match e b with
        | none => Nonempty (Over.mk (R.immersion b) ≅ Over.mk i)
        | some a => Nonempty (Over.mk (R.immersion b) ≅ Over.mk (S.immersion a ≫ j))) ∧
      (∀ b : Fin R.n, HasFiniteConstantLocalModel Λ (R.domain b)
        ((CondensedRing.upperStar Λ (R.immersion b)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj F)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ j)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj F) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj F)) ∧
    IsZero ((CondensedRing.upperStar Λ i).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj F))) ∧
  (∀ (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (S : Scheme.Stratification Z),
    (∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj G)) →
    (∃ (R : Scheme.Stratification T) (e : Fin R.n ≃ Option (Fin S.n)),
      (∀ b : Fin R.n, match e b with
        | none => Nonempty (Over.mk (R.immersion b) ≅ Over.mk j)
        | some a => Nonempty (Over.mk (R.immersion b) ≅ Over.mk (S.immersion a ≫ i))) ∧
      (∀ b : Fin R.n, HasFiniteConstantLocalModel Λ (R.domain b)
        ((CondensedRing.upperStar Λ (R.immersion b)).obj
          ((CondensedRing.lowerStar Λ i).obj G)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ i)).obj
          ((CondensedRing.lowerStar Λ i).obj G) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj G)) ∧
    IsZero ((CondensedRing.upperStar Λ j).obj ((CondensedRing.lowerStar Λ i).obj G)))

/-- Exact open extension by zero and closed direct image preserve finite constant
scalar-model constructibility, retaining the source stratification and its local models
and adjoining the complementary locus with zero model, for every admissible coefficient.

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md, paragraph (3)
(blueprint: lem-sfb-scalar-model-immersion-extension).

Proof:
1. The open and closed source schemes are Noetherian, hence qcqs: use
lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-closed-immersion-proper,
lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-locally-noetherian-quasi-separated.
Thus sk-def-sfb-constructible gives finite adapted stratifications and scalar models.
2. The minimal-closed-subset property (lem-weil-pbc-noetherian-scheme-closed-subsets-minimal)
gives the Noetherian descending-chain condition. By lem-sfb-noetherian-space-compact-subsets,
every subset is quasi-compact; in particular j is quasi-compact. Compose the old immersions
with j or i, using lem-weil-pbc-proper-fp-permanence, and add i or j respectively.
The disjoint finite cover is a stratification (def-constructible-stratification), with
constructible images (def-weil-constructible-subset).
3. Apply lem-weil-pbc-proetale-ringed-open-closed to the reconstructed section-ring sheaf.
The Cartesian identifications of sk-prop-sfb-cartesian-coefficients and the exact equivalences
and adjunction comparisons of lem-sfb-internal-module-operations-transport identify its
functors with the specified internal module functors. This gives exactness, j^* j_! F = F,
i^* i_* G = G, and zero cross restrictions.
4. The pullback composition isomorphism of sk-def-sfb-module-pushforward-pullback gives
(j s_a)^* j_! F = s_a^* F. Pull this isomorphism to each member of the original cover: the same
finitely presented scalar module gives the same model. No presentation matrix is extended.
5. The added closed stratum has zero restriction. Its identity cover and the zero scalar
module, presented by the rank-zero matrix, give its model. Hence j!F is constructible.
6. Similarly (i t_b)^* i_* G = t_b^* G retains every original cover and scalar module on the
closed-side strata; the added open stratum has zero restriction and the rank-zero model.
This proves constructibility of i*G and both adapted-stratification assertions. -/
theorem scalarModelImmersionExtension
    (ℓ : ℕ) [Fact ℓ.Prime] {U Z T : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (_hComplement : Set.range j = (Set.range i)ᶜ) :
    (∀ (A : Type u) [CommRing A] [Finite A],
      ScalarModelImmersionExtensionAssertions (cartesianFinitePointRing A) j i) ∧
    ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj (PadicInt ℓ)) j i ∧
    ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj (Padic ℓ)) j i ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ScalarModelImmersionExtensionAssertions (Profinite.padicIntegersRingObj ℓ E.1) j i ∧
      ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj E.1) j i) ∧
    ScalarModelImmersionExtensionAssertions (Profinite.padicAlgClRingObj ℓ) j i := by
  sorry

end AlgebraicGeometry.ProEtale
