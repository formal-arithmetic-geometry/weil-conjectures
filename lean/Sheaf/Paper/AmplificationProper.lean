/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.TowerPreservation
public import Sheaf.Paper.WitnessCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AmplificationConsequences
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.FiniteLevelAmplification
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.ProperDirectImageFiniteness
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.RingTheory.UniformPerfectQuotientBound
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Amplification for proper base-change squares

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1354;
Stacks Tags 095U, 0GL0, 09C1, 09C7 and 09C2
(blueprint: thm-weil-pbc-amplification-proper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- AMP with the common bound `2 * e`, WIT, and TOW for a proper Cartesian square.
The same adic coefficient datum is used by all three predicates.
Source: blueprint order 1354; Stacks Tags 095U, 0GL0, 09C1, 09C7 and 09C2
(blueprint: thm-weil-pbc-amplification-proper).

Proof (the DAG's repaired assembly, with no perfectness assumption over a quotient):
1. Fix the adic datum (A,I) and put P_n=A/I^n. Evaluating N(A/I)=0 on 1 gives N ∈ I, so N^n ∈
I^n annihilates P_n; a power of a unit is a unit on all four schemes. To check the fibre bound
for f', use that proper implies locally finite type. The fibre-dimension base-change statement
[lem-sc-fibre-dimension-after-base-change], applied also to geometric residue-field extensions,
identifies its local fibre dimensions with those of f. Taking their supremum by
[lem-weil-pbc-dimension-supremum-local-dimensions] gives the same bound e. Empty fibres
contribute -∞ and cause no exception.
2. Apply [thm-weil-pbc-direct-image-finiteness-proper] to f and f' at every P_n, using the
torsion annihilator and fibre bound just verified. This supplies both FIN clauses with the same
2e. Apply [lem-weil-pbc-pullback-preserves-bounded-constructible] to g and g' for exact
triangulated pullback and preservation of every cohomological interval. These are precisely the
two clauses of [def-weil-pbc-finite-level-amplification], proving AMP(square;2e).
3. Every finite-level bounded constructible object admits an etale witness by
[def-weil-pbc-proetale-modules]. Normalization morphisms lift uniquely between witnesses by the
full faithfulness in [thm-weil-pbc-site-comparison]. Tensor comparison identifies their source
with the pulled-back etale derived reduction; exactness and conservativity on etale sheaves in
[prop-weil-pbc-site-comparison-finite-level] ensure that this reduction is bounded whenever the
supplied pro-etale normalization makes it bounded. For u=f or f', put B=P_{n+1}, C=P_n. For a
compatible witness K_{n+1} ≅ ν_U^*L_{n+1}, use the proper torsion projection formula
[lem-kun-0f0g] over B with the constant coefficient complex C. It gives
(Ru_{et,*}L_{n+1}) ⊗^L_B C ≅ Ru_{et,*}(L_{n+1} ⊗^L_B C). The
comparison [prop-weil-pbc-comparison-direct-image] identifies its two ends with the
corresponding pro-etale direct images; choose the specified canonical exchange isomorphism of
[lem-weil-pbc-comparison-direct-image-canonical-mate], whose counit normalization is exactly the
exchange used by the tensor-coherence lemma. Tensor commutes with ν^* by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback];
[lem-weil-pbc-ringed-exchange-tensor-coherence], applied to the comparison square of topoi, says
these identifications commute with the projection map. Thus the transported witness and its
normalization are the same on both routes. This proves normalization and witness compatibility
for both direct images. Properness gives the qcqs hypothesis of the comparison theorem via the
scheme conventions. No perfectness of C as a B-module is used.
4. For u=g or g', derived inverse image commutes with tensor by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Apply this with the constant quotient P_n
to pull the supplied normalization K_{n+1} ⊗^L_{P_{n+1}}P_n ≅ K_n to the normalization of
Lu^*K_•. The comparison isomorphism [lem-weil-pbc-comparison-pullback] transports the etale
witnesses. On a K-flat representative the normalization is the balancing map (x ⊗ b) ⊗
c ↦ x ⊗ q(b)c; inverse image applies to this same formula. For three quotients either
order sends ((x ⊗ d) ⊗ b) ⊗ c to x ⊗ q(d)q(b)c. Hence quotient cocycles and
witness compatibilities agree. Together with the preceding direct-image step this is
WIT(square) of [def-weil-pbc-witness-compatibility].
5. Let M_• be any uniformly bounded constructible input tower, with local terms supported
in [d_0,d_1] as in [def-weil-pbc-bounded-constructible-tower]. By
[lem-weil-pbc-uniform-perfect-quotient-bound] choose one r with all P_n represented in [-r,0] by
finite projectives over A. The flat constant-to-completed coefficient comparison
[lem-weil-pbc-constant-completion-equivalence] gives the same bound over the completed
coefficient sheaf. Tensor the local bounded complex with these resolutions: each reduction is
supported in [d_0-r,d_1], uniformly in n. Its finite-lisse cohomology on the supplied finite
stratification is intrinsically constructible by [def-weil-proetale-constructible-sheaf]. Apply
the etale-origin conclusion of [lem-weil-pbc-normalized-constructible-local-effectivity] to this
normalized input tower with the interval just proved: it belongs to the etale-origin bounded
constructible category at every level. This bridge is necessary because the definition of that
category uses etale origin, not only intrinsic constructible cohomology. By AMP and
[prop-weil-pbc-amplification-consequences], the two direct-image output levels are constructible
in [d_0-r,d_1+2e] and the two finite pullback output levels are constructible in [d_0-r,d_1].
6. These finite-level outputs are the evaluations of the strict-tower functors in TOW. For
direct image this is [prop-weil-pbc-direct-image-limits]. For completed-coefficient tower
pullback, use the objectwise K-flat construction [def-weil-pbc-completed-pullback] and the
flatness and finite-quotient identities of [lem-weil-pbc-constant-completion-equivalence]. Write
R = the constant sheaf A, B=u^{-1}A_T, B'=A_{T'}, S_n=(P_n)_{T'}. Flatness and B ⊗^L_R S_n ≅ S_n,
B' ⊗^L_R S_n ≅ S_n give B' ⊗^L_B S_n ≅ S_n by derived tensor reassociation
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Consequently, for any supplied R_n-level
object M_n, B' ⊗^L_B u^{-1}Res(M_n) ≅ Res(u_n^{-1}M_n); this is
not an identification of the two ambient coefficient categories. Naturality in M_n makes the
isomorphisms commute with all transitions. The preceding normalization arguments supply
quotient-coefficient level structures, inducing the actual transitions, with the quotient
cocycle. Apply [lem-weil-pbc-normalized-constructible-local-effectivity] to each output strict
tower with the common interval from the preceding step. It supplies one finite stratification
and common bounded adic-lisse finite-type local complexes, with reduction maps compatible with
normalization. Thus the full data required by [def-weil-pbc-tower-preservation] exist for each
of the four functors on every input tower. This proves TOW, and completes all three assertions.
-/
theorem amplification_of_isProper
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ k : ℕ, topologicalKrullDim X ≤ (k : WithBot ℕ∞))
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hDimX' : ∃ k : ℕ, topologicalKrullDim X' ≤ (k : WithBot ℕ∞))
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ (k : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnnihilator : ∀ a : A ⧸ d.ideal, N • a = 0)
    (hInvertX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (hInvertY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (hInvertX' : ∀ x : X', IsUnit (N : X'.presheaf.stalk x))
    (hInvertY' : ∀ y : Y', IsUnit (N : Y'.presheaf.stalk y))
    (e : ℕ)
    (hFib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim ↥(pullback f y) ≤ (e : WithBot ℕ∞)) :
    Scheme.HasFiniteLevelAmplification sq d (2 * e) ∧
      WitnessCompatibility sq d ∧ Scheme.HasTowerPreservation sq d := by
  sorry

end AlgebraicGeometry.ProEtale
