/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift
public import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import WeilConjectures.RingTheory.StrictHenselizationCompletionNoetherian
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.AlgebraicGeometry.SaturatedLogBlowupChartCover
import Sheaf.TraceFormula.LogRegularToricRefinement
import Sheaf.TraceFormula.FsFaceSharpening
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Associated points of monoidal centers and canonical log fans

Source: ILO, Travaux de Gabber, VIII 3.4.11 and Lemma 3.4.13(i)--(iii),
printed pp.112--113 (blueprint: lem-per-log-monoidal-associated-points).

The fan is defined using generic points in the rank-stratum SUBSPACE topology.
The algebraized ideal is the uniquely determined ideal of the already stated
chart-construction theorem; no blowup or other auxiliary witness is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Generic points of the connected components of the constant characteristic-rank
loci, with their subspace topology. Source: ILO VI 1.5 and VIII 3.4.11
(blueprint: lem-per-log-monoidal-associated-points). -/
def FineSaturatedLogScheme.fanPoints (X : FineSaturatedLogScheme.{u}) : Set X.scheme :=
  {x | ∃ n : ℕ∞, ∃ hx : x ∈ SimultaneousCohenRigidification.rankLocus X.logStructure n,
    IsGenericPoint (⟨x, hx⟩ : SimultaneousCohenRigidification.rankLocus X.logStructure n)
      (connectedComponent
        (⟨x, hx⟩ : SimultaneousCohenRigidification.rankLocus X.logStructure n))}

/-- The ideal `α(I) O_X`. The first witness of the chart-construction theorem is
uniquely determined by its displayed ideals on all geometric stalks: faithfully flat
strict local rings detect equality of quasi-coherent ideals on every affine open.
Thus this uses a theorem determining the object up to equality, rather than choosing
arbitrary data from an existence assertion. Source: ILO VIII 3.4.2, 3.4.13
(blueprint: lem-per-log-monoidal-associated-points). -/
def FineSaturatedLogScheme.monoidalIdeal (X : FineSaturatedLogScheme.{u})
    (I : X.logStructure.IdealFamily) (hI : X.logStructure.IsNonemptyCoherentIdeal I) :
    X.scheme.IdealSheafData :=
  (coherentLogIdeal_chart_construction X I hI).choose

/-- The actual quotient module `O_X / α(I) O_X`, as the cokernel of the canonical
ideal inclusion. Source: ILO VIII 3.4.13(i)
(blueprint: lem-per-log-monoidal-associated-points). -/
def FineSaturatedLogScheme.monoidalQuotient (X : FineSaturatedLogScheme.{u})
    (I : X.logStructure.IdealFamily) (hI : X.logStructure.IsNonemptyCoherentIdeal I) :
    X.scheme.Modules :=
  cokernel (X.monoidalIdeal I hI).toModulesι

/-- Composition of the underlying arrows from a level to the initial level, including
the identity at level zero. Source: ILO VIII 3.3.9 and 3.4.13(iii)
(blueprint: lem-per-log-monoidal-associated-points). -/
def SaturatedLogBlowupTower.toBase (T : SaturatedLogBlowupTower.{u})
    (i : Fin (T.length + 1)) : (T.level i).scheme ⟶ (T.level 0).scheme :=
  Fin.induction (𝟙 _) (fun j f ↦ (T.arrow j).base ≫ f) i

/-- Associated points of monoidal quotients lie in the log fan, fan points descend
through saturated log blowups, and associated center points descend through every
finite tower. These assertions commute with strict étale restriction. For Zariski
log structures the finite fan is the induced-topology characteristic-sheaf restriction.

Source: ILO VIII 3.4.11 and Lemma 3.4.13(i)--(iii), printed pp.112--113
(blueprint: lem-per-log-monoidal-associated-points).

Proof:
1. The rank-stratum local model identifies fan points by the field condition on
strict local stratum rings. This and associated points are strict étale local
(lem-per-log-rank-strata-local-model, lem-sfb-scheme-etale-assassin-invariance).
The chart-construction theorem identifies the algebraized ideal with chart monomials.
2. An associated point outside the fan gives an injection of the residue field into
the local quotient. Tensoring along the faithfully flat strict henselization and
its Noetherian completion preserves this injection and the maximal-ideal annihilator
(lem-sc-strict-henselization-faithfully-flat, lem-sc-strict-henselization-noetherian,
lem-weil-pbc-strict-henselization-chart-maximal-ideal,
lem-sc-strict-henselization-completion-noetherian,
lem-weil-pbc-local-completion-local-ring).
3. The completed-chart theorem gives k[[Q]][[t]] or C[[Q]][[t]]/(theta), with the
center generated by monomials. There is a transverse variable: otherwise the stratum
quotient is a field, contrary to being outside the fan
(lem-trf-log-regular-completed-chart, lem-per-log-rank-strata-local-model).
4. Multiplication by the first transverse variable is injective on the monomial
quotient, contradicting the nonzero maximal-ideal-annihilated element
(lem-per-completed-monomial-transverse-parameter).
5. A nonempty vanishing locus meets a Noetherian affine open with a nonzero quotient.
The zerodivisor/associated-prime equality gives an associated prime there, hence an
associated point (lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes,
lem-sfb-affine-associated-points-primes).
6. Saturated blowup charts P to Q have the same group completion; toric refinement
preserves log regularity (lem-sfb-saturated-log-blowup-chart-cover,
lem-trf-log-regular-toric-refinement).
7. For the unit faces G in P and F in Q, the local stratum ring upstairs is the
localization of (R/I) tensor Z[F^gp] over Z[G^gp]. The mutually inverse maps send
a surviving monomial to its face-group monomial and all complementary monomials to zero.
8. Face sharpening and finite freeness split F^gp/G^gp, so this is a localized
Laurent polynomial ring over the regular local domain R/I. Its local map from R/I
is injective. If the upstairs stratum ring is a field, every element of the maximal
ideal downstairs must vanish; thus R/I is a field too (lem-trf-fs-face-sharpening,
lem-weil-subgroup-finite-free-abelian-group-free, lem-sc-regular-local-domain).
9. Induct on the tower length, applying fan preservation at every arrow and part
(i) to each center. Length zero has no centers. Strict étale compatibility follows
from the rank-stratum model and the chart-construction theorem.
10. For Zariski log structures, the local face models identify the induced-topology
fan and restricted characteristic sheaf with sharp monoid spectra. These identifications
glue because they restrict the same sheaf. Noetherianity gives finitely many ranks
and components (lem-per-log-rank-strata-local-model, def-trf-fine-fan-blowup).
All arguments use only fs log regularity and Noetherianity.
-/
theorem logMonoidal_associatedPoints (X : FineSaturatedLogScheme.{u})
    [IsNoetherian X.scheme] (hX : X.IsLogRegular) :
    (∀ (I : X.logStructure.IdealFamily) (hI : X.logStructure.IsNonemptyCoherentIdeal I),
      Scheme.Modules.associatedPoints (X.monoidalQuotient I hI) ⊆ X.fanPoints ∧
        (((X.monoidalIdeal I hI).support : Set X.scheme).Nonempty →
          (Scheme.Modules.associatedPoints (X.monoidalQuotient I hI)).Nonempty)) ∧
    (∀ (Y : FineSaturatedLogScheme.{u}) (b : EtaleLogHom Y X)
      (I : X.logStructure.IdealFamily), IsSaturatedLogBlowup b I →
        Y.fanPoints ⊆ b.base ⁻¹' X.fanPoints) ∧
    (∀ (T : SaturatedLogBlowupTower.{u}) (h : T.level 0 = X) (i : Fin T.length),
      (T.toBase i.castSucc ≫ eqToHom (congrArg FineSaturatedLogScheme.scheme h)) ''
        Scheme.Modules.associatedPoints
        ((T.level i.castSucc).monoidalQuotient (T.center i) (T.isBlowup i).1) ⊆
          X.fanPoints) ∧
    (∀ (Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y X),
      f.IsStrict → Etale f.base →
        Y.fanPoints = f.base ⁻¹' X.fanPoints ∧
        ∀ (I : X.logStructure.IdealFamily) (hI : X.logStructure.IsNonemptyCoherentIdeal I),
          ∃ hJ : Y.logStructure.IsNonemptyCoherentIdeal (f.pullbackIdeal I),
          Scheme.Modules.associatedPoints (Y.monoidalQuotient (f.pullbackIdeal I) hJ) =
            f.base ⁻¹' Scheme.Modules.associatedPoints (X.monoidalQuotient I hI)) ∧
    (X.logStructure.IsZariski → X.fanPoints.Finite ∧
      ∃ (F : FineFan.Fan.{u}) (e : F.space ⟶ X.logStructure.sharpSpace),
        Topology.IsEmbedding e.hom.base ∧ Set.range e.hom.base = X.fanPoints ∧
          ∀ z : F.space, Function.Bijective (FineFan.stalkMap e z)) := by
  sorry

end AlgebraicGeometry
