/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Finite.Exact
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.FieldTheory.SeparableClosure

import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.StrictHenselizationDimension
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.CompletionRegularLocal
import Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.EtaleSupportedSections
import Sheaf.AlgebraicGeometry.HenselianCompletionOpenRigidity
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.AlgebraicGeometry.SupportCohomology
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison

/-!
# Closed-point purity and strict completion

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2 and Proposition 3.2.4, printed p.244
(blueprint: lem-per-punctual-strict-completion-test).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The geometric closed point determined by the chosen separable closure, embedded
in its algebraic closure to use the recorded pointed-neighbourhood construction.
Source: ILO XVI, paragraph after 3.2.1
(blueprint: lem-per-punctual-strict-completion-test). -/
def punctualGeometricPoint (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] :
    Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap K (AlgebraicClosure K)).comp
    ((algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R))))

/-- The recorded affine pointed-etale colimit for the chosen geometric closed point.
Source: ILO XVI, paragraph after 3.2.1; Stacks 04GP
(blueprint: lem-per-punctual-strict-completion-test). -/
abbrev punctualStrictRing (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] : CommRingCat.{u} :=
  Scheme.strictHenselizationRing (punctualGeometricPoint R K)

/-- Maximal-ideal completion of the actual strict-henselization colimit.
Source: ILO XVI 3.2.4 (blueprint: lem-per-punctual-strict-completion-test). -/
abbrev punctualStrictCompletion (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] : Type u :=
  AdicCompletion (@IsLocalRing.maximalIdeal (punctualStrictRing R K) _
    (Classical.choose (strictHenselizationLocalStructure (punctualGeometricPoint R K))))
    (punctualStrictRing R K)

/-- Testing closed-point purity after strict henselian completion, including the
local-algebra properties of the two canonical rings.
Source: ILO XVI 3.2.1 and the following paragraph, Proposition 3.2.4, printed p.244
(blueprint: lem-per-punctual-strict-completion-test).

Proof:
1. Identify the pointed-neighbourhood colimit with the etale-triples colimit using
`lem-weil-pbc-etale-local-ring-triples`. Strict henselization preserves Noetherianity,
regularity and dimension by `lem-sc-strict-henselization-noetherian`,
`lem-sc-strict-henselization-regular`, `lem-sc-strict-henselization-dimension`.
The completion results give the same properties for B, its completeness and its
residue field K; completeness gives henselianity, hence strict henselianity.
2. `lem-per-ind-etale-closed-support-base-change` and compatibility of the normalized
class identify its pullback to the strict henselization. The residue-field pullback
is exact and conservative by `lem-exc-etale-sheaves-gsets-point`, so it detects purity.
3. On either strictly local scheme, exact global sections are the closed geometric
stalk. Injective representatives and `lem-pur-etale-supported-kernel-adjunction`
identify supported cohomology with the cohomology of the closed exceptional pullback.
4. `lem-per-henselian-completion-open-rigidity` compares the punctured spectra.
The ambient cohomology is the same closed stalk. Functoriality of the support long
exact sequences (`thm-pur-with-support-exactness`) and the five lemma therefore
compare supported cohomology in every degree, also after retaining module scalars.
5. Flatness of completion and flat compatibility of the Kummer classes identify the
actual class maps under this comparison. The cohomology criterion detects their
isomorphism. Combine with step 2. In dimension zero the classes are identities and
the punctured spectra are empty. No excellence hypothesis is used. -/
theorem punctual_strict_completion_test (ℓ : ℕ) (hℓ : ℓ.Prime)
    (R K : Type u) [CommRing R] [IsRegularLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] (hℓR : IsUnit (ℓ : R)) :
    ∃ (_hC : IsRegularLocalRing (punctualStrictRing R K))
      (hB : IsRegularLocalRing (punctualStrictCompletion R K)),
      ringKrullDim (punctualStrictRing R K) = ringKrullDim R ∧
      ringKrullDim (punctualStrictCompletion R K) = ringKrullDim R ∧
      IsStrictlyHenselianLocalRing (punctualStrictCompletion R K) ∧
      IsAdicComplete
        (@IsLocalRing.maximalIdeal (punctualStrictCompletion R K) _ hB.toIsLocalRing)
        (punctualStrictCompletion R K) ∧
      Nonempty ((@IsLocalRing.ResidueField (punctualStrictCompletion R K) _
        hB.toIsLocalRing) ≃+* K) ∧
      (IsPunctuallyPureAt ℓ hℓ (Spec (.of R)) (IsLocalRing.closedPoint R) ↔
        IsPunctuallyPureAt ℓ hℓ (Spec (.of (punctualStrictCompletion R K)))
          (@IsLocalRing.closedPoint (punctualStrictCompletion R K) _ hB.toIsLocalRing)) := by
  sorry

end AlgebraicGeometry.Etale
