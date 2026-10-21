/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationDimension
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.RingTheory.QuotientHenselianPair
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import Sheaf.AlgebraicGeometry.FieldDiscreteModules
import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.DiscreteModulesAbelian
import Sheaf.CategoryTheory.EquivalenceDerivedSections
import Sheaf.RepresentationTheory.DvrGalois
import Sheaf.RingTheory.FieldAlgebraStrictHenselizationExcellent
import Sheaf.RingTheory.PuncturedCurveBranches

/-!
# Open direct-image dimension on arbitrary curves

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-dimension-general.md`, statement and proof
(blueprint: thm-exc-curve-open-dimension-general).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images across an arbitrary open immersion into a finite-type scheme of
 dimension at most one over a finite field or its algebraic closure vanish above degree one
 for every module sheaf over a finite prime-power-torsion coefficient ring.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-dimension-general.md`
(blueprint: thm-exc-curve-open-dimension-general).

Proof:
1. Forget the coefficient action using `lem-weil-pbc-exchange-forget-coefficients`, obtaining
   a torsion abelian sheaf F. Finite type over a field makes T Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`. Its opens are Noetherian by
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`, so j is quasi-compact. The diagonal
   of the open immersion is an isomorphism, so j is quasi-separated.
2. Apply `prop-weil-pbc-strict-henselization-stalk-formula` at each geometric point t.
   Its strict local ring R is the colimit of affine pointed etale neighbourhoods by
   `lem-weil-pbc-etale-local-ring-triples` and `lem-weil-pbc-strict-henselization-triples`.
   Its dimension is the local dimension at t, at most one, by
   `lem-sc-strict-henselization-dimension` and the bound on chains of point closures in T.
3. If t is in U, its strict local spectrum lies over U, because an open containing the
   closed point of a local spectrum is the whole spectrum. Apply
   `lem-weil-pbc-strictly-henselian-etale-acyclic` to obtain positive-degree vanishing.
4. Otherwise the open above U omits the closed point of Spec R. If dim R is zero it is
   empty, and its cohomology vanishes by the empty covering axiom. If dim R is one, t is
   closed: a distinct specialization of t together with a strict generization would give
   a chain of irreducible closed subsets of T of length two.
5. By `lem-kun-closed-point-field`, the residue field at this closed point is finite over
   k, hence finite or algebraically closed. Its separable closure is algebraically closed.
   By `lem-exc-field-algebra-strict-henselization-excellent`, R and its reduction R0 are
   excellent Noetherian. By `lem-weil-pbc-quotient-henselian-pair`, R0 remains strictly
   henselian with the same residue field. Its spectrum has the same dimension. Apply
   `lem-weil-pbc-reduction-universal-homeomorphism` and
   `thm-weil-pbc-universal-homeomorphism-invariance` to replace R and the open by reductions.
6. By `lem-exc-punctured-curve-branches`, the reduced punctured spectrum is the finite
   coproduct of fraction fields of excellent strictly henselian DVRs with that algebraically
   closed residue field. Its open above U is a subcoproduct, possibly empty.
7. On each branch use `lem-weil-pbc-module-sheaf-constant-ring-equivalence` and
   `lem-exc-field-discrete-modules` to identify module-sheaf cohomology with continuous
   Galois cohomology (`def-exc-continuous-cohomology`). Exact equivalences preserve injectives
   and identify section complexes. `lem-weil-pbc-etale-module-cohomology-forget` identifies
   the underlying abelian groups. Invertibility of the prime on the nonempty T makes it
   different from the residue characteristic; `lem-exc-dvr-galois` gives vanishing above
   degree one, without assuming finiteness of the module.
8. `lem-weil-pbc-finite-coproduct-cohomology-assembly` assembles the branch vanishings.
   The stalk formula gives zero at every geometric point, and
   `lemma-weil-pbc-geometric-stalk-conservative` gives zero for the abelian higher image.
   The comparison of step 1 gives zero for the module higher image. If T is empty, every
   module sheaf on T is zero directly by the empty covering axiom. -/
theorem isZero_higherDirectImage_of_open_curve
    (k : Type u) [Field k]
    (hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (hdim : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hinv : IsUnit (ℓ : Γ(T, ⊤)))
    (hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : ℤ) (hq : 1 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
  sorry

end AlgebraicGeometry.Etale
