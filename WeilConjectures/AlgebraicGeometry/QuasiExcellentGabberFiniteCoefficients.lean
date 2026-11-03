/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTorsionProperFiniteness
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# Gabber finiteness with finite local coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 6.7,
Theorem 6.7.1 and the finite-coefficient devissage used in Lemmas 6.7.2 and 6.7.17
(blueprint: lem-per-qe-gabber-finite-coefficient-finiteness).

The vanishing bound is uniform over all residue-field module sheaves. Constructibility
at every positive finite quotient level uses the existing finite-stratification predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- For a finitely presented map of qcqs quasi-excellent schemes on which the residue
characteristic is invertible, residue-field direct image has finite cohomological
dimension when the target has finite Krull dimension. Finite-level direct images of
constructible module sheaves are constructible.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Theorem 6.7.1,
with the finite-coefficient devissage of Lemmas 6.7.2 and 6.7.17
(blueprint: lem-per-qe-gabber-finite-coefficient-finiteness).

Proof plan:
1. Quasi-excellence makes every affine coordinate ring Noetherian; finite affine covers
   make V and T Noetherian. Finite generators of the maximal ideal show that each
   successive quotient of its powers is finite-dimensional over the finite residue
   field. Thus A = R/m^r is finite, J = m/m^r satisfies J^r = 0, and A/J = R/m.
2. For a separated finite-type map, choose a Nagata compactification as an open
   immersion j followed by a proper map p. Finite-type stability of quasi-excellence
   and Noetherianity makes the compactification quasi-excellent and j quasi-compact.
   Apply lem-per-qe-open-residue-finiteness to j.
3. Bound the fibre dimensions of p by e. Proper torsion cohomological dimension gives
   vanishing above 2e, and proper finiteness preserves constructibility. The Leray
   spectral sequence assembles these with the open bound d_j to give 2e + d_j.
   Constructibility passes through its finite abutment filtration by the Serre property.
4. Cover T by finitely many affine opens, and their inverse images by finitely many
   affine opens of V. Their finite intersections need not be affine, but are separated
   over the affine target and quasi-compact since V is Noetherian. Apply Steps 2--3
   to the resulting finite-type restricted maps.
5. The ordered finite-open-cover direct-image spectral sequence adds at most the
   cover length minus one to the maximum intersection bound. Restriction of higher
   direct images agrees with the restricted map, by its sheafified cohomology formula.
   Taking the maximum over the target cover gives a bound uniform in every residue
   module sheaf. Constructibility glues over this finite cover.
6. Filter a constructible A-module sheaf F by J^i F. The ideals J^i have finite
   generating sets, so these images of finite sums of F and their successive quotients
   are constructible. Each successive quotient is killed by J and is constructible
   over R/m by constructible change of rings.
7. Exact scalar restriction from R/m to A commutes with derived direct image: the
   two pushforward compositors for the identity-site coefficient square identify
   the composites, without any assertion that scalar restriction preserves injectives.
   Thus Step 5 gives constructibility of the direct images of the successive quotients.
8. Descending induction on i, using the derived-functor long exact sequence, expresses
   each direct image of J^i F as an extension of a cokernel and a kernel of maps
   between constructible objects. The constructible Serre property proves the claim
   for F. Negative degrees vanish since sheaves have resolutions starting in degree zero.
-/
theorem quasiExcellent_gabber_finiteCoefficient_finiteness
    (R : Type (u + 1)) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (R ⧸ IsLocalRing.maximalIdeal R)]
    (ℓ : ℕ) [CharP (R ⧸ IsLocalRing.maximalIdeal R) ℓ]
    (r : ℕ) (_hr : 1 ≤ r)
    {V T : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace T] [QuasiSeparatedSpace T]
    (h : V ⟶ T) [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    (_hV : ∀ U : V.affineOpens, IsQuasiExcellent Γ(V, U))
    (_hT : ∀ U : T.affineOpens, IsQuasiExcellent Γ(T, U))
    (_hℓV : IsUnit (ℓ : Γ(V, ⊤))) (_hℓT : IsUnit (ℓ : Γ(T, ⊤)))
    (_hTdim : topologicalKrullDim T ≠ ⊤) :
    (∃ c_h : ℤ,
      ∀ (Q : Sheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (R ⧸ IsLocalRing.maximalIdeal R))) (q : ℤ),
        c_h < q → IsZero (higherDirectImage (R ⧸ IsLocalRing.maximalIdeal R) h q Q)) ∧
    (∀ F : Sheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (R ⧸ IsLocalRing.maximalIdeal R ^ r)),
      @Scheme.IsConstructibleEtaleModuleSheaf V (R ⧸ IsLocalRing.maximalIdeal R ^ r) _
        (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) r) F →
      ∀ q : ℤ,
        @Scheme.IsConstructibleEtaleModuleSheaf T (R ⧸ IsLocalRing.maximalIdeal R ^ r) _
          (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) r)
          (higherDirectImage (R ⧸ IsLocalRing.maximalIdeal R ^ r) h q F)) := by
  sorry

end AlgebraicGeometry.Etale
