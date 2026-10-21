/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude

/-! # Closed-support bounds transported from the etale site

Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2
(blueprint: lem-pur-closed-etale-transport-bounds).
The two assertions have independent inputs: cohomological amplitude in the first,
and bounded constructibility plus a Tor interval in the second. The comparison is
an isomorphism of derived functors on the bounded constructible etale complexes
in the specified interval.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The two independent closed-support bounds. The natural isomorphism on the full
bounded constructible etale interval category supplies the identification for every witness
alpha: nu_T^* B_e ≅ B, by composing its component with Ri^!(alpha^{-1}).
There is no Tor hypothesis in the first conjunct. The Tor predicate in the second
conjunct quantifies over all pro-etale module sheaves, without an origin restriction.
Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2
(blueprint: lem-pur-closed-etale-transport-bounds).

Proof:
1. Apply lem-weil-pbc-finite-ring-constructible-derived-origin to the finite ring A.
It gives a bounded constructible etale witness and reflects each cohomological interval.
2. For a closed immersion the ordinary compact-support functor is canonically closed
direct image; uniqueness of right adjoints identifies its right adjoint with i_e^!.
On a bounded constructible witness the comparison unit is invertible by
thm-weil-pbc-site-comparison. Apply nu_Z^* i_e^! to the unit and then to Rnu_* alpha.
Invert this composite to obtain the identification. Naturality of the unit and
functoriality give the natural isomorphism on the full etale interval subcategory; composing
with Ri^!(alpha^{-1}) gives its value for each witness of B.
3. The two clauses of HasOpenComplementCondition are precisely the hypotheses of
lem-exc-closed-amplitude. It gives the etale interval [r,s+c+1] and constructibility.
Finite-ring constructible comparison transfers them to Z and the identification
transfers them to Ri^!B. No Tor hypothesis was used.
4. For the second conjunct apply lem-sf-comparison-tor-amplitude (ii) to every
bounded constructible witness. It is bounded below; ell is invertible since the
schemes are over k and ell differs from its characteristic. Thus each witness has
the etale Tor interval [r,s], tested against every degree-zero etale sheaf.
5. Apply prop-exc-closed-tor with the given complement condition, then apply
lem-sf-comparison-tor-amplitude (i) on Z. This gives bounded constructibility and
pro-etale Tor interval [r,s+c+1]. Tensoring the comparison isomorphism with each
arbitrary degree-zero pro-etale module sheaf transfers the vanishing to Ri^!B. -/
theorem closedEtaleTransport_bounds (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (i : Z ⟶ T) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (c : ℕ) (_hc : Scheme.HasOpenComplementCondition P.Coefficient j c)
    (r s : ℤ) (_hrs : r ≤ s) :
    (Nonempty
      (ObjectProperty.ι
          (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T ⊓
            _root_.DerivedCategory.homologyConcentratedIn r s) ⋙
          finiteCoefficientIntrinsicDerivedComparison T P.Ring ⋙ P.exceptionalInverseImage i ≅
        ObjectProperty.ι
          (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T ⊓
            _root_.DerivedCategory.homologyConcentratedIn r s) ⋙
          (R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint ⋙
          finiteCoefficientIntrinsicDerivedComparison Z P.Ring) ∧
      ∀ B : WeilConjectures.intrinsicConstructibleIntervalCategory
          P.coefficients.l P.extension P.level P.level_pos T r s,
        (∃ B_e : Etale.DerivedCategoryModule P.Coefficient T,
          Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e ∧
          _root_.DerivedCategory.homologyConcentratedIn r s B_e ∧
          Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e ≅ B.obj)) ∧
        WeilConjectures.constructibleInterval
          P.coefficients.l P.extension P.level P.level_pos Z r (s + (c : ℤ) + 1)
          ((P.exceptionalInverseImage i).obj B.obj)) ∧
    (∀ B : Scheme.proEtaleDerivedCategory T P.Ring,
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos T B →
      Scheme.HasProEtaleTorAmplitude T P.Ring B r s →
      (∀ B_e : Etale.DerivedCategoryModule P.Coefficient T,
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e →
        Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e ≅ B) →
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s B_e) ∧
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos Z
        ((P.exceptionalInverseImage i).obj B) ∧
      Scheme.HasProEtaleTorAmplitude Z P.Ring ((P.exceptionalInverseImage i).obj B)
        r (s + (c : ℤ) + 1)) := by
  sorry

end AlgebraicGeometry.ProEtale
