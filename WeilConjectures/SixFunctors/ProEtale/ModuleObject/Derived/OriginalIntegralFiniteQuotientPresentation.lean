/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralFiniteQuotientConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible

/-! # The actual finite coefficient module underlying an ordinary integral quotient

The coefficient ring is `PadicAlgCl.integersModPow ell E (n + 1)`, and the module is
ordinary extension of scalars along the quotient homomorphism.
(blueprint: lem-sp-original-integral-finite-quotient-presentation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite coefficient module `M / ell^(n+1) M`, constructed by extension of scalars.
Its definition makes no choice of a witness to an unproved existence theorem.
(blueprint: lem-sp-original-integral-finite-quotient-presentation) -/
noncomputable def originalIntegralFiniteQuotientModule
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell)) (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)) (n : ℕ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ell E (n + 1)) X) :=
  (Mod.extendScalars (integersModPowReduction X ell E (n + 1))).obj M

/-- Restriction of the constructed finite coefficient module is the ordinary cokernel.

Proof in words. The coefficient sequence `O_E --ell^(n+1)--> O_E --> O_E/ell^(n+1)`
is short exact. Tensoring with M gives the right exact sequence whose last map is the
extension-of-scalars unit. The unit is therefore a cokernel of multiplication by the
prime power. Uniqueness of cokernels supplies the displayed isomorphism.
(blueprint: lem-sp-original-integral-finite-quotient-presentation) -/
noncomputable def originalIntegralFiniteQuotientRestrictionIso
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell)) (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)) (n : ℕ) :
    (Mod.comap (integersModPowReduction X ell E (n + 1))).obj
      (originalIntegralFiniteQuotientModule ell E X M n) ≅
        cokernel (ell ^ (n + 1) • 𝟙 M) := by
  obtain ⟨hex, hepi⟩ := Mod.exact_extendUnit ((ell : ℤ) ^ (n + 1))
    (zsmul_id_comp_integersModPowReduction X ell E (n + 1))
    (shortExact_integersModPowReduction X ell E (n + 1)) M
  have : Epi (Mod.extendUnit (integersModPowReduction X ell E (n + 1)) M) := hepi
  have e : (Mod.comap (integersModPowReduction X ell E (n + 1))).obj
      (originalIntegralFiniteQuotientModule ell E X M n) ≅
        cokernel (((ell : ℤ) ^ (n + 1)) • 𝟙 M) :=
    hex.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)
  have hmul : (((ell : ℤ) ^ (n + 1)) • 𝟙 M) = (ell ^ (n + 1) • 𝟙 M) := by
    rw [← Int.natCast_pow, natCast_zsmul]
  exact e ≪≫ cokernelIsoOfEq hmul

/-- The actual finite coefficient quotient is constructible, and its restriction is the
specified ordinary cokernel.

Proof in words. Constructibility of the integral cokernel follows from closure under
cokernels. Transport it across the canonical restriction isomorphism just constructed.
For a quotient by a nonzerodivisor, constructibility of a restricted module implies
constructibility over the quotient ring, since extension of scalars preserves its finite
local presentations on each stratum. This works also for zero modules and empty schemes.
(blueprint: lem-sp-original-integral-finite-quotient-presentation) -/
theorem originalIntegralFiniteQuotientPresentation
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E] (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M) (n : ℕ) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.integersModPowRingObj ell E (n + 1)) X)
      (originalIntegralFiniteQuotientModule ell E X M n) ∧
    Nonempty ((Mod.comap (integersModPowReduction X ell E (n + 1))).obj
      (originalIntegralFiniteQuotientModule ell E X M n) ≅
        cokernel (ell ^ (n + 1) • 𝟙 M)) := by
  refine ⟨?_, ⟨originalIntegralFiniteQuotientRestrictionIso ell E X M n⟩⟩
  apply IsConstructibleModuleObject.of_comap_of_shortExact ((ell : ℤ) ^ (n + 1))
    (zsmul_id_comp_integersModPowReduction X ell E (n + 1))
    (shortExact_integersModPowReduction X ell E (n + 1))
  exact IsConstructibleModuleObject.of_iso
    (originalIntegralFiniteQuotientRestrictionIso ell E X M n).symm
    (originalIntegralFiniteQuotientConstructible ell E X M hM n)

end AlgebraicGeometry.ProEtale.CondensedRing
