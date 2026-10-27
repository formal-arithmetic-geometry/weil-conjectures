/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.TraceFormula.ConductorSmoothBaseChange
public import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Finite normalization quotients and local normality

Source: Stacks Project, Morphisms, Tags 035P and 0C3B; Modules, Tag 01BY;
Coherent, Tag 01Y6 (blueprint: lem-trf-finite-normalization-quotient-local-criterion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite componentwise normalization of a reduced locally Noetherian scheme gives
an exact coherent quotient, its affine quotient model, and its canonical stalk model.
The affine and stalk isomorphisms are normalized on the actual quotient maps.
Source: Stacks Project, Morphisms, Tags 035P and 0C3B; Coherent, Tag 01Y6;
Modules, Tag 01BY (blueprint: lem-trf-finite-normalization-quotient-local-criterion).

Proof:
1. Quasi-compact opens have finitely many components. On each affine open the
normalization algebra is the integral closure in the total fraction ring
(lem-sfb-normalization-affine-total-fractions). The map a to a/1 is injective since
its denominators are non-zero-divisors. Affine sheaf uniqueness gives injectivity;
the definition of conductorCokernel gives the short exact sequence.
2. Finiteness makes the pushforward quasi-coherent of finite type. Apply
pqf-lem-coherent-ft-locnoeth to it and to the structure sheaf, then
lem-weil-pbc-coherent-modules-kernel-cokernel-sum to their cokernel.
3. Apply lem-weil-pbc-quasi-coherent-module-cokernel-image on each affine open.
Images of finite generators generate B/A. The two clauses of
lem-weil-pbc-affine-module-basic-open-localization and tilde sections identify the
restriction with tilde(B/A), compatibly on the principal-open basis, hence globally.
4. At x in Spec A, identify the local ring with A_p and the pushforward stalk with
S⁻¹B using lem-sc-affine-pushforward-stalk-localization. Integral closure commutes
with localization. Lemma lem-trf-total-fractions-prime-localization identifies the
localized ambient total fractions with those of A_p, giving the displayed algebra model.
5. Exactness of module stalks identifies the cokernel with the quotient by R.
The reduced Noetherian local ring has finitely many minimal primes, so
lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions makes this quotient
zero precisely when R is normal. A normal local ring is an integrally closed domain;
conversely such a domain equals its integral closure. The empty scheme has no stalks
and its affine section rings and quotients are zero. -/
theorem finite_normalization_quotient_local_criterion
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X]
    [IsFinite X.fromReducedNormalization] :
    (ShortComplex.cokernelSequence
      (SheafOfModules.unitToPushforwardObjUnit
        X.fromReducedNormalization.toRingCatSheafHom)).ShortExact ∧
    RingedSpace.IsCoherent X.toRingedSpace
      ((Scheme.Modules.pushforward X.fromReducedNormalization).obj
        (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)) ∧
    RingedSpace.IsCoherent X.toRingedSpace (conductorCokernel X) ∧
    (∀ (U : X.Opens) (hU : IsAffineOpen U),
      Function.Injective (X.fromReducedNormalization.app U).hom ∧
      Module.Finite Γ(X, U)
        (Γ(((Scheme.Modules.pushforward X.fromReducedNormalization).obj
          (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)), U) ⧸
          LinearMap.range ((SheafOfModules.unitToPushforwardObjUnit
            X.fromReducedNormalization.toRingCatSheafHom).val.app (op U)).hom) ∧
      ∃ e : (Γ(((Scheme.Modules.pushforward X.fromReducedNormalization).obj
          (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)), U) ⧸
          LinearMap.range ((SheafOfModules.unitToPushforwardObjUnit
            X.fromReducedNormalization.toRingCatSheafHom).val.app (op U)).hom) ≃ₗ[Γ(X, U)]
          Γ(conductorCokernel X, U),
        (∀ s, e ((LinearMap.range ((SheafOfModules.unitToPushforwardObjUnit
            X.fromReducedNormalization.toRingCatSheafHom).val.app (op U)).hom).mkQ s) =
          (cokernel.π (SheafOfModules.unitToPushforwardObjUnit
            X.fromReducedNormalization.toRingCatSheafHom)).val.app (op U) s) ∧
        ∃ E : tilde (ModuleCat.of Γ(X, U)
            (Γ(((Scheme.Modules.pushforward X.fromReducedNormalization).obj
              (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)), U) ⧸
              LinearMap.range ((SheafOfModules.unitToPushforwardObjUnit
                X.fromReducedNormalization.toRingCatSheafHom).val.app (op U)).hom)) ≅
            (conductorCokernel X).restrict hU.fromSpec,
          ∀ q, E.hom.app ⊤ (tilde.toOpen _ ⊤ q) =
            ((conductorCokernel X).restrict hU.fromSpec).presheaf.map
              (eqToHom hU.fromSpec_preimage_self.symm).op
              (((Scheme.Modules.restrictAdjunction hU.fromSpec).unit.app
                (conductorCokernel X)).app U (e q))) ∧
    (∀ x : X,
      ∃ e : X.normalizationPushforwardStalk x ≃ₐ[X.presheaf.stalk x]
          integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)),
        ∃ E : ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            (conductorCokernel X)) ≃ₗ[X.presheaf.stalk x]
            (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) ⧸
              (Algebra.linearMap (X.presheaf.stalk x)
                (integralClosure (X.presheaf.stalk x)
                  (FractionRing (X.presheaf.stalk x)))).range),
          ∀ (U : X.Opens) (hx : x ∈ U)
            (s : Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U)),
            E ((conductorCokernel X).presheaf.germ U x hx
              ((cokernel.π (SheafOfModules.unitToPushforwardObjUnit
                X.fromReducedNormalization.toRingCatSheafHom)).val.app (op U) s)) =
              (Algebra.linearMap (X.presheaf.stalk x)
                (integralClosure (X.presheaf.stalk x)
                  (FractionRing (X.presheaf.stalk x)))).range.mkQ (e
                (((TopCat.Presheaf.pushforward CommRingCat
                  X.fromReducedNormalization.base).obj X.reducedNormalization.presheaf).germ
                    U x hx s))) ∧
    (∀ x : X,
      Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (conductorCokernel X)) ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) := by
  sorry

end AlgebraicGeometry
