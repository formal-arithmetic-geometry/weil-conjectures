/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Paper.ClosedRestrictionDerivedOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Localization and the actual derived restriction

Source: steps 4--5 of lem-sfb-supported-rational-model-rigidity-transfer,
Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2(2).
(blueprint: lem-sfb-supported-coefficient-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- An exact scalar extension whose regular module is the specified prime telescope.
The zeroth leg is the given coefficient map, so the cocone is compatible with its
ring action. No localization object is chosen by this predicate.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-sfb-supported-coefficient-localization). -/
def IsEllLocalizationCoefficient (ℓ : ℕ)
    {R K : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj K] [IsCommMonObj K]
    (a : Mon.mk R ⟶ Mon.mk K) : Prop :=
  (∀ V : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a.hom V))) ∧
  ∀ V : Scheme.{u},
    ∃ α : Functor.ofSequence (fun _ : ℕ ↦ ℓ • 𝟙 (Mod.regular (condensedRingObj R V))) ⟶
        (Functor.const ℕ).obj ((Mod.comap (coefficientMap a.hom V)).obj
          (Mod.regular (condensedRingObj K V))),
      (α.app 0).hom = coefficientMap a.hom V ∧
      Nonempty (IsColimit (Cocone.mk _ α))

/-- Inverting the prime preserves comparison on an individual module. The premise
concerns only this module, not a class of supported models or a stratification.

Source: steps 4--5 of lem-sfb-supported-rational-model-rigidity-transfer;
Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2(2).
(blueprint: lem-sfb-supported-coefficient-localization).

Proof: Tensor the regular-module localization cocone with H. The tensor adjunction
and its colimit preservation identify restriction of the scalar extension of H with
H --ell--> H --ell--> H. The zeroth-leg equation identifies the module action, not
merely the underlying abelian sheaf. Cartesian coefficient pullback carries this
to the same telescope of t^*H. Apply bounded-below section continuity on both qcqs
schemes to the degree-zero telescopes. Naturality at every leg identifies the
homology map of restriction with the colimit of the homology maps for H. Each is
invertible by the premise. Flatness makes coefficient restriction preserve
K-injectives: a K-injective resolution over K computes derived sections also over
R. On the source choose a second K-injective resolution after pullback. Forgetting
coefficients preserves both the adjunction-unit section map and its comparison
chain map, so the two-resolution formula identifies the resulting map with the
actual K-derived restriction. Homology in all integer degrees detects its
invertibility. Negative degrees vanish, and zero modules and empty schemes give
the same zero telescope. -/
theorem supported_coefficient_localization
    (ℓ : ℕ) [Fact ℓ.Prime]
    {R K : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj K] [IsCommMonObj K]
    (a : Mon.mk R ⟶ Mon.mk K) (ha : IsEllLocalizationCoefficient ℓ a)
    {T₀ T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
    (hH : IsIso ((closedRestrictionRho R t).app
      ((DerivedCategory.singleFunctor _ 0).obj H))) :
    IsIso ((closedRestrictionRho K t).app ((DerivedCategory.singleFunctor _ 0).obj
      ((Mod.extendScalars (coefficientMap a.hom T)).obj H))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
