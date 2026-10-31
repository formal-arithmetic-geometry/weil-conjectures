/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-! # Condensed coefficient compatibility

Source: blueprint, `det-prop-sfb-finite-extension-compatibility`, clauses 1–3
(blueprint: prop-zl-condensed-coefficient-compatibility).

The algebraic closure has finite-subextension-valued continuous sections. Its Push and
Shriek comparisons are asserted only at bounded-below objects; finite coefficient
extension and both Pull comparisons apply on the unbounded derived categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Coefficient inclusions compose, both scalar extensions are exact, both canonical Pull
comparisons are invertible, finite-extension Push and Shriek are invertible on all objects,
and algebraic-closure proper Push and compactifiable Shriek are invertible on bounded-below
objects.

Source: blueprint, `det-prop-sfb-finite-extension-compatibility`, clauses 1–3
(blueprint: prop-zl-condensed-coefficient-compatibility).

Proof:
1. The inclusions are `coefficientMap` applied to the continuous condensed inclusions.
   Their composition is `lem-sfb-subfield-coefficient-map-comp`. Flatness follows from
   `lem-sfb-subfield-flat` and `lem-sfb-qlbar-flat`; these give exact scalar extension,
   since extension is a left adjoint. The canonical `derivedPullIso` gives both Pull claims.
2. `lem-sfb-subfield-push-iso` gives finite-extension Push on all unbounded objects.
3. For a compactification, `def-sfb-derived-lower-shriek-hom` is the proper Push comparison
   followed by the extension-by-zero coefficient isomorphism. Apply
   `lem-sfb-derived-lower-shriek-hom-iso` and step 2 to obtain finite-extension Shriek.
4. For proper `f`, `lem-weil-pbc-condensed-qbar-bounded-push` gives the algebraic-closure
   Push comparison at every object with a lower cohomological bound.
5. Extension by zero along the open part of a compactification is exact, by
   `sk-def-sfb-module-lower-shriek`, so preserves that lower bound. Apply step 4 to the
   proper part and the extended object. The defining Shriek comparison composes this
   invertible component with the proper pushforward of the invertible open comparison
   `def-sfb-derived-open-immersion-shriek-iso`, so its component is invertible too. -/
theorem condensedCoefficientCompatibility (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    (∀ Z : Scheme.{u},
      (padicSubfieldRingObjMap Z ℓ h ≫ padicSubfieldRingObjToPadicAlgCl Z ℓ F =
        padicSubfieldRingObjToPadicAlgCl Z ℓ E) ∧
      PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap Z ℓ h)) ∧
      PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ E))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsIso (derivedPullIso (Profinite.padicSubfieldRingObjMap ℓ h) f).hom ∧
      IsIso (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).hom ∧
      IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f) ∧
      (∀ [hf : HasCompactification f],
        IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ h) f)) ∧
      (∀ [hf : IsProper f]
        (M : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
        (N : ℤ) [hM : M.IsGE N],
        IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M)) ∧
      (∀ [hf : HasCompactification f]
        (M : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
        (N : ℤ) [hM : M.IsGE N],
        IsIso ((derivedLowerShriekHom
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M)))  := by
  constructor
  · intro Z
    refine ⟨?_, inferInstance, inferInstance⟩
    exact AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgCl Z ℓ h
  · intro X Y f
    constructor
    · infer_instance
    constructor
    · infer_instance
    constructor
    · infer_instance
    constructor
    · intro hf
      infer_instance
    constructor
    · intro hf M N hM
      exact isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE ℓ f E M N
    · intro hf M N hM
      letI :
          (D(((HasCompactification.compactification f).i)_!open⟦
            Profinite.continuousMapRingObj E⟧).obj M).IsGE N :=
        Functor.isGE_mapDerivedCategory_obj _ M N
      let hp := isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE ℓ
          (HasCompactification.compactification f).g E
          (D(((HasCompactification.compactification f).i)_!open⟦
            Profinite.continuousMapRingObj E⟧).obj M) N
      letI : IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (HasCompactification.compactification f).g).app
            (D(((HasCompactification.compactification f).i)_!open⟦
              Profinite.continuousMapRingObj E⟧).obj M)) := hp
      have hopen : IsIso ((derivedOpenImmersionShriekIso
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (HasCompactification.compactification f).i).hom.app M) := by
        infer_instance
      have hmap : IsIso (R(((HasCompactification.compactification f).g)_*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
          ((derivedOpenImmersionShriekIso
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
            (HasCompactification.compactification f).i).hom.app M)) := by
        infer_instance
      letI : IsIso ((derivedOpenImmersionShriekIso
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (HasCompactification.compactification f).i).hom.app M) := hopen
      letI : IsIso (R(((HasCompactification.compactification f).g)_*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
          ((derivedOpenImmersionShriekIso
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
            (HasCompactification.compactification f).i).hom.app M)) := hmap
      dsimp [derivedLowerShriekHom]
      exact IsIso.comp_isIso' (IsIso.id _)
        (IsIso.comp_isIso' hp
          (IsIso.comp_isIso' (IsIso.id _)
            (IsIso.comp_isIso' hmap (IsIso.id _))))

end AlgebraicGeometry.ProEtale.CondensedRing
