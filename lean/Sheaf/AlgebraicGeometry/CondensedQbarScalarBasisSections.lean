/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
import Sheaf.Paper.ProfinitePointPullback
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Coherent coefficient sections for the algebraic closure.

This is the finite-support coordinate part of the scalar-basis construction. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Coherent sections giving the ordinary scalar-extension copower, with exact extension.
Source: Compatibility.lean, `continuousBasisSheafIso`, `isIso_basisAdjUnitDesc`, and
`preservesFiniteLimits_extendScalars_of_flat`; FiniteSubextension.lean, the sectionwise
finite-subextension model.

Proof: choose a small algebraic `E`-basis of `PadicAlgCl ℓ`. A finite-subextension-valued
section has values in an `E`-span of finite dimension (take the compositum with `E`), so
only finitely many basis coordinates occur. Each coordinate is continuous: restrict it to
this finite-dimensional span and apply finite-dimensional linear topology over `ℚ_[ℓ]`.
Conversely a finite sum of continuous `E`-valued coordinates times basis vectors takes
values in a finite subextension and is continuous. These inverse maps, natural on profinite
sets, exhibit the restricted regular coefficient module as the basis-indexed coproduct of
regular `E`-modules. Pull this decomposition to `Z` using the colimit-preserving monoidal
point inverse image. Its monoidal composition comparison proves coherence of the pulled-back
basis sections. Tensoring the regular-module coproduct with `N` preserves it, and the
extension-unit/scalar-action calculation identifies its legs with the displayed maps.
The regular module is flat; coproducts of flat modules are flat. Thus the restricted
regular closure module is flat, and `extendForgetTensorIso`, with reflection by the exact
forgetful functor, proves the finite-limit-preservation clause. This construction is entirely
in ordinary internal modules; no derived unit decomposition is assumed.
(blueprint: lem-weil-pbc-condensed-qbar-derived-scalar-basis-sections) -/
theorem exists_condensedQbar_scalar_basis_sections :
    ∃ (I : Type (u + 1))
      (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
      (∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z))) ∧
      (∀ (Z : Scheme.{u})
        (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z))
        [HasCoproduct (fun _ : I ↦ N)],
        IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
          (Mod.extendRestrictAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app N ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).map
            (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
              (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).obj N)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
