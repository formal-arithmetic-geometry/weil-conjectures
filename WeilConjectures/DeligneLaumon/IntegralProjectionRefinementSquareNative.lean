/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedCompositorCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.DeligneLaumon.IntegralNativeRefinementIsIso
public import WeilConjectures.DeligneLaumon.NativeIntegralTensorClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection

/-! # Condensed integral projection and one proper refinement

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-sf-integral-projection-refinement-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

private theorem inverseTensorSquare
    {C : Type*} [Category C] [MonoidalCategory C] {A₁ A₂ B₁ B₂ T : C}
    (rA : A₂ ⟶ A₁) (rB : B₂ ⟶ B₁) [IsIso rA] [IsIso rB]
    (p₁ : A₁ ⊗ T ⟶ B₁) (p₂ : A₂ ⊗ T ⟶ B₂)
    (h : p₂ ≫ rB = (rA ⊗ₘ 𝟙 T) ≫ p₁) :
    p₁ ≫ inv rB = (inv rA ⊗ₘ 𝟙 T) ≫ p₂ := by
  apply (cancel_mono rB).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h, tensorHom_comp_tensorHom_assoc]
  simp only [IsIso.inv_hom_id, Category.id_comp, tensorHom_id, id_whiskerRight]

private theorem nativePullbackClosure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : D Λ Y)
    (hL : boundedConstructible (condensedRingObj Λ Y) L) :
    boundedConstructible (condensedRingObj Λ X) ((P Λ f).obj L) := by
  exact boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f L hL

-- Keep cancellation abstract in the coefficient ring and derived category.

private theorem nativeInverseProjectionSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (K : D Λ X) (L : D Λ Y)
    [hKiso : IsIso ((refinement Λ u).app K)]
    [hHiso : IsIso ((refinement Λ u).app (K ⊗ (P Λ f).obj L))] :
    pf Λ c₁ K L ≫ (asIso ((refinement Λ u).app (K ⊗ (P Λ f).obj L))).inv =
      ((asIso ((refinement Λ u).app K)).inv ⊗ₘ 𝟙 L) ≫ pf Λ c₂ K L := by
  exact inverseTensorSquare (C := D Λ Y)
    (A₁ := (F Λ c₁).obj K) (A₂ := (F Λ c₂).obj K)
    (B₁ := (F Λ c₁).obj (K ⊗ (P Λ f).obj L))
    (B₂ := (F Λ c₂).obj (K ⊗ (P Λ f).obj L)) (T := L)
    ((refinement Λ u).app K)
    ((refinement Λ u).app (K ⊗ (P Λ f).obj L))
    (pf Λ c₁ K L) (pf Λ c₂ K L) (refinement_projection Λ u K L)

-- Transport above `NatTrans.app` to avoid converting concrete derived-category
-- endpoints through a full-subcategory projection.

private theorem isIsoAppOfObjectEq
    {C B : Type*} [Category C] [Category B] {F G : C ⥤ B}
    (r : F ⟶ G) {M N : C} (h : M = N) (hi : IsIso (r.app M)) :
    IsIso (r.app N) := by
  subst h
  exact hi

-- Specialization synthesizes the same sheaf tensor with different proof witnesses
-- for weak sheafification and monoidality. Reify proof irrelevance above those data
-- projections instead of asking kernel conversion to unfold the derived categories.
-- This builds only reflexivity, congruence, and proof-irrelevance proofs; the kernel
-- checks the resulting equality and cast normally.

private meta def refinementTypeCongruence (fuel : Nat) (a b : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let fuel + 1 := fuel | throwError "congruence depth"
  if a.isFVar then
    if let some v ← a.fvarId!.getValue? then
      return ← refinementTypeCongruence fuel v b
  if b.isFVar then
    if let some v ← b.fvarId!.getValue? then
      return ← refinementTypeCongruence fuel a v
  if a.isLet then
    return ← refinementTypeCongruence fuel (a.letBody!.instantiate1 a.letValue!) b
  if b.isLet then
    return ← refinementTypeCongruence fuel a (b.letBody!.instantiate1 b.letValue!)
  if a.isMData then
    return ← refinementTypeCongruence fuel a.mdataExpr! b
  if b.isMData then
    return ← refinementTypeCongruence fuel a b.mdataExpr!
  if a == b then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  if ← Lean.Meta.isProof a then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
  if a.isApp && b.isApp && a.getAppFn == b.getAppFn then
    try
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if aa.size != ba.size then throwError "arity mismatch"
      let th ← Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
      let mut args : Array Lean.Expr := #[]
      for i in [:aa.size] do
        let h ← refinementTypeCongruence fuel aa[i]! ba[i]!
        let h ← if th.argKinds[i]! == Lean.Meta.CongrArgKind.eq then
            Lean.Meta.mkAppM ``eq_of_heq #[h]
          else pure h
        args := args ++ #[aa[i]!, ba[i]!, h]
      let out := Lean.mkAppN th.proof args
      let ty ← Lean.Meta.inferType out
      if ty.isEq then return ← Lean.Meta.mkAppM ``heq_of_eq #[out]
      return out
    catch _ => pure ()
  if ← Lean.Meta.withReducible (Lean.Meta.isDefEq a b) then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  throwError "nonapplication mismatch: {a} / {b}"

private theorem nativeRawRefinementIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenIntegralCoefficient l E)))
    (S : Scheme.{u}) (hl : ∀ s : S, IsUnit (l : S.residueField s))
    {X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (M : D Λ X) (hM : boundedConstructible (condensedRingObj Λ X) M) :
    IsIso ((refinement Λ u).app M) := by
  let M' : BoundedConstructible (condensedRingObj Λ X) := ⟨M, hM⟩
  have hi := integralNativeRefinementIsIso Λ l E hcoeff S hl f f c₁ c₂ u M'
  exact isIsoAppOfObjectEq (refinement Λ u) (show M'.obj = M from rfl) hi

/-- The native ordinary condensed integral projection square for one supplied
proper compactification refinement.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-sf-integral-projection-refinement-square).

Proof: pullback preserves bounded constructibility. Identify the continuous integral
coefficient with the integer-ring coefficient of the integral tensor theorem, and
use its constructibility comparison to deduce bounded constructibility of the tensor.
The compactification-independence theorem supplies comparison isomorphisms normalized
on every common refinement. Take the first leg to be the identity refinement: the
normalization then identifies each native refinement with an isomorphism's inverse.
Finally, the native directed projection square and tensor functoriality allow us to
cancel the two refinement components, giving precisely the displayed inverse square.

The statement retains ordinary uncompleted tensor and pullback, the supplied proper
refinement without a Cartesian condition, and the zero and empty cases.
-/
theorem integralProjectionRefinementSquareNative
    (D₀ : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hlp : l ≠ D₀.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))]
    [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D₀.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (K : D (properOpenIntegralCoefficient l E) X)
    (L : D (properOpenIntegralCoefficient l E) Y)
    (hK : boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X) K)
    (hL : condensedConstructibleFiniteTor
      (properOpenIntegralCoefficient l E) Y L) :
    boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X)
      (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L) ∧
      IsIso ((refinement (properOpenIntegralCoefficient l E) u).app K) ∧
      IsIso ((refinement (properOpenIntegralCoefficient l E) u).app
        (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L)) ∧
      ∀ [hKiso : IsIso ((refinement (properOpenIntegralCoefficient l E) u).app K)]
        [hHiso : IsIso ((refinement (properOpenIntegralCoefficient l E) u).app
          (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L))],
        ((pf (properOpenIntegralCoefficient l E) c₁ K L ≫
            (@asIso _ _ _ _ ((refinement (properOpenIntegralCoefficient l E) u).app
              (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L)) hHiso).inv) =
          (((@asIso _ _ _ _ ((refinement (properOpenIntegralCoefficient l E) u).app K)
            hKiso).inv ⊗ₘ 𝟙 L) ≫ pf (properOpenIntegralCoefficient l E) c₂ K L)) := by
  classical
  let : Fintype D₀.k₀ := Fintype.ofFinite D₀.k₀
  let : Fact D₀.p.Prime := ⟨D₀.prime⟩
  let : CharP D₀.k₀ D₀.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D₀.k₀)).symm.trans
      (D₀.card_base.trans D₀.cardinality_eq))
  let : CharP D₀.k D₀.p := charP_of_injective_algebraMap' D₀.k₀ D₀.p
  -- Keep the coefficient expression identical to the public signature. A local
  -- alias forces expensive kernel conversion through the derived-category instances.
  have hP : boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X)
      ((P (properOpenIntegralCoefficient l E) f).obj L) :=
    nativePullbackClosure (properOpenIntegralCoefficient l E) f L hL.1
  have hH : boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X)
      (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L) :=
    nativeIntegralTensorClosure.{u} l E D₀.k D₀.p D₀.prime.pos hlp.symm
      X K ((P (properOpenIntegralCoefficient l E) f).obj L) hK hP
  have hunit : IsUnit (l : D₀.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime D₀.k (Fact.out : l.Prime) hlp.symm)
  have hres (s : Spec (.of D₀.k)) : IsUnit (l : (Spec (.of D₀.k)).residueField s) := by
    have h := hunit.map (algebraMap D₀.k s.asIdeal.ResidueField)
    have h' := h.map (Scheme.Spec.residueFieldIso (.of D₀.k) s).inv.hom
    simpa only [map_natCast] using h'
  have refine_iso (M : D (properOpenIntegralCoefficient l E) X)
      (hM : boundedConstructible
        (condensedRingObj (properOpenIntegralCoefficient l E) X) M) :
      IsIso ((refinement (properOpenIntegralCoefficient l E) u).app M) := by
    let hi := nativeRawRefinementIsIso (properOpenIntegralCoefficient l E) l E
      ⟨Iso.refl _⟩ (Spec (.of D₀.k)) hres f c₁ c₂ u M hM
    run_tac Lean.Elab.Tactic.withMainContext do
      let hd ← Lean.Meta.getLocalDeclFromUserName `hi
      let some t := hd.value? | throwError "missing refinement specialization"
      let t ← Lean.instantiateMVars t
      let source ← Lean.Meta.inferType t
      let target ← Lean.Elab.Tactic.getMainTarget
      let he ← refinementTypeCongruence 100 source target
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[he]
      (← Lean.Elab.Tactic.getMainGoal).assign
        (← Lean.Meta.mkAppM ``Eq.mp #[eq, t])
  refine ⟨hH, refine_iso K hK, refine_iso _ hH, ?_⟩
  intro hKiso hHiso
  exact nativeInverseProjectionSquare (properOpenIntegralCoefficient l E) c₁ c₂ u K L

end WeilConjectures
