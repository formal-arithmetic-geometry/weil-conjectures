/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.Compactification.CondensedConstant.CondensedSmoothProperFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Compactification.FiniteFieldDatum.GeometricHypotheses
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

/-! # Native realizations for the every-iterate trace identity

(blueprint: def-every-iterate-trace-native-realizations).

Source: latest blueprint, `sec-zeta-weil/sk-thm-weil-final/prop-every-iterate-trace.md`
(blueprint: `prop-every-iterate-trace`).  The statement is written on the current
condensed `D^b_c(Y_proet,E)` strict-pair interface.  It uses the current local return
operator and the compact/ordinary global transports; no withdrawn rationalization or
Karoubi coefficient model occurs here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures
open scoped CategoryTheory.Obj
namespace WeilConjectures

-- Fix the site universe before generic imported enlargement instances are tried.
local instance (Y : Scheme.{u}) : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} _

/-- The strict condensed bounded-constructible Weil pair at a finite coefficient field.
Source: strict pairs in def-weil-weil-sheaf-complex
(blueprint: prop-every-iterate-trace). -/
abbrev currentStrictWeilComplex
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : PadicAlgCl.FiniteIntermediateField ell) : Type _ :=
  strictWeilComplexCategory D ell hEll Y₀ (.finite E)

/-- The geometric point of the geometric fibre obtained from an extension-valued point.
Source: the stalk and local-return convention (blueprint: prop-every-iterate-trace). -/
def currentExtensionPoint (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (𝟙 _) (by
      let hdata := FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
        D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k n hn
      have hbase := hdata.choose_spec.2.2.2.2.2.2.choose_spec
      rw [Category.assoc, Over.w x, Category.id_comp]
      change Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hbase)

/-- A geometric point lies over the extension-valued point `x`.
Source: the stalk and local-return convention (blueprint: prop-every-iterate-trace). -/
def currentPointOver (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : Prop :=
  z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left


/-- Every geometric point over an extension-valued point has the required return.
Source: local geometric-point choice and semilinear return
(blueprint: prop-every-iterate-trace).

Proof: project to Y₀, where the point factors through F_{q^n} and n-th Frobenius is
identity. Project to Spec k; every field map commutes with the q-power automorphism
and its inverse. The two projections agree, hence pullback extensionality proves
this return equation. The native positive-power index n-1 has exponent n because n≥1.
-/
theorem currentPointOver_return
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : currentPointOver D Y₀ n hn x z) :
    z ≫ NativeCondensedModule.localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫ z := by
  let := Fintype.ofFinite D.k₀
  have hpoint (r : ℕ) :
      NativeCondensedModule.localPositivePower (NativeCondensedModule.frobeniusPointIso D).hom r =
        Spec.map (CommRingCat.ofHom
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (r + 1)).toRingHom) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [NativeCondensedModule.localPositivePower, ih]
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      congr 1
  have hproj (r : ℕ) :
      NativeCondensedModule.localPositivePower (D.geometricFrobenius Y₀).hom r ≫
          pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
      NativeCondensedModule.localPositivePower (D.geometricFrobenius Y₀).hom r ≫
          pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
          NativeCondensedModule.localPositivePower
            (NativeCondensedModule.frobeniusPointIso D).hom r := by
    have h := D.galoisMap_projections Y₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
      (D.geometricFrobenius Y₀).hom ≫ _ =
        _ ≫ (NativeCondensedModule.frobeniusPointIso D).hom at h
    induction r with
    | zero => exact h
    | succ r ih =>
      constructor
      · rw [NativeCondensedModule.localPositivePower, Category.assoc, h.1]
        exact ih.1
      · rw [NativeCondensedModule.localPositivePower, Category.assoc, h.2,
          ← Category.assoc, ih.2, Category.assoc]
        rfl
  have hc : Nat.card (D.extensionSubfield n hn) = Fintype.card D.k₀ ^ n := by
    have h := (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
      D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
    change Nat.card (D.extensionSubfield n hn) = D.q ^ n at h
    exact h.trans (congrArg (fun c : ℕ ↦ c ^ n)
      (D.card_base.symm.trans Nat.card_eq_fintype_card))
  have : Finite (D.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos Fintype.card_pos n)).2
  have hfixed : NativeCondensedModule.localPositivePower
      (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫
      Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) =
      Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) := by
    rw [hpoint, Nat.sub_add_cancel hn, ← Spec.map_comp]
    congr 1
    ext a
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
      D.k₀ D.k n hc (D.extensionSubfield n hn).subtype a
  apply pullback.hom_ext
  · rw [Category.assoc, (hproj (n - 1)).1, Category.assoc]
    change z ≫ pullback.fst _ _ = _
    rw [hz, ← Category.assoc, hfixed]
  · rw [Category.assoc, (hproj (n - 1)).2, ← Category.assoc]
    let c := z ≫ pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    change c ≫ NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫ c
    let β : D.k →+* D.k := (Spec.preimage c).hom
    have hcβ : Spec.map (CommRingCat.ofHom β) = c := Spec.map_preimage c
    rw [← hcβ, hpoint, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply
      D.k₀ D.k β (n - 1 + 1) y

/-- The return equation for the canonical extension point.
Source: the local-return construction of `def-weil-local-frobenius-trace`
(blueprint: prop-every-iterate-trace).

Proof: compare the two pullback projections. On the Y₀ projection, the extension-point
map factors through F_{q^n}, on which the n-th q-Frobenius is the identity. On the k
projection both composites are the n-th geometric Frobenius. Pullback extensionality
then identifies the composites.
-/
theorem currentExtensionPoint_return
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :
    currentExtensionPoint D Y₀ n hn x ≫
        (NativeCondensedModule.localPositivePower (D.geometricFrobenius Y₀).hom (n - 1)) =
      (NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1)) ≫
        currentExtensionPoint D Y₀ n hn x := by
  apply currentPointOver_return D Y₀ n hn x
  exact pullback.lift_fst _ _ _

/-- The finite condensed coefficient ring of the trace identity.
Source: the coefficient E of the statement (blueprint: prop-every-iterate-trace). -/
abbrev currentCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  WeilCoefficient.ab.{u} (.finite E)

local instance (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (currentCoefficient.{u} ell E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _

end WeilConjectures
