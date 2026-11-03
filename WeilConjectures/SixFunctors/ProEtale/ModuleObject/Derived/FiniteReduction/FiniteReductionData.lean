/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData

/-! # Canonical finite coefficient reduction data

Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md`, proof steps 1-2 (finite quotient reduction
and the specified comparison maps); setting of `sk-def-sf-setting`
(blueprint: def-sf-pf-finite-reduction-data).

The map and functors below are the canonical quotient reduction from
`A_{E,n+1}` to `A_{E,m+1}`. The six-functor comparison maps are the flatness-free
analogues of the published condensed coefficient-change maps of
`ChangeOfCoefficients`/`ChangeOfCoefficientsMate` (which assume flat scalar extension):
the Pull comparison is the scalar mate of `derivedComapLeftDerivedUpperStarIso`, the Push
comparison is the base-change mate of its inverse (as in `derivedPushHom_eq_mateEquiv`),
the compact-support comparison pastes Push with `derivedOpenImmersionShriekIso`, and the
tensor comparison is the tensorator of the left-derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor CategoryTheory.MonoidalCategory CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The quotient map `A_{E,n+1} → A_{E,m+1}` for `m ≤ n`.
Source: blueprint `def-sf-pf-finite-reduction-data` (quotient reduction clause). -/
def quotientMap {m n : ℕ} (h : m ≤ n) :
    Padic.coefficientExtensionRing ell E (n + 1) →+*
      Padic.coefficientExtensionRing ell E (m + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The same quotient map on the continuous condensed coefficient rings.
Source: blueprint `def-sf-pf-finite-reduction-data` (condensed coefficient clause). -/
def ringMapSheaf {m n : ℕ} (h : m ≤ n) :
    DerivedNakayama.quotientRingSheaf ell E (n + 1) ⟶
      DerivedNakayama.quotientRingSheaf ell E (m + 1) := by
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  let q := quotientMap ell E h
  have hq : Continuous (q.comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E (n + 1)))) := by
    rw [show q.comp (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal ell E (n + 1))) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E (m + 1)) by
      exact Ideal.Quotient.factor_comp_mk
        (R := Padic.coefficientExtensionIntegers ell E)
        (S := Padic.coefficientExtensionIdeal ell E (n + 1))
        (T := Padic.coefficientExtensionIdeal ell E (m + 1))
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))]
    exact continuous_quot_mk
  have hq' : Continuous q :=
    (QuotientRing.isOpenQuotientMap_mk
      (Padic.coefficientExtensionIdeal ell E (n + 1))).continuous_comp_iff.mp hq
  let s : DerivedNakayama.quotientRingSheaf ell E (n + 1) ⟶
      DerivedNakayama.quotientRingSheaf ell E (m + 1) :=
    ⟨{
      app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((q.compLeftContinuous _ hq').comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  exact s

/-- The induced morphism of condensed coefficient rings.
Source: blueprint `def-sf-pf-finite-reduction-data` (coefficient-map clause). -/
def ringMap {m n : ℕ} (h : m ≤ n) :
    DerivedNakayama.quotientRing ell E (n + 1) ⟶
      DerivedNakayama.quotientRing ell E (m + 1) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (ringMapSheaf ell E h)

/-- The canonical derived scalar-extension functor at a scheme.
Source: blueprint `def-sf-pf-finite-reduction-data`.
(blueprint: def-sf-pf-finite-reduction-data) -/
noncomputable def reduction {X : Scheme.{u}} {m n : ℕ} (h : m ≤ n) :
    CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) X ⥤
      CondensedRing.CompactificationReindexing.D
        (DerivedNakayama.quotientRing ell E (m + 1)) X :=
  let aX : condensedRingObj (DerivedNakayama.quotientRing ell E (n + 1)) X ⟶
      condensedRingObj (DerivedNakayama.quotientRing ell E (m + 1)) X :=
    AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) X
  (Mod.extendScalars aX).leftDerivedFunctor

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]

/-! The following maps are the flatness-free coefficient-change mates. -/

/-- The canonical Pull comparison `ρ_X ∘ Lg^*_n ⟶ Lg^*_m ∘ ρ_Y`, obtained as the scalar mate of
the restriction square `derivedComapLeftDerivedUpperStarIso` (Stacks 0D6D).
Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md` (comparison clause; blueprint:
def-sf-pf-finite-reduction-data). -/
noncomputable def derivedPullHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    L((g)^*⟦DerivedNakayama.quotientRing ell E (n + 1)⟧) ⋙
        L(Mod.extendScalars (coefficientMap (ringMap ell E h) X)) ⟶
      L(Mod.extendScalars (coefficientMap (ringMap ell E h) Y)) ⋙
        L((g)^*⟦DerivedNakayama.quotientRing ell E (m + 1)⟧) :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) X))).symm
      (derivedComapLeftDerivedUpperStarIso (ringMap ell E h) g).hom).natTrans

/-- The tensor comparison from the strong monoidal derived scalar extension.
Source: Stacks 07A4 (blueprint: def-sf-pf-finite-reduction-data). -/
noncomputable def s {T : Scheme.{u}} {m n : ℕ} (h : m ≤ n)
    (K L : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) T) :
    (reduction ell E h).obj (K ⊗ L) ⟶
    (reduction ell E h).obj K ⊗ (reduction ell E h).obj L := by
  letI := Mod.extendScalarsMonoidal
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) T)
  letI : (reduction ell E h).Monoidal :=
    (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap
      (ringMap ell E h) T)).leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.μIso (reduction ell E h) K L).inv

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction
