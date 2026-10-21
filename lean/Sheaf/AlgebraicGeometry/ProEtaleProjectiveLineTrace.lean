/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem
public import Sheaf.AlgebraicGeometry.CartierDerivedRealization
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents
import Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore
import Sheaf.AlgebraicGeometry.SpP1BaseChangeOfNormalized
import Sheaf.AlgebraicGeometry.SpP1RationalPointChern
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite


/-!
# The pro-etale projective-line trace and diagonal integrals

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-geo-p1-adjunction,
det-sp-p1-trace, clauses 1--3 and its final arbitrary-base consequence
(blueprint: det-sp-p1-trace).

The helpers extend the existing canonical-arrow interface to arbitrary bases by
accepting the Kummer-normalized Chern arrow explicitly. They introduce no replacement
site, twist, derived functor, or independently chosen trace. Every existential arrow
is fixed by its canonical formula. The diagonal uses the literal Cartier comparison
equation with the uniquely normalized supported Kummer boundary.

## Main statements

- `SpP1TraceStatement` assembles the canonical formulas and every conclusion.
- `proEtale_projectiveLine_trace` specializes to the specified finite coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical supported diagonal integrals over one Noetherian base.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
def SpP1DiagonalIntegralsAt (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∃ (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S))),
    (Etale.SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
      ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) κ) ∧
    (SpP1CartierCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A)
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ) ∧
    ∃ hE : PreservesFiniteColimits
        (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))),
      DiagonalIntegralCondition
        (@geoP1DiagonalKernelData A inferInstance N hN hA S hS hE cΔ)
        (geoP1Trace A N hA (ProjectiveLine S)
          (b (ProjectiveLine S)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)))

/-- The canonical source, diagonal-class, and projection-trace formulas, and both
integral identities. The canonical formulas uniquely determine every arrow.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
@[irreducible]
def SpP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    SpP1DiagonalIntegralsAt A N hN hA b S hS

/-- The full projective-line statement, including its arbitrary-base consequence.
All existential maps have their exact canonical formulas specified above.
Source: det-sp-p1-trace, clauses 1--3 (blueprint: det-sp-p1-trace). -/
def SpP1TraceStatement (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) : Prop :=
  ∃ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA),
    SpP1BaseTraceConditions A N hN hA c b d ∧
    SpP1DiagonalIntegrals A N hN hA b

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  Etale.projectiveLineTraceTransport Etale.projectiveLineTraceDatum

private theorem baseTraceConditions_mk
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (c : SpP1ChernFamily A N hA)
    (b : SpP1TwistedFamily A N hA) (d : SpP1DecompositionFamily A N hA)
    (hnorm : SpP1NormalizedDecompositions A N hN hA c b d)
    (hbc : SpP1BaseChange A N hN hA b d)
    (hpoint : SpP1RationalPointChern A N hA c) :
    SpP1BaseTraceConditions A N hN hA c b d := by
  refine ⟨hnorm, hbc, ?_, hpoint⟩
  intro S hS
  apply heq_of_eq
  simp only [geoP1Trace, Iso.hom_inv_id_assoc, biprod.inr_snd]

private theorem exists_baseTraceConditions_generic
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) :
    ∃ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
      (d : SpP1DecompositionFamily A N hA), SpP1BaseTraceConditions A N hN hA c b d := by
  obtain ⟨c, b, d, hnorm⟩ := exists_spP1NormalizedDecompositions A N hN hA
  exact ⟨c, b, d, baseTraceConditions_mk A N hN hA c b d hnorm
    (spP1BaseChange_of_normalized A N hN hA c b d hnorm)
    (spP1RationalPointChern_of_normalized A N hN hA c b d hnorm)⟩

private theorem traceStatement_mk
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (c : SpP1ChernFamily A N hA)
    (b : SpP1TwistedFamily A N hA) (d : SpP1DecompositionFamily A N hA)
    (hbase : SpP1BaseTraceConditions A N hN hA c b d)
    (hdiag : SpP1DiagonalIntegrals A N hN hA b) : SpP1TraceStatement A N hN hA :=
  ⟨c, b, d, hbase, hdiag⟩

private theorem traceStatement_of_baseConditions
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0)
    (hbase : ∃ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
      (d : SpP1DecompositionFamily A N hA), SpP1BaseTraceConditions A N hN hA c b d)
    (hdiag : ∀ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
      (d : SpP1DecompositionFamily A N hA),
      SpP1BaseTraceConditions A N hN hA c b d → SpP1DiagonalIntegrals A N hN hA b) :
    SpP1TraceStatement A N hN hA := by
  obtain ⟨c, b, d, hb⟩ := hbase
  exact traceStatement_mk A N hN hA c b d hb (hdiag c b d hb)

set_option linter.unusedVariables false in
/-- The projective-line component construction, separated from the diagonal clause.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: lem-sp-p1-base-trace-families). -/
theorem exists_spP1BaseTraceConditions (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (hn : 0 < n)
    [Finite (ULift.{u + 1} (ZMod (ℓ ^ n)))] :
    ∃ c : SpP1ChernFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
      ∃ b : SpP1TwistedFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
        (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
      ∃ d : SpP1DecompositionFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
          (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
          SpP1BaseTraceConditions (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
            (pow_pos hℓ.pos n)
            (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) c b d := by
  exact exists_baseTraceConditions_generic (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
    (pow_pos hℓ.pos n) (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n))

private def ext_preimage
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) [IsIso σ] (κ : Ext X L 2) :
    Ext Y (F.obj L) 2 :=
  (Ext.mk₀ (inv σ)).comp (κ.mapExactFunctor F) (zero_add 2)

private theorem ext_preimage_spec
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) [IsIso σ] (κ : Ext X L 2) :
    SpP1CartierCompatibility F σ κ (ext_preimage F σ κ) := by
  unfold SpP1CartierCompatibility ext_preimage
  rw [Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id, Ext.mk₀_id_comp]

private theorem cartierSource_isIso
    (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    IsIso (geoCartierSourceComparison A i) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  unfold geoCartierSourceComparison
  infer_instance

private theorem diagonalComponentFormula_integral
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type uD} [Category.{vD} D] (v : DiagonalComponentData C D)
    (b : v.line ⊞ v.unit ≅ v.target)
    (hu : HEq (biprod.inl ≫ b.hom) v.unitMap)
    (hv : HEq (biprod.inr ≫ b.hom) v.chernMap)
    (h : DiagonalComponentFormula v) :
    DiagonalIntegralCondition v.toDiagonalKernelData (b.inv ≫ biprod.snd) := by
  refine ⟨b.inv ≫ biprod.snd, HEq.rfl, ?_⟩
  obtain ⟨r, unitMap, chernMap, hunit, hchern, h⟩ := h
  have hu := eq_of_heq (hu.trans hunit)
  have hv := eq_of_heq (hv.trans hchern)
  refine ⟨r, ?_⟩
  intro a
  obtain ⟨β, hβ⟩ := h a
  rw [reassoc_of% hβ, ← hu, ← hv]
  simp only [Preadditive.add_comp, Category.assoc,
    Iso.hom_inv_id_assoc, biprod.inl_snd, biprod.inr_snd, comp_zero, zero_add]

private theorem diagonal_cartier (S : Scheme.{u}) :
    (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible := by
  let d := pullback.diagonal (ProjectiveLine S ↘ S)
  let p := pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp only [d, p, pullback.diagonal_fst, Category.comp_id]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker) inferInstance inferInstance inferInstance

private theorem supported_integral_mk
    {I E : Prop} {K : Type uC} {L : Type uD}
    {B : I → K → Prop} {H : K → L → Prop} {R : E → L → Prop}
    (i : I) (k : K) (l : L) (hb : B i k) (hc : H k l) (e : E) (hr : R e l) :
    ∃ (i : I) (k : K) (l : L), B i k ∧ H k l ∧ ∃ e, R e l :=
  ⟨i, k, l, hb, hc, e, hr⟩

private theorem diagonalIntegralsAt_generic
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA)
    (_hbase : SpP1BaseTraceConditions A N hN hA c b d)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    SpP1DiagonalIntegralsAt A N hN hA b S hS := by
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  have : IsLocallyNoetherian
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
  have hE := preservesFiniteColimits_lowerStar_of_isFinite A
    (pullback.diagonal (ProjectiveLine S ↘ S))
  let hW : IsUnit
      (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)) :=
    (map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
      (ProjectiveLine S ↘ S)).appTop.hom N) ▸
        hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
          (ProjectiveLine S ↘ S)).appTop.hom
  have hI := diagonal_cartier S
  obtain ⟨κ, hκ⟩ := (Etale.ordinary_supported_kummer_uniqueBoundary
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hW
    (pullback.diagonal (ProjectiveLine S ↘ S)) hI).exists
  have := cartierSource_isIso A (pullback.diagonal (ProjectiveLine S ↘ S))
  let cΔ := ext_preimage
    (comparisonUpperStar (ModuleCat.{u + 1} A)
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ
  have hcompat := ext_preimage_spec
    (comparisonUpperStar (ModuleCat.{u + 1} A)
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ
  refine supported_integral_mk hI κ cΔ hκ hcompat hE ?_
  let hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)) :=
    (map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
      hS.map (ProjectiveLine S ↘ S).appTop.hom
  have hnorm := _hbase.1 (ProjectiveLine S) hP
  exact diagonalComponentFormula_integral
    (geoP1DiagonalComponentData A N hN hA S hS (c (ProjectiveLine S) hP) cΔ)
    (b (ProjectiveLine S) hP)
    hnorm.twisted_unit hnorm.twisted_chern
    (geoP1_diagonal_comparison_components A N hN hA S hS
      (c (ProjectiveLine S) hP) hnorm.chern hI κ hκ cΔ hcompat)



private theorem diagonalIntegrals_generic
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA)
    (hbase : SpP1BaseTraceConditions A N hN hA c b d) :
    SpP1DiagonalIntegrals A N hN hA b := by
  delta SpP1DiagonalIntegrals
  exact fun S _ hS ↦ diagonalIntegralsAt_generic A N hN hA c b d hbase S hS

set_option linter.unusedVariables false in
/-- The diagonal integral clause for normalized projective-line families.
Source: det-sp-p1-trace, clause 3 (blueprint: lem-sp-p1-diagonal-integrals-family). -/
theorem spP1DiagonalIntegrals_of_twisted (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (hn : 0 < n)
    [Finite (ULift.{u + 1} (ZMod (ℓ ^ n)))]
    (c : SpP1ChernFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (b : SpP1TwistedFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (d : SpP1DecompositionFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (_hbase : SpP1BaseTraceConditions (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) c b d) :
    SpP1DiagonalIntegrals (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) b := by
  exact diagonalIntegrals_generic (ULift.{u + 1} (ZMod (ℓ ^ n)))
    (ℓ ^ n) (pow_pos hℓ.pos n)
    (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) c b d _hbase

set_option linter.style.haveILetI false in
theorem proEtale_projectiveLine_trace (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (_hn : 0 < n) :
    @SpP1TraceStatement (ULift.{u + 1} (ZMod (ℓ ^ n))) inferInstance
      (Finite.of_equiv (ZMod (ℓ ^ n))
        (h := @Finite.of_fintype _ (@ZMod.fintype (ℓ ^ n)
          ⟨ne_of_gt (pow_pos hℓ.pos n)⟩)) Equiv.ulift.symm)
      (ℓ ^ n) (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) := by
  letI : Finite (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
    Finite.of_equiv (ZMod (ℓ ^ n))
      (h := @Finite.of_fintype _ (@ZMod.fintype (ℓ ^ n)
        ⟨ne_of_gt (pow_pos hℓ.pos n)⟩)) Equiv.ulift.symm
  exact traceStatement_of_baseConditions (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
    (pow_pos hℓ.pos n) (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n))
    (exists_spP1BaseTraceConditions ℓ hℓ n _hn)
    (spP1DiagonalIntegrals_of_twisted ℓ hℓ n _hn)

end AlgebraicGeometry.ProEtale
