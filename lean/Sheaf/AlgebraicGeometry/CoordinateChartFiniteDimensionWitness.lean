/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import Sheaf.AlgebraicGeometry.CoordinateSubspaceGenericStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# A finite local-dimension witness in an etale coordinate chart

Source: the nine-step coordinate-chart witness argument in the DAG; Stacks Project,
Tags 056G, 02GO, 03WT, 00E0, 00EU, 00OP, 07QP, 01HV and 0HA1
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).

The base is arbitrary. The structures over the base on `Y`, `T` and `Y ×[X] T`
are the ones induced by `i`, `e` and the pullback projections, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem generic_isMax {V : Scheme.{u}} {v : V} (hv : v ∈ genericPoints V) :
    IsMax v := by
  intro w hw
  change w ⤳ v at hw
  have hsub := hv.2 isIrreducible_singleton.closure hw.closure_subset
  change v ⤳ w
  exact specializes_iff_closure_subset.mpr hsub

private theorem flat_image_isMax {V S : Scheme.{u}} (f : V ⟶ S) [Flat f]
    (v : V) (hv : IsMax v) : IsMax (f v) := by
  intro s hs
  obtain ⟨v', hv', hv's⟩ := Flat.generalizingMap f (Scheme.le_iff_specializes.mp hs)
  have hle : v' ≤ v := hv (Scheme.le_iff_specializes.mpr hv')
  rw [Scheme.le_iff_specializes, ← hv's]
  exact (Scheme.le_iff_specializes.mp hle).map f.continuous

private theorem affine_prime_minimal {S : Scheme.{u}} (U : S.Opens) (hU : IsAffineOpen U)
    (x : U) (hx : IsMax x.val) : (hU.primeIdealOf x).asIdeal ∈ minimalPrimes Γ(S, U) := by
  apply PrimeSpectrum.isMin_iff.mp
  intro q hq
  have hle : (x : S) ≤ hU.fromSpec q := by
    rw [← hU.fromSpec_primeIdealOf x, Scheme.le_iff_specializes]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hq |>.map hU.fromSpec.continuous
  have hback := hx hle
  rw [← hU.fromSpec_primeIdealOf x, Scheme.le_iff_specializes] at hback
  exact (PrimeSpectrum.le_iff_specializes _ _).mpr
    (hU.fromSpec.isEmbedding.isInducing.specializes_iff.mp hback)

private theorem affine_fiber_generic {S : Scheme.{u}} (a : ℕ)
    (z : AffineSpace (ULift.{u} (Fin a)) S) (hz : IsMax z) :
    IsGenericPoint ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber z) Set.univ := by
  let π := AffineSpace (ULift.{u} (Fin a)) S ↘ S
  have hf : IsIrreducible (π ⁻¹' {π z}) :=
    π.isIrreducible_preimage (AffineSpace.isOpenMap_over S) isIrreducible_singleton
  let : IrreducibleSpace (π ⁻¹' {π z}) := Subtype.irreducibleSpace hf
  let : IrreducibleSpace (π.fiber (π z)) := (π.fiberHomeo _).irreducibleSpace_iff.mpr
    inferInstance
  have hmax : IsMax (π.asFiber z) := by
    intro w hw
    have hle : z ≤ π.fiberι (π z) w := by
      apply Scheme.le_iff_specializes.mpr
      simpa only [Scheme.Hom.fiberι_asFiber] using
        ((Scheme.le_iff_specializes.mp hw).map (π.fiberι _).continuous)
    rw [Scheme.le_iff_specializes]
    apply (π.fiberι _).isEmbedding.isInducing.specializes_iff.mp
    simpa only [Scheme.Hom.fiberι_asFiber] using Scheme.le_iff_specializes.mp (hz hle)
  have hle : π.asFiber z ≤ genericPoint (π.fiber (π z)) := genericPoint_specializes _
  have heq : π.asFiber z = genericPoint (π.fiber (π z)) :=
    (Scheme.le_iff_specializes.mp hle).antisymm
      (Scheme.le_iff_specializes.mp (hmax hle)) |>.eq.symm
  rw [heq]
  exact genericPoint_spec _

/-- Selection of the minimal-prime coordinate-chart point and its ambient polynomial prime.
Source: the nine-step coordinate-chart witness argument, Steps 1--4 and 9
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).
-/
private theorem coordinate_chart_selection
    {S X Y T : Scheme.{u}} (p : X ⟶ S) (i : Y ⟶ X) (e : T ⟶ X)
    [IsClosedImmersion i] [Etale e] (a b : ℕ)
    (h : T ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S) [Etale h]
    (coordinatesOver : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = e ≫ p)
    (g : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S)
    (cartesian : IsPullback g (pullback.snd i e)
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (nonemptySupport : Nonempty (pullback i e : Scheme.{u})) :
    ∃ (U : S.Opens) (hU : IsAffineOpen U) (s : PrimeSpectrum Γ(S, U))
        (t : (pullback i e : Scheme.{u})),
      s.asIdeal ∈ minimalPrimes Γ(S, U) ∧
      (pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s ∧
      Nonempty (s.asIdeal.ResidueField ≃+* FractionRing (Γ(S, U) ⧸ s.asIdeal)) ∧
      IsGenericPoint
        ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber (g t)) Set.univ ∧
      ∃ q : PrimeSpectrum
          (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))),
        q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
          MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)))) ∧
        Nonempty
          ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
              ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
                (h ((pullback.snd i e) t)))).presheaf.stalk
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber
              (h ((pullback.snd i e) t)))) ≃+* Localization.AtPrime q.asIdeal) := by
  let : Etale g := MorphismProperty.of_isPullback cartesian.flip inferInstance
  obtain ⟨z₀⟩ := nonemptySupport
  let t' := genericPoints.ofComponent
    ⟨irreducibleComponent z₀, irreducibleComponent_mem_irreducibleComponents z₀⟩
  let t : (pullback i e : Scheme.{u}) := t'.val
  have htm : IsMax t := generic_isMax t'.property
  have hgm := flat_image_isMax g t htm
  have hgen := affine_fiber_generic a (g t) hgm
  have hcomp : g ≫ (AffineSpace (ULift.{u} (Fin a)) S ↘ S) =
      pullback.fst i e ≫ i ≫ p := by
    rw [← AffineSpace.homOfVector_over
      (f := (AffineSpace (ULift.{u} (Fin a)) S ↘ S))
      (v := fun j : ULift.{u} (Fin (a + b)) ↦
        Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k)) (fun _ ↦ 0) j.down)]
    rw [← Category.assoc, cartesian.w, Category.assoc, coordinatesOver]
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  let : Smooth (AffineSpace (ULift.{u} (Fin a)) S ↘ S) :=
    SmoothOfRelativeDimension.smooth (n := Nat.card (ULift.{u} (Fin a))) _
  have hbase : IsMax ((pullback.fst i e ≫ i ≫ p) t) := by
    rw [← hcomp, Scheme.Hom.comp_apply]
    exact flat_image_isMax _ _ hgm
  obtain ⟨U, hU, hmem, _⟩ := exists_isAffineOpen_mem_and_subset
    (show (pullback.fst i e ≫ i ≫ p) t ∈ (⊤ : S.Opens) from trivial)
  let s := hU.primeIdealOf ⟨(pullback.fst i e ≫ i ≫ p) t, hmem⟩
  have hs : s.asIdeal ∈ minimalPrimes Γ(S, U) :=
    affine_prime_minimal U hU _ hbase
  have ht : (pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s :=
    (hU.fromSpec_primeIdealOf ⟨(pullback.fst i e ≫ i ≫ p) t, hmem⟩).symm
  refine ⟨U, hU, s, t, hs, ht, ?_, hgen, ?_⟩
  · exact ⟨(IsLocalization.algEquiv (nonZeroDivisors (Γ(S, U) ⧸ s.asIdeal))
      s.asIdeal.ResidueField (FractionRing (Γ(S, U) ⧸ s.asIdeal))).toRingEquiv⟩
  · have hz : (AffineSpace (ULift.{u} (Fin a)) S ↘ S) (g t) = hU.fromSpec s := by
      simpa only [← Scheme.Hom.comp_apply, hcomp] using ht
    have hnormal := coordinate_subspace_generic_fiber_stalk a b U hU s (g t) hz hgen
    have hc := congrArg (fun f ↦ f t) cartesian.w
    simp only [Scheme.Hom.comp_apply] at hc
    rw [← hc]
    exact hnormal


private theorem fiber_dimension_of_isMax {V S : Scheme.{u}} (f : V ⟶ S) (v : V)
    (hs : IsMax (f v)) :
    ringKrullDim (V.presheaf.stalk v) =
      ringKrullDim ((f.fiber (f v)).presheaf.stalk (f.asFiber v)) := by
  simp only [ringKrullDim_stalk_eq_coheight]
  have he := (f.fiberι (f v)).isEmbedding
  have hmono : StrictMono (f.fiberι (f v)) := by
    intro a b hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
    exact ⟨hab.1.map (f.fiberι (f v)).continuous,
      fun h ↦ hab.2 (he.isInducing.specializes_iff.mp h)⟩
  have hh := Order.coheight_eq_of_strictMono (f.fiberι (f v)) hmono (by
    intro a b hab
    have hb : f b = f v := by
      have hle : f (f.fiberι (f v) a) ≤ f b :=
        (Scheme.le_iff_specializes.mpr
          ((Scheme.le_iff_specializes.mp hab.le).map f.continuous))
      have ha : f (f.fiberι (f v) a) = f v := (f.fiberHomeo (f v) a).property
      rw [ha] at hle
      exact ((Scheme.le_iff_specializes.mp hle).antisymm
        (Scheme.le_iff_specializes.mp (hs hle))).eq
    have hr : b ∈ Set.range (f.fiberι (f v)) := by
      rw [f.range_fiberι]
      exact hb
    obtain ⟨b', hb'⟩ := hr
    refine ⟨b', ?_, hb'⟩
    rw [← hb'] at hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
    exact ⟨he.isInducing.specializes_iff.mp hab.1,
      fun h ↦ hab.2 (h.map (f.fiberι (f v)).continuous)⟩) (f.asFiber v)
  simpa using (congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hh).symm

private theorem affine_minimal_isMax {S : Scheme.{u}} (U : S.Opens) (hU : IsAffineOpen U)
    (s : PrimeSpectrum Γ(S, U)) (hs : s.asIdeal ∈ minimalPrimes Γ(S, U)) :
    IsMax (hU.fromSpec s) := by
  apply Order.coheight_eq_zero.mp
  have hd : ringKrullDim ((Spec Γ(S, U)).presheaf.stalk s) = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso Γ(S, U) s).commRingCatIsoToRingEquiv]
    let := Ring.KrullDimLE.of_isLocalization s.asIdeal hs (Localization.AtPrime s.asIdeal)
    exact le_antisymm (Ring.krullDimLE_iff.mp inferInstance)
      (ringKrullDim_nonneg_of_nontrivial (R := Localization.AtPrime s.asIdeal))
  have he := ringKrullDim_eq_of_ringEquiv
    (asIso (hU.fromSpec.stalkMap s)).commRingCatIsoToRingEquiv
  have hz := he.trans hd
  rw [ringKrullDim_stalk_eq_coheight] at hz
  exact_mod_cast hz

private theorem generic_dimension_zero (V : Scheme.{u}) (v : V)
    (hv : IsGenericPoint v Set.univ) : ringKrullDim (V.presheaf.stalk v) = 0 := by
  have hm : IsMax v := by
    intro w hw
    rw [Scheme.le_iff_specializes]
    exact hv.specializes (Set.mem_univ w)
  rw [ringKrullDim_stalk_eq_coheight, Order.IsMax.coheight_eq_zero hm]
  rfl

/-- Dimension and fibre-stalk equalities for a selected coordinate-chart point.
Source: the nine-step coordinate-chart witness argument, Steps 5--9
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).
-/
private theorem coordinate_chart_dimensions
    {S X Y T : Scheme.{u}} (p : X ⟶ S) (i : Y ⟶ X) (e : T ⟶ X)
    [IsClosedImmersion i] [Etale e] (a b : ℕ)
    (h : T ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S) [Etale h]
    (coordinatesOver : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = e ≫ p)
    (g : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S)
    (cartesian : IsPullback g (pullback.snd i e)
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (U : S.Opens) (hU : IsAffineOpen U) (s : PrimeSpectrum Γ(S, U))
    (t : (pullback i e : Scheme.{u}))
    (hs : s.asIdeal ∈ minimalPrimes Γ(S, U))
    (ht : (pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s)
    (hgen : IsGenericPoint
      ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber (g t)) Set.univ)
    (hq : ∃ q : PrimeSpectrum
          (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))),
        q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
          MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)))) ∧
        Nonempty
          ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
              ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
                (h ((pullback.snd i e) t)))).presheaf.stalk
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber
              (h ((pullback.snd i e) t)))) ≃+* Localization.AtPrime q.asIdeal)) :
    ringKrullDim ((pullback i e).presheaf.stalk t) = 0 ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) = 0 ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) = (b : WithBot ℕ∞) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) = (b : WithBot ℕ∞) ∧
      ringKrullDim ((pullback i e).presheaf.stalk t) =
        ringKrullDim (((pullback.fst i e ≫ i ≫ p).fiber
          ((pullback.fst i e ≫ i ≫ p) t)).presheaf.stalk
            ((pullback.fst i e ≫ i ≫ p).asFiber t)) ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) =
        ringKrullDim (((i ≫ p).fiber ((i ≫ p) ((pullback.fst i e) t))).presheaf.stalk
          ((i ≫ p).asFiber ((pullback.fst i e) t))) ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) =
        ringKrullDim (((e ≫ p).fiber ((e ≫ p) ((pullback.snd i e) t))).presheaf.stalk
          ((e ≫ p).asFiber ((pullback.snd i e) t))) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) =
        ringKrullDim ((p.fiber (p (i ((pullback.fst i e) t)))).presheaf.stalk
          (p.asFiber (i ((pullback.fst i e) t)))) := by
  have hg : Etale g := MorphismProperty.of_isPullback cartesian.flip inferInstance
  let := hg
  have hzbase : IsMax ((pullback.fst i e ≫ i ≫ p) t) := by
    rw [ht]
    exact affine_minimal_isMax U hU s hs
  have hybase : IsMax ((i ≫ p) ((pullback.fst i e) t)) := hzbase
  have hpoint : e ((pullback.snd i e) t) = i ((pullback.fst i e) t) := by
    have := congrArg (fun f ↦ f t) (pullback.condition (f := i) (g := e))
    exact this.symm
  have hTbase : IsMax ((e ≫ p) ((pullback.snd i e) t)) := by
    simpa only [Scheme.Hom.comp_apply, hpoint] using hzbase
  have hXbase : IsMax (p (i ((pullback.fst i e) t))) := hzbase
  have hgbase : IsMax ((AffineSpace (ULift.{u} (Fin a)) S ↘ S) (g t)) := by
    have hcomp : g ≫ (AffineSpace (ULift.{u} (Fin a)) S ↘ S) =
        pullback.fst i e ≫ i ≫ p := by
      rw [← AffineSpace.homOfVector_over
        (f := (AffineSpace (ULift.{u} (Fin a)) S ↘ S))
        (v := fun j : ULift.{u} (Fin (a + b)) ↦
          Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k)) (fun _ ↦ 0) j.down)]
      rw [← Category.assoc, cartesian.w, Category.assoc, coordinatesOver]
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    simpa only [← Scheme.Hom.comp_apply, hcomp] using hzbase
  have hhbase : IsMax ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
      (h ((pullback.snd i e) t))) := by
    have hhpoint : (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
        (h ((pullback.snd i e) t)) = (e ≫ p) ((pullback.snd i e) t) := by
      rw [← Scheme.Hom.comp_apply, coordinatesOver]
    rwa [hhpoint]
  have hgf := fiber_dimension_of_isMax
    (AffineSpace (ULift.{u} (Fin a)) S ↘ S) (g t) hgbase
  have hzero : ringKrullDim
      ((AffineSpace (ULift.{u} (Fin a)) S).presheaf.stalk (g t)) = 0 :=
    hgf.trans (generic_dimension_zero _ _ hgen)
  have hnormal : ringKrullDim
      ((AffineSpace (ULift.{u} (Fin (a + b))) S).presheaf.stalk
        (h ((pullback.snd i e) t))) = (b : WithBot ℕ∞) := by
    rw [fiber_dimension_of_isMax _ _ hhbase]
    obtain ⟨q, hq, ⟨eqv⟩⟩ := hq
    rw [ringKrullDim_eq_of_ringEquiv eqv]
    obtain ⟨hp, _, _, hd, _, _⟩ := MvPolynomial.polynomial_origin_regularLocal
      (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)) b
    let origin := Ideal.span (Set.range (MvPolynomial.X : Fin b →
      MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))))
    have : origin.IsPrime := hp.isPrime
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height origin] at hd
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hq]
    exact hd
  have hz : ringKrullDim ((pullback i e).presheaf.stalk t) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hzero ⊢
    rw [← g.coheight_apply_of_flat t]
    exact hzero
  have hy : ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, (pullback.fst i e).coheight_apply_of_flat]
    simpa only [ringKrullDim_stalk_eq_coheight] using hz
  have hT : ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) =
      (b : WithBot ℕ∞) := by
    rw [ringKrullDim_stalk_eq_coheight, ← h.coheight_apply_of_flat]
    simpa only [ringKrullDim_stalk_eq_coheight] using hnormal
  have hX : ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) =
      (b : WithBot ℕ∞) := by
    rw [← hpoint, ringKrullDim_stalk_eq_coheight, e.coheight_apply_of_flat]
    simpa only [ringKrullDim_stalk_eq_coheight] using hT
  exact ⟨hz, hy, hT, hX, fiber_dimension_of_isMax _ _ hzbase,
    fiber_dimension_of_isMax _ _ hybase, fiber_dimension_of_isMax _ _ hTbase,
    fiber_dimension_of_isMax _ _ hXbase⟩


/-- A nonempty simultaneous-coordinate chart has a point over a minimal base prime
where the support local rings have dimension zero and the ambient local rings have
dimension `b`. The affine open is `U = Spec Γ(S,U)`. Its prime `s` has residue field
`κ(s)`, canonically the fraction field of `Γ(S,U)/s`. `asFiber` denotes the unique
point above the displayed point. Thus genericity is asserted in the actual
scheme-theoretic affine-space fibre, and the last ring equivalence gives its ambient
local ring as `κ(s)(u₁,…,uₐ)[v₁,…,v_b]_(v₁,…,v_b)`.
Source: Stacks 056G and the extracted coordinate-model argument, steps 1--9
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).

Proof:
1. The cartesian square makes `g` etale by etale base change
   [lem-weil-pbc-etale-scheme-base-change], as is `Z → Y`. Choose an affine base open
   meeting `Z`. The image of `g` there is a nonempty open in affine space
   [lem-weil-pbc-etale-morphism-open-map].
2. For a prime `P` in this image choose a minimal base prime `s ⊆ P ∩ R`
   [lem-weil-pbc-prime-contains-minimal-prime]. The polynomial prime `s R[u] ⊆ P`
   lies in this open, since opens contain generizations. Lift it through `g` to `t`.
3. Reducing and localizing sends `s R[u]` to the zero prime of `κ(s)[u]`.
   This is the generic point, whose local ring is `K = Frac(κ(s)[u])`
   [def-weil-pbc-localization-at-prime, lem-weil-pbc-affine-open-stalk-localization].
4. The ambient image prime is `(v)` in `κ(s)[u,v]`. Its localization is `K[v]_(v)`:
   nonzero polynomials in `u` are inverted already; clearing the finitely many
   `u`-denominators constructs the inverse localization homomorphism.
5. The tangential field has dimension zero. The polynomial-origin lemma gives
   dimension `b` for the ambient local ring
   [lem-weil-pbc-polynomial-ring-origin-regular-local], including `b = 0`.
6. Base change makes both fibre chart maps etale. Affine stalk localization and
   [lem-sc-etale-local-dimension] give dimensions zero and `b` on the source fibres.
7. At a minimal base prime the maximal ideal of `R_s` consists of nilpotents
   [lem-weil-pbc-minimal-prime-reduced-localization-field]. Its extension to each
   of the four local rings is nil: a finite sum of nilpotent multiples is nilpotent
   by the multinomial expansion. No uniform nilpotence exponent is needed.
8. [lem-sbc-scheme-fibre-stalk-quotient] identifies each fibre stalk with the quotient
   by this nil ideal. Every prime contains it, so quotient and contraction identify
   all strict prime chains and preserve their dimension suprema.
9. Apply [lem-sc-etale-local-dimension] to `Z → Y` and `T → X`, using affine stalk
   localization, to get the two remaining local dimensions. The pullback equation
   identifies the two images in `X`. These are all the required witnesses. -/
theorem Scheme.Hom.exists_coordinate_chart_finite_dimension_witness
    {S X Y T : Scheme.{u}} (p : X ⟶ S) (i : Y ⟶ X) (e : T ⟶ X)
    [IsClosedImmersion i] [Etale e] (a b : ℕ)
    (h : T ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S) [Etale h]
    (coordinatesOver :
      h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = e ≫ p)
    (g : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S)
    (cartesian : IsPullback g (pullback.snd i e)
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (nonemptySupport : Nonempty (pullback i e : Scheme.{u})) :
    ∃ (U : S.Opens) (hU : IsAffineOpen U) (s : PrimeSpectrum Γ(S, U))
        (t : (pullback i e : Scheme.{u})),
      s.asIdeal ∈ minimalPrimes Γ(S, U) ∧
      (pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s ∧
      Nonempty (s.asIdeal.ResidueField ≃+* FractionRing (Γ(S, U) ⧸ s.asIdeal)) ∧
      IsGenericPoint
        ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber (g t)) Set.univ ∧
      ringKrullDim ((pullback i e).presheaf.stalk t) = 0 ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) = 0 ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) = (b : WithBot ℕ∞) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) = (b : WithBot ℕ∞) ∧
      ringKrullDim ((pullback i e).presheaf.stalk t) =
        ringKrullDim (((pullback.fst i e ≫ i ≫ p).fiber
          ((pullback.fst i e ≫ i ≫ p) t)).presheaf.stalk
            ((pullback.fst i e ≫ i ≫ p).asFiber t)) ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) =
        ringKrullDim (((i ≫ p).fiber ((i ≫ p) ((pullback.fst i e) t))).presheaf.stalk
          ((i ≫ p).asFiber ((pullback.fst i e) t))) ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) =
        ringKrullDim (((e ≫ p).fiber ((e ≫ p) ((pullback.snd i e) t))).presheaf.stalk
          ((e ≫ p).asFiber ((pullback.snd i e) t))) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) =
        ringKrullDim ((p.fiber (p (i ((pullback.fst i e) t)))).presheaf.stalk
          (p.asFiber (i ((pullback.fst i e) t)))) ∧
      ∃ q : PrimeSpectrum
          (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))),
        q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
          MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)))) ∧
        Nonempty
          ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
              ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
                (h ((pullback.snd i e) t)))).presheaf.stalk
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber
              (h ((pullback.snd i e) t)))) ≃+* Localization.AtPrime q.asIdeal) := by
  obtain ⟨U, hU, s, t, hs, ht, hres, hgen, hq⟩ :=
    coordinate_chart_selection p i e a b h coordinatesOver g cartesian nonemptySupport
  obtain ⟨hz, hy, hT, hX, hzf, hyf, hTf, hXf⟩ :=
    coordinate_chart_dimensions p i e a b h coordinatesOver g cartesian U hU s t hs ht hgen hq
  refine ⟨U, hU, s, t, hs, ht, hres, hgen, hz, hy, hT, hX, hzf, hyf, hTf, hXf, hq⟩

end AlgebraicGeometry
