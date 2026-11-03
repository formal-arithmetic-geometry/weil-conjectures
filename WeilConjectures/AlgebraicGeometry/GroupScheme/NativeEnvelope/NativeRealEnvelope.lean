/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeEnvelopeReality
public import Mathlib.LinearAlgebra.Trace
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Pure.ConstantTwistWeight
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleClosedDetection
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.LocalPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Twisting to weight zero and adding the dual

Source: latest blueprint, part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-and-the-growth-of-squared-traces/sk-prop-wrp-real-envelope/_section.md,
F-clause and Complement (blueprint: sk-prop-wrp-real-envelope).

The positive-power trace form covers points over every finite extension: at a point
of degree d over k_n, d divides n and its operator is the n/d-th closed-point power.
Conversely every positive closed-point power occurs over k_(d*m).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeEnvelope

/-- Native scalar fibres of lisse coefficient modules are finite dimensional.
Source: lem-wf-envelope-real, finite-rank local calculation;
lem-zl-condensed-lisse-fibres-finite, finite-free-cover proof.
(blueprint: lem-zl-condensed-lisse-fibres-finite).

Proof: lift the algebraically closed point through a member of a finite-free
trivializing pro-etale cover. Pull the chosen free model to the point, using the
pullback composition isomorphism. Actual unit sections are additive, so preserve the
finite biproduct of coefficient units. Identify each unit's sections with the lifted
coefficient field. This gives coordinates K^r on the native fibre and transports
finite dimensionality. This includes r = 0. -/
private theorem native_fibre_finite
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (L : NativeCondensedModule.Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L)
    (z : Spec (.of D.k) ⟶ T) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D L z) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨U, hU⟩ := hL
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale z
  subst z
  have hfree := (hU i).map
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l) g)
  have hcomp := hfree.of_iso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g (U.f i)).app L).symm
  obtain ⟨r, ⟨e⟩⟩ := hcomp
  let H := NativeCondensedModule.pointSections l D.k
  have : H.Additive := by
    dsimp [H, NativeCondensedModule.pointSections]
    infer_instance
  let R := condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k))
  let eV := H.mapIso e ≪≫ H.mapBiproduct (fun _ : Fin r => Mod.regular R) ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin r => H.obj (Mod.regular R))
  let d := eV.toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun _ : Fin r =>
      (NativeCondensedModule.pointSectionsUnitIso l D.k).symm.toLinearEquiv)
  exact LinearEquiv.finiteDimensional d.symm

/-- The native transport used as the local Frobenius field.
Source: the local Frobenius operator definition
(blueprint: def-weil-local-frobenius-trace). -/
private def localFrobeniusTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    NativeCondensedModule.fibre l D M.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x i hi) ≅
      NativeCondensedModule.fibre l D M.carrier
        (NativeCondensedModule.localClosedPoint D X₀ x i hi) :=
  NativeCondensedModule.transport l D (D.geometricFrobenius X₀).hom M.carrier M.str
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
    (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
    (NativeCondensedModule.localClosedPoint_return D X₀ x i hi)

/-- Package an actual module and its automorphism with their given module structures. -/
private def frobeniusOfModuleIso
    {K : Type u} [Field K] (V : ModuleCat.{u} K)
    (hV : FiniteDimensional K V) (e : V ≅ V) : FrobeniusModule.{u, u} K :=
  { carrier := V
    addCommGroup := V.isAddCommGroup
    module := V.isModule
    finiteDimensional := hV
    frobenius := e.toLinearEquiv }

/-- The concrete Frobenius module on the native scalar fibre of a lisse Weil module.
Finite dimensionality is a proved property, and the automorphism is the existing
native transport. No vector space or automorphism is selected by existence.
Source: local-factor calculation of lem-wf-envelope-real.
(blueprint: def-weil-local-frobenius-trace). -/
private def localFrobeniusModule
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    FrobeniusModule.{u + 1, u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  frobeniusOfModuleIso
    (NativeCondensedModule.fibre l D M.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x i hi))
    (native_fibre_finite l D M.carrier hM _)
    (localFrobeniusTransport D l X₀ M x i hi)

private theorem charpoly_eq_of_localPolynomial_eq
    {K : Type u} [Field K] (M N : FrobeniusModule.{u, u} K)
    (h : M.localPolynomial = N.localPolynomial) :
    M.frobeniusEnd.charpoly = N.frobeniusEnd.charpoly := by
  have hd : Module.finrank K M.carrier = Module.finrank K N.carrier := by
    simpa only [FrobeniusModule.natDegree_localPolynomial] using
      congrArg Polynomial.natDegree h
  have hh := congrArg (fun p : Polynomial K ↦ p.reflect (Module.finrank K M.carrier)) h
  simpa only [FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def,
    Polynomial.reverse, LinearMap.charpoly_natDegree, hd, Polynomial.reflect_reflect] using hh

section Local

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem local_frobenius_eq
    (M : NativeL2.WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀ M hM x i hi).frobenius =
      (localFrobeniusTransport D l X₀ M x i hi).toLinearEquiv := by
  rfl

private theorem local_end_eq
    (M : NativeL2.WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀ M hM x i hi).frobeniusEnd =
      (NativeL2.closedOperator D l X₀ M x i hi).hom := by
  rw [FrobeniusModule.frobeniusEnd, local_frobenius_eq,
    CategoryTheory.Iso.toLinearMap_toLinearEquiv]
  rw [NativeL2.closedOperator, NativeCondensedModule.operator]
  rfl

private theorem pure_local_module
    (M : NativeL2.WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (hp : NativeL2.Pure D l X₀ M iota w)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀ M hM x i hi).IsPureOfWeight
      (iota.comp ULift.ringEquiv.toRingHom) (Nat.card (X₀.left.residueField x.val)) w := by
  intro α hα
  apply hp x i hi α
  rwa [local_end_eq D l X₀ M hM x i hi] at hα

end Local

private theorem lisse_constructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (F : NativeL2.WeilModule D l X₀)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left F.carrier := by
  classical
  let Y := (D.geometricFiber X₀).left
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber X₀).hom := inferInstanceAs
    (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom }
  let S : Y.FiniteLocallyClosedStratification :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ Y
      immersion := fun _ ↦ 𝟙 Y
      isImmersion := fun _ ↦ inferInstance
      range_immersion := fun _ ↦ Set.range_id' }
  apply ((coefficientHeart_closure l (Profinite.padicAlgClCondensedRing l)
    (Or.inr rfl)).2 Y).2.2.2.2.2.2 F.carrier |>.mpr
  refine ⟨S, fun _ ↦ ?_⟩
  exact (isLocallyFree_iff _).mp (((isLocallyFree_iff _).mpr hF).of_iso
    ((CondensedRing.upperStarId (Profinite.padicAlgClRingObj l) Y).app F.carrier).symm)

private theorem normalizing_scalar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : NativeL2.WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hne : ¬ IsZero F)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (hpure : NativeL2.Pure D l X₀ F iota w) :
    ∃ b : (PadicAlgCl l)ˣ, ‖iota b‖ = (D.q : ℝ) ^ (-w / 2) := by
  classical
  have hcons := lisse_constructible D l X₀ F hF
  have hncarrier : ¬ IsZero F.carrier := by
    intro hz
    apply hne
    apply (IsZero.iff_id_eq_zero F).mpr
    apply (CategoryTheory.Endofunctor.IsoAlgebra.forget _).map_injective
    exact hz.eq_of_src _ _
  obtain ⟨x, hx, i, hi, z, hz₁, hz₂, hz⟩ :=
    condensed_constructible_closed_detection D l hl X₀ ⟨F.carrier, hcons⟩ hncarrier
  let x' : {x : X₀.left // x ∈ closedPoints X₀.left} := ⟨x, hx⟩
  have hzeq : z = NativeCondensedModule.localClosedPoint D X₀ x' i hi := by
    apply pullback.hom_ext
    · simpa only [NativeCondensedModule.localClosedPoint, pullback.lift_fst] using hz₁
    · rw [NativeCondensedModule.localClosedPoint, pullback.lift_snd]
      exact hz₂
  subst z
  have := hz
  let N := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (NativeCondensedModule.localClosedPoint D X₀ x' i hi)).obj F.carrier
  let e := (Mod.regularHomAddEquiv N).trans
    (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId _) N.X)
  have hnontrivial : Nontrivial (NativeCondensedModule.fibre l D F.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x' i hi)) := e.toEquiv.nontrivial
  let M := localFrobeniusModule D l X₀ F hF x' i hi
  let : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    isAlgClosed_ulift_padic l
  let : Nontrivial M.carrier := hnontrivial
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue M.frobeniusEnd
  have hαzero : α.down ≠ 0 := by
    intro h
    apply FrobeniusModule.ne_zero_of_hasEigenvalue hα
    apply ULift.ext
    exact h
  let := (X₀.hom.residueFieldAlgebraMap x).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x).2.1.mp hx
  have : Finite (X₀.left.residueField x) := Module.finite_of_finite D.k₀
  let d := NativeCondensedModule.localClosedPointDegree D X₀ x'
  have hd : 0 < d := Module.finrank_pos
  have hc : Nat.card (X₀.left.residueField x) = D.q ^ d := by
    simpa only [d, NativeCondensedModule.localClosedPointDegree, D.card_base] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := X₀.left.residueField x))
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq α.down⁻¹ hd
  have hbzero : b ≠ 0 := by
    intro h
    exact (inv_ne_zero hαzero) (by simpa [h, hd.ne'] using hb.symm)
  refine ⟨Units.mk0 b hbzero, ?_⟩
  change ‖iota b‖ = _
  apply (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hd.ne').mp
  have hnorm := pure_local_module D l X₀ F hF iota w hpure x' i hi α hα
  change ‖iota α.down‖ = (Nat.card (X₀.left.residueField x) : ℝ) ^ (w / 2) at hnorm
  have hq : (0 : ℝ) < D.q := by
    rw [← D.card_base]
    exact_mod_cast (Nat.card_pos : 0 < Nat.card D.k₀)
  calc
    ‖iota b‖ ^ d = ‖iota (b ^ d)‖ := by rw [map_pow, norm_pow]
    _ = ‖iota α.down‖⁻¹ := by rw [hb, map_inv₀, norm_inv]
    _ = (((D.q : ℝ) ^ d) ^ (w / 2))⁻¹ := by
      rw [hnorm, hc, Nat.cast_pow]
    _ = ((D.q : ℝ) ^ (-w / 2)) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_neg hq.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      congr 1
      ring

/-- A lisse coefficient module is constructible in the native module-object category:
use the one-stratum decomposition and local finite presentation of finite free models. -/
private theorem lisse_native_constructible
    (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}}
    (F : NativeCondensedModule.Modules l Y)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj l) Y) F := by
  let S : Scheme.Stratification Y :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ Y
      immersion := fun _ ↦ 𝟙 Y
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  apply (CondensedRing.isLocallyFinitelyPresented_mapMod_iff
    (Profinite.padicAlgClRingObj l) (S.immersion a) F).mpr
  exact (((isLocallyFree_iff F).mpr hF).upperStar
    (Profinite.padicAlgClRingObj l) (S.immersion a)).isLocallyFinitelyPresented

private theorem normalized_pure_zero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (F : NativeL2.WeilModule D l X₀)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hpure : NativeL2.Pure D l X₀ F iota w) (b : (PadicAlgCl l)ˣ)
    (hb : ‖iota b‖ = (D.q : ℝ) ^ (-w / 2)) :
    NativeL2.Pure D l X₀ (normalizedTwist D l X₀ hl F b) iota 0 := by
  let Fc : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom := ⟨F, lisse_native_constructible l F.carrier hF⟩
  have hq : (0 : ℝ) < D.q := by
    rw [← D.card_base]
    exact_mod_cast (Nat.card_pos : 0 < Nat.card D.k₀)
  have hqne : (D.q : ℝ) ≠ 1 := by
    have h : 1 < D.q := by simpa only [D.card_base] using
      (Finite.one_lt_card (α := D.k₀))
    exact ne_of_gt (by exact_mod_cast h)
  have hlog : 2 * Real.logb (Nat.card D.k₀) ‖iota b‖ = -w := by
    rw [hb, D.card_base, Real.logb_rpow hq hqne]
    ring
  have h := NativeL2.Pure.constantTwist D l hl X₀ Fc iota w (-w) hpure b hlog
  simpa only [add_neg_cancel, normalizedTwist, CondensedFibreLinearCurrent.tensorWeil,
    CondensedRing.ConstantWeil.twist, CondensedRing.ConstantWeil.line, Fc] using h

private theorem sumIsoAlgebra_retract
    {C : Type*} [Category C] [Preadditive C] [HasFiniteProducts C]
    (G : C ⥤ C) [G.Additive] [PreservesFiniteProducts G] (n : ℕ)
    (F : Fin n → CategoryTheory.Endofunctor.IsoAlgebra G) (j : Fin n) :
    let E := CategoryTheory.Endofunctor.IsoAlgebra.mk (∏ᶜ fun k ↦ (F k).carrier)
      (PreservesProduct.iso G (fun k ↦ (F k).carrier) ≪≫ Pi.mapIso (fun k ↦ (F k).str))
    ∃ (a : F j ⟶ E) (r : E ⟶ F j), a ≫ r = 𝟙 (F j) := by
  classical
  dsimp only
  let E := CategoryTheory.Endofunctor.IsoAlgebra.mk (∏ᶜ fun k ↦ (F k).carrier)
    (PreservesProduct.iso G (fun k ↦ (F k).carrier) ≪≫ Pi.mapIso (fun k ↦ (F k).str))
  let d : ∀ k, (F j).carrier ⟶ (F k).carrier :=
    fun k ↦ if h : j = k then eqToHom (congrArg (fun k ↦ (F k).carrier) h) else 0
  have he (k : Fin n) : G.map (d k) ≫ (F k).str.hom = (F j).str.hom ≫ d k := by
    by_cases h : j = k
    · subst k; simp [d]
    · simp [d, h]
  let a : F j ⟶ E :=
    ⟨{ f := Pi.lift d
       h := by
        apply Pi.hom_ext
        intro k
        change (G.map (Pi.lift d) ≫
            ((PreservesProduct.iso G (fun k ↦ (F k).carrier)).hom ≫
              (Pi.mapIso (fun k ↦ (F k).str)).hom)) ≫ Pi.π _ k =
          ((F j).str.hom ≫ Pi.lift d) ≫ Pi.π _ k
        simp only [Category.assoc, Pi.mapIso_hom_π, PreservesProduct.iso_hom,
          piComparison_comp_π_assoc, Pi.lift_π]
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Pi.lift_π]
        exact he k }⟩
  let r : E ⟶ F j :=
    ⟨{ f := Pi.π (fun k ↦ (F k).carrier) j
       h := by
        change G.map (Pi.π _ j) ≫ (F j).str.hom =
          ((PreservesProduct.iso G (fun k ↦ (F k).carrier)).hom ≫
            (Pi.mapIso (fun k ↦ (F k).str)).hom) ≫ Pi.π _ j
        simp only [Category.assoc, Pi.mapIso_hom_π, PreservesProduct.iso_hom,
          piComparison_comp_π_assoc] }⟩
  refine ⟨a, r, ?_⟩
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Endofunctor.Algebra.Hom.ext
  change Pi.lift d ≫ Pi.π _ j = 𝟙 _
  simp [d]

/-- Evaluate a linear equivalence through its specified coordinate projection. -/
private theorem linearEquiv_projection
    {K : Type u} [Field K] {A : ModuleCat.{u} K}
    (B : (Fin 2) → ModuleCat.{u} K) (e : A ≅ ModuleCat.of K (∀ j, B j))
    (j : (Fin 2)) (f : A ⟶ B j)
    (h : e.hom ≫ ModuleCat.ofHom (LinearMap.proj j) = f) (v : A) :
    e.toLinearEquiv v j = f.hom v := by
  have hv := congrArg (fun f : A ⟶ B j ↦ f.hom v) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.proj_apply] at hv ⊢
  exact hv

/-- The canonical scalar coordinates supplied by a product comparison. -/
@[irreducible] private def piCoordinates
    {K : Type u} [Field K] {C : Type*} [Category C]
    (H : C ⥤ ModuleCat.{u} K) (B : Fin 2 → C) [HasProduct B]
    [IsIso (piComparison H B)] :
    H.obj (∏ᶜ B) ≃ₗ[K] ∀ j, H.obj (B j) :=
  (asIso (piComparison H B) ≪≫ ModuleCat.piIsoPi (fun j ↦ H.obj (B j))).toLinearEquiv

/-- A product comparison intertwines operators when its projections do. -/
private theorem pi_comparison_operator
    {K : Type u} [Field K] {C : Type*} [Category C]
    (H : C ⥤ ModuleCat.{u} K) (B : (Fin 2) → C) [HasProduct B]
    [IsIso (piComparison H B)]
    (a : End (H.obj (∏ᶜ B))) (b : ∀ j, End (H.obj (B j)))
    (h : ∀ j, a ≫ H.map (Pi.π B j) = H.map (Pi.π B j) ≫ b j)
    (v : H.obj (∏ᶜ B)) (j : (Fin 2)) :
    piCoordinates H B (a.hom v) j = (b j).hom (piCoordinates H B v j) := by
  unfold piCoordinates
  let pe := asIso (piComparison H B) ≪≫ ModuleCat.piIsoPi (fun j ↦ H.obj (B j))
  have hp (v : H.obj (∏ᶜ B)) (j : (Fin 2)) :
      pe.toLinearEquiv v j = (H.map (Pi.π B j)).hom v := by
    apply linearEquiv_projection (fun j ↦ H.obj (B j)) pe j (H.map (Pi.π B j))
    simp only [pe, Iso.trans_hom, Category.assoc,
      ModuleCat.piIsoPi_hom_ker_subtype, asIso_hom, piComparison_comp_π]
  change pe.toLinearEquiv (a.hom v) j = (b j).hom (pe.toLinearEquiv v j)
  rw [hp, hp]
  have hj := congrArg (fun f : H.obj (∏ᶜ B) ⟶ H.obj (B j) ↦ f.hom v) (h j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hj

/-- Turn a fixed two-term family of modules into ordinary pair coordinates. -/
@[irreducible] private def twoCoordinates
    {K : Type u} [Field K] {A : Type*} (H : A → ModuleCat.{u} K) (a b : A)
    {V : Type u} [AddCommGroup V] [Module K V]
    (p : V ≃ₗ[K] ∀ j : Fin 2,
      H (@ite A (j.val = 0) (Nat.decEq j.val 0) a b)) :
    V ≃ₗ[K] H a × H b :=
  p.trans (LinearEquiv.piFinTwo K
    (fun j : Fin 2 ↦ H (@ite A (j.val = 0) (Nat.decEq j.val 0) a b)))

private theorem twoCoordinates_fst
    {K : Type u} [Field K] {A : Type*} (H : A → ModuleCat.{u} K) (a b : A)
    {V : Type u} [AddCommGroup V] [Module K V]
    (p : V ≃ₗ[K] ∀ j : Fin 2,
      H (@ite A (j.val = 0) (Nat.decEq j.val 0) a b)) (v : V) :
    (twoCoordinates H a b p v).1 = p v 0 := by
  unfold twoCoordinates
  rfl

private theorem twoCoordinates_snd
    {K : Type u} [Field K] {A : Type*} (H : A → ModuleCat.{u} K) (a b : A)
    {V : Type u} [AddCommGroup V] [Module K V]
    (p : V ≃ₗ[K] ∀ j : Fin 2,
      H (@ite A (j.val = 0) (Nat.decEq j.val 0) a b)) (v : V) :
    (twoCoordinates H a b p v).2 = p v 1 := by
  unfold twoCoordinates
  rfl

/-- A product decomposition with the inverse-transpose second component identifies
its Frobenius polynomial with that of a module and its dual. -/
private theorem polynomial_eq_of_components
    {K : Type u} [Field K] (M N : FrobeniusModule.{u, u} K)
    {V : Type u} [AddCommGroup V] [Module K V]
    (p : N.carrier ≃ₗ[K] M.carrier × V)
    (d : V ≃ₗ[K] Module.Dual K M.carrier)
    (h₀ : ∀ v, (p (N.frobeniusEnd v)).1 = M.frobeniusEnd (p v).1)
    (h₁ : ∀ v a, d (p (N.frobeniusEnd v)).2 a = d (p v).2 (M.frobenius.symm a)) :
    N.localPolynomial = (M.prod M.dual).localPolynomial := by
  let e := p.trans ((LinearEquiv.refl K M.carrier).prodCongr d)
  apply FrobeniusModule.Equiv.localPolynomial_eq
  refine { toLinearEquiv := e, map_frobenius := ?_ }
  intro v
  apply Prod.ext
  · exact h₀ v
  · apply LinearMap.ext
    intro a
    exact h₁ v a

/-- The polynomial comparison on an explicitly specified module and automorphism. -/
private theorem polynomial_eq_of_module_iso_components
    {K : Type u} [Field K] (V : ModuleCat.{u} K)
    (hV : FiniteDimensional K V) (e : V ≅ V) (N : FrobeniusModule.{u, u} K)
    {W : Type u} [AddCommGroup W] [Module K W]
    (p : N.carrier ≃ₗ[K] V × W) (d : W ≃ₗ[K] Module.Dual K V)
    (h₀ : ∀ v, (p (N.frobeniusEnd v)).1 = e.hom.hom (p v).1)
    (h₁ : ∀ v a, d (p (N.frobeniusEnd v)).2 a = d (p v).2 (e.inv.hom a)) :
    N.localPolynomial =
      ((frobeniusOfModuleIso V hV e).prod (frobeniusOfModuleIso V hV e).dual).localPolynomial :=
  polynomial_eq_of_components (frobeniusOfModuleIso V hV e) N p d h₀ h₁

/-- An abstract two-term family needs only its two projection equations and the
inverse-transpose equation to determine the product polynomial. -/
private theorem polynomial_eq_of_pair_coordinates
    {K : Type u} [Field K] {A : Type*} (Q : A → ModuleCat.{u} K)
    (t : ∀ a, Q a ≅ Q a) (a b : A) (ha : FiniteDimensional K (Q a))
    (N : FrobeniusModule.{u, u} K)
    (p : N.carrier ≃ₗ[K] ∀ j : Fin 2,
      Q (@ite A (j.val = 0) (Nat.decEq j.val 0) a b))
    (d : Q b ≃ₗ[K] Module.Dual K (Q a))
    (hp : ∀ v j, p (N.frobeniusEnd v) j =
      (t (@ite A (j.val = 0) (Nat.decEq j.val 0) a b)).hom.hom (p v j))
    (hd : ∀ v x, d ((t b).hom.hom v) x = d v ((t a).inv.hom x)) :
    N.localPolynomial =
      ((frobeniusOfModuleIso (Q a) ha (t a)).prod
        (frobeniusOfModuleIso (Q a) ha (t a)).dual).localPolynomial := by
  let p' := twoCoordinates Q a b p
  apply polynomial_eq_of_module_iso_components (Q a) ha (t a) N p' d
  · intro v
    have hL := twoCoordinates_fst Q a b p (N.frobeniusEnd v)
    have hR := twoCoordinates_fst Q a b p v
    exact hL.trans ((hp v 0).trans (congrArg (fun x ↦ (t a).hom.hom x) hR.symm))
  · intro v x
    have hL := twoCoordinates_snd Q a b p (N.frobeniusEnd v)
    have hR := twoCoordinates_snd Q a b p v
    exact (congrArg (fun y ↦ d y x) (hL.trans (hp v 1))).trans
      ((hd (p v 1) x).trans (congrArg (fun y ↦ d y ((t a).inv.hom x)) hR.symm))

private theorem property_if {A : Type*} (P : A → Prop) (a b : A)
    (ha : P a) (hb : P b) (q : Prop) [Decidable q] : P (if q then a else b) := by
  split_ifs
  · exact ha
  · exact hb

attribute [local irreducible] NativeCondensedModule.operator
  NativeCondensedModule.pointSections

/-- The fixed two-term family used for the native dual envelope. -/
private abbrev dualPair
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (F : NativeL2.WeilModule D l X₀) : Fin 2 → NativeL2.WeilModule D l X₀ :=
  fun j ↦ @ite _ (j.val = 0) (Nat.decEq j.val 0) F
    (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) F)

/-- The actual finite sum of the fixed native dual pair. -/
private abbrev sumDual
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (F : NativeL2.WeilModule D l X₀) : NativeL2.WeilModule D l X₀ :=
  CondensedFibreLinearCurrent.sumWeil l (D.geometricFrobenius X₀) 2 (dualPair D l X₀ F)

/-- The dual/product polynomial calculation at an arbitrary returning geometric point.
The sum projections give product coordinates. The specified dual evaluation identifies
the second component with inverse transpose, so the abstract pair calculation applies. -/
private theorem native_dual_polynomial
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower g.hom n =
      NativeCondensedModule.localPositivePower (NativeCondensedModule.frobeniusPointIso D).hom
        n ≫ z)
    (F : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (hcons : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T F.carrier)
    (hdcons : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T
      (CondensedFibreLinearCurrent.dualWeil l g F).carrier)
    (hS : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (CondensedFibreLinearCurrent.sumWeil l g 2 (fun j : Fin 2 ↦
        @ite _ (j.val = 0) (Nat.decEq j.val 0) F
          (CondensedFibreLinearCurrent.dualWeil l g F))).carrier)
    (c : CondensedFibreLinearCurrent.Comparisons l D g z)
    (hc : CondensedFibreLinearCurrent.WeilCompatibility l D g z n h c) :
    let G := fun j : Fin 2 ↦ @ite _ (j.val = 0) (Nat.decEq j.val 0) F
      (CondensedFibreLinearCurrent.dualWeil l g F)
    let S := CondensedFibreLinearCurrent.sumWeil l g 2 G
    let M := frobeniusOfModuleIso (NativeCondensedModule.fibre l D F.carrier z)
      (native_fibre_finite l D F.carrier hF z)
      (NativeCondensedModule.transport l D g.hom F.carrier F.str z z n h)
    let N := frobeniusOfModuleIso (NativeCondensedModule.fibre l D S.carrier z)
      (native_fibre_finite l D S.carrier hS z)
      (NativeCondensedModule.transport l D g.hom S.carrier S.str z z n h)
    N.localPolynomial = (M.prod M.dual).localPolynomial := by
  let K := ULift.{u + 1} (PadicAlgCl l)
  let G := fun j : Fin 2 ↦ @ite _ (j.val = 0) (Nat.decEq j.val 0) F
    (CondensedFibreLinearCurrent.dualWeil l g F)
  let S := CondensedFibreLinearCurrent.sumWeil l g 2 G
  let Q : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) → ModuleCat.{u + 1} K :=
    fun L ↦ NativeCondensedModule.fibre l D L.carrier z
  let t : ∀ L, Q L ≅ Q L := fun L ↦
    NativeCondensedModule.transport l D g.hom L.carrier L.str z z n h
  let N := frobeniusOfModuleIso (Q S) (native_fibre_finite l D S.carrier hS z) (t S)
  let H := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
    NativeCondensedModule.pointSections l D.k
  have hG : ∀ j, IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T
      (G j).carrier := fun j ↦ property_if
    (fun L : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier)
    F (CondensedFibreLinearCurrent.dualWeil l g F) hcons hdcons (j.val = 0)
  obtain ⟨hiso, hproj⟩ := hc.sum_frobenius 2 G hG
  let := hiso
  let p := piCoordinates H (fun j ↦ (G j).carrier)
  have hp : ∀ v j, p (N.frobeniusEnd v) j = (t (G j)).hom.hom (p v j) := by
    intro v j
    have hj := pi_comparison_operator H (fun j ↦ (G j).carrier)
      (NativeCondensedModule.operator l D g.hom S.carrier S.str z n h)
      (fun j ↦ NativeCondensedModule.operator l D g.hom (G j).carrier (G j).str z n h)
      hproj v j
    unfold NativeCondensedModule.operator at hj
    exact hj
  apply polynomial_eq_of_pair_coordinates Q t F
    (CondensedFibreLinearCurrent.dualWeil l g F)
    (native_fibre_finite l D F.carrier hF z) N p (c.dual F hcons hF) hp
  intro v a
  have hd := hc.dual_frobenius F hcons hF v a
  unfold NativeCondensedModule.operator at hd
  exact hd

private theorem sum_dual_polynomial
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (F₀ : NativeL2.WeilModule D l X₀)
    (hF₀ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      F₀.carrier)
    (hE : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (sumDual D l X₀ F₀).carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀
      (sumDual D l X₀ F₀)
      hE x i hi).localPolynomial =
      let M := localFrobeniusModule D l X₀ F₀ hF₀ x i hi
      (M.prod M.dual).localPolynomial := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hcons := lisse_constructible D l X₀ F₀ hF₀
  have hops := CondensedFibreLinearCurrent.condensed_fibre_linear_operations D l hl X₀
  have hdual := hops.1 F₀ hcons hF₀
  have hdcons := lisse_constructible D l X₀
    (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) F₀) hdual
  obtain ⟨c, hc⟩ := hops.2.2 x i hi
  exact native_dual_polynomial D l (D.geometricFrobenius X₀)
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
    (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
    (NativeCondensedModule.localClosedPoint_return D X₀ x i hi)
    F₀ hF₀ hcons hdcons hE c hc

private theorem envelope_polynomial
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (F : NativeL2.WeilModule D l X₀) (b : (PadicAlgCl l)ˣ)
    (hF₀ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (normalizedTwist D l X₀ hl F b).carrier)
    (hE : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (realEnvelope D l X₀ hl F b).carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀ (realEnvelope D l X₀ hl F b) hE x i hi).localPolynomial =
      let M := localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b) hF₀ x i hi
      (M.prod M.dual).localPolynomial := by
  exact sum_dual_polynomial D l hl X₀ (normalizedTwist D l X₀ hl F b) hF₀ hE x i hi

/-- A nonzero lisse pure sheaf admits a weight-zero twist with a real pure envelope,
containing the twist as a Weil-equivariant summand and with twice-real-part traces.
Source: latest blueprint, sk-prop-wrp-real-envelope, entire F-clause and Complement
(blueprint: sk-prop-wrp-real-envelope).
Proof:
1. Closed-point detection gives a nonzero finite-dimensional fibre. Its invertible
geometric Frobenius has a nonzero eigenvalue alpha, at a point of positive degree d.
Choose a d-th root b of alpha inverse in the algebraically closed coefficient field.
Purity gives norm(iota alpha) = q^(dw/2). Taking positive d-th roots gives the stated
norm of b. This uses only an embedding iota, with no surjectivity assumption.
2. The constant twist adds -w to every weight, so F^0 is lisse and pure of weight zero.
Construct its envelope using the recorded internal dual and finite direct sum.
3. Dual local eigenvalues are inverse eigenvalues. Their images are conjugates since
all have norm one. The union is conjugation-stable, giving reality and purity zero;
finite-free trivializations give lissity. The first inclusion and projection are
Weil maps with composite the identity, hence exhibit the required direct summand.
4. The trace of every positive power is the sum of eigenvalue powers, with algebraic
multiplicity, without semisimplicity. The dual trace is its complex conjugate, and the
sum trace is z + conjugate z = 2*re(z). At a k_n-point over a degree-d closed point,
the rational-point operator is conjugate to the n/d-th closed-point power, with d|n.
Trace is invariant under conjugacy. Conversely a positive m-th power occurs over
k_(d*m), so the quantified trace clause is exactly the finite-extension clause.
Zero fibres give zero traces and impose no exception. -/
theorem exists_normalized_real_envelope
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [Nonempty X₀.left]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (hne : ¬ IsZero F)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (hpure : NativeL2.Pure D l X₀ F iota w) :
    ∃ b : (PadicAlgCl l)ˣ,
      ‖iota b‖ = (D.q : ℝ) ^ (-w / 2) ∧
      let F₀ := normalizedTwist D l X₀ hl F b
      let E := realEnvelope D l X₀ hl F b
      NativeL2.Pure D l X₀ F₀ iota 0 ∧
      NativeCondensedWeil.Real D l X₀ E iota ∧
      NativeL2.Pure D l X₀ E iota 0 ∧
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) E.carrier ∧
      (∃ (a : F₀ ⟶ E) (r : E ⟶ F₀), a ≫ r = 𝟙 F₀) ∧
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (m : ℕ), 1 ≤ m →
        iota (ULift.down (LinearMap.trace (ULift.{u + 1} (PadicAlgCl l))
          (NativeCondensedModule.fibre l D E.carrier
            (NativeCondensedModule.localClosedPoint D X₀ x i hi))
          ((NativeL2.closedOperator D l X₀ E x i hi).hom ^ m))) =
        ((2 * (iota (ULift.down (LinearMap.trace (ULift.{u + 1} (PadicAlgCl l))
          (NativeCondensedModule.fibre l D F₀.carrier
            (NativeCondensedModule.localClosedPoint D X₀ x i hi))
          ((NativeL2.closedOperator D l X₀ F₀ x i hi).hom ^ m)))).re : ℝ) : ℂ) := by
  classical
  let : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    isAlgClosed_ulift_padic l
  obtain ⟨b, hb⟩ := normalizing_scalar D l hl X₀ F iota w hne hF hpure
  have hzero := normalized_pure_zero D l hl X₀ F hF iota w hpure b hb
  obtain ⟨hreal, hE⟩ := realEnvelope_real_lisse D l hl X₀ F iota w hF hpure b hb
  have hF₀ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (normalizedTwist D l X₀ hl F b).carrier := by
    apply (isLocallyFree_iff _).mp
    change IsLocallyFree _ (F.carrier ⊗ (𝟙_ _))
    exact ((isLocallyFree_iff _).mpr hF).of_iso (ρ_ F.carrier).symm
  refine ⟨b, hb, hzero, hreal, ?_, hE, ?_, ?_⟩
  · intro x i hi α hα
    let M := localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b) hF₀ x i hi
    let N := localFrobeniusModule D l X₀ (realEnvelope D l X₀ hl F b) hE x i hi
    have hp := pure_local_module D l X₀ _ hF₀ iota 0 hzero x i hi
    have hpd : M.dual.IsPureOfWeight (iota.comp ULift.ringEquiv.toRingHom)
        (Nat.card (X₀.left.residueField x.val)) 0 := by simpa using hp.dual
    have hpoly := charpoly_eq_of_localPolynomial_eq N (M.prod M.dual)
      (envelope_polynomial D l hl X₀ F b hF₀ hE x i hi)
    have heig : N.frobeniusEnd.HasEigenvalue α := by
      rwa [local_end_eq]
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hpoly,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at heig
    exact (hp.prod hpd) α heig
  · exact sumIsoAlgebra_retract
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom) 2
        (fun j : Fin 2 ↦ if j.val = 0 then normalizedTwist D l X₀ hl F b else
          CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀)
            (normalizedTwist D l X₀ hl F b)) 0
  · intro x i hi m hm
    let M := localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b) hF₀ x i hi
    let N := localFrobeniusModule D l X₀ (realEnvelope D l X₀ hl F b) hE x i hi
    let ι := iota.comp ULift.ringEquiv.toRingHom
    have hp : M.IsPureOfWeight ι (Nat.card (X₀.left.residueField x.val)) 0 :=
      pure_local_module D l X₀ _ hF₀ iota 0 hzero x i hi
    have ht := FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq
      (M.prod M.dual) N ι ι
      (congrArg (Polynomial.map ι) (envelope_polynomial D l hl X₀ F b hF₀ hE x i hi)) m
    conv_rhs at ht =>
      rw [FrobeniusModule.trace_frobeniusEnd_prod_pow, map_add,
        hp.map_trace_frobeniusEnd_dual_pow, Complex.add_conj]
    change ι (LinearMap.trace _ _
      ((localFrobeniusModule D l X₀ (realEnvelope D l X₀ hl F b) hE x i hi).frobeniusEnd
        ^ m)) = ((2 * (ι (LinearMap.trace _ _
      ((localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b)
        hF₀ x i hi).frobeniusEnd ^ m))).re : ℝ) : ℂ) at ht
    rw [local_end_eq, local_end_eq] at ht
    change iota (ULift.down.{u + 1, 0} _) =
      ((2 * (iota (ULift.down.{u + 1, 0} _)).re : ℝ) : ℂ) at ht
    exact ht

attribute [local semireducible] NativeCondensedModule.operator
  NativeCondensedModule.pointSections

end WeilConjectures.NativeEnvelope
