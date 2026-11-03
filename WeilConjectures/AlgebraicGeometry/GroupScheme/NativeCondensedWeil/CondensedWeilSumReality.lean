/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement
public import Mathlib.LinearAlgebra.Trace
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TracePow
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Reality of two condensed Weil summands with conjugate power traces

Source: latest blueprint, lem-fd-realified-kernel-real.proof.md, Step 2
(blueprint: lem-fd-condensed-sum-conjugate-traces).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w w'
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeCondensedWeil
open NativeCondensedModule CondensedFibreLinearCurrent

private def twoProductLinearEquiv {C : Type v} [Category.{w} C]
    {K : Type*} [Field K] (G : C ⥤ ModuleCat.{w'} K) (F : Fin 2 → C)
    [HasProduct F] [IsIso (piComparison G F)] :
    G.obj (∏ᶜ F) ≃ₗ[K] G.obj (F 0) × G.obj (F 1) :=
  ((asIso (piComparison G F) ≪≫ ModuleCat.piIsoPi (fun a ↦ G.obj (F a))).toLinearEquiv).trans
    (LinearEquiv.piFinTwo K (fun a ↦ G.obj (F a)))

private theorem twoProductLinearEquiv_conj {C : Type v} [Category.{w} C]
    {K : Type*} [Field K] (G : C ⥤ ModuleCat.{w'} K) (F : Fin 2 → C)
    [HasProduct F] [IsIso (piComparison G F)]
    (B : End (G.obj (∏ᶜ F))) (A : (a : Fin 2) → End (G.obj (F a)))
    (h : ∀ a, B ≫ G.map (Pi.π F a) = G.map (Pi.π F a) ≫ A a) :
    (twoProductLinearEquiv G F).conj B.hom = (A 0).hom.prodMap (A 1).hom := by
  let e₀ := (asIso (piComparison G F) ≪≫
    ModuleCat.piIsoPi (fun a ↦ G.obj (F a))).toLinearEquiv
  let e := twoProductLinearEquiv G F
  have ecoord (a : Fin 2) (v : G.obj (∏ᶜ F)) :
      e₀ v a = G.map (Pi.π F a) v := by
    have hh :
        (asIso (piComparison G F) ≪≫
          ModuleCat.piIsoPi (fun a ↦ G.obj (F a))).hom ≫
            ModuleCat.ofHom (LinearMap.proj a) = G.map (Pi.π F a) := by
      simp only [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
        asIso_hom]
      exact piComparison_comp_π G F a
    exact congrArg (fun f ↦ f v) hh
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := e.surjective v
  apply Prod.ext
  · change (e (B.hom (e.symm (e v)))).1 = (A 0).hom (e v).1
    rw [e.symm_apply_apply]
    change e₀ (B.hom v) 0 = (A 0).hom (e₀ v 0)
    rw [ecoord, ecoord]
    exact congrArg (fun f ↦ f v) (h 0)
  · change (e (B.hom (e.symm (e v)))).2 = (A 1).hom (e v).2
    rw [e.symm_apply_apply]
    change e₀ (B.hom v) 1 = (A 1).hom (e₀ v 1)
    rw [ecoord, ecoord]
    exact congrArg (fun f ↦ f v) (h 1)

private theorem real_coeff_of_trace_product
    {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K Z]
    (φ : K →+* ℂ) (e : V ≃ₗ[K] W × Z)
    (B : Module.End K V) (A : Module.End K W) (C : Module.End K Z)
    (hc : e.conj B = A.prodMap C)
    (ht : ∀ m, φ (LinearMap.trace K Z (C ^ m)) =
      starRingEnd ℂ (φ (LinearMap.trace K W (A ^ m)))) (j : ℕ) :
    (φ (B.charpolyRev.coeff j)).im = 0 := by
  have hp (m : ℕ) : (A.prodMap C) ^ m = (A ^ m).prodMap (C ^ m) := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, LinearMap.prodMap_mul, pow_succ, pow_succ]
  have htrace (m : ℕ) : LinearMap.trace K V (B ^ m) =
      LinearMap.trace K W (A ^ m) + LinearMap.trace K Z (C ^ m) := by
    rw [← LinearMap.trace_conj' (B ^ m) e, ← LinearEquiv.conj_pow, hc, hp]
    exact LinearMap.trace_prodMap' _ _
  have hr : ∀ m, LinearMap.trace K V (B ^ m) ∈ φ.realSubfield := by
    intro m
    rw [RingHom.mem_realSubfield, htrace, map_add, ht, map_add,
      Complex.conj_conj, add_comm]
  have : CharZero K := φ.charZero
  have hr' := (LinearMap.forall_coeff_charpolyRev_mem_iff B φ.realSubfield).mpr hr j
  exact Complex.conj_eq_iff_im.mp (RingHom.mem_realSubfield.mp hr')

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- Normalizing chosen products through the actual section functor needs a larger budget.
private theorem real_coeff_native_sum
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T)
    (F : Fin 2 → Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom))
    (hF : ∀ a, IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      T (F a).carrier)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower g.hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z)
    (c : Comparisons ell D g z) (hc : WeilCompatibility ell D g z r h c)
    (hfd : ∀ a, FiniteDimensional (ULift.{u + 1} (PadicAlgCl ell))
      (fibre ell D (F a).carrier z))
    (φ : ULift.{u + 1} (PadicAlgCl ell) →+* ℂ)
    (ht : ∀ m, φ (LinearMap.trace (ULift.{u + 1} (PadicAlgCl ell))
        (fibre ell D (F 1).carrier z)
        ((operator ell D g.hom (F 1).carrier (F 1).str z r h).hom ^ m)) =
      starRingEnd ℂ (φ (LinearMap.trace (ULift.{u + 1} (PadicAlgCl ell))
        (fibre ell D (F 0).carrier z)
        ((operator ell D g.hom (F 0).carrier (F 0).str z r h).hom ^ m))))
    (n : ℕ) (b : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl ell))
      (fibre ell D (sumWeil ell g 2 F).carrier z)) (j : ℕ) :
    (φ (((LinearMap.toMatrix b b
      (operator ell D g.hom (sumWeil ell g 2 F).carrier
        (sumWeil ell g 2 F).str z r h).hom).charpoly.reverse).coeff j)).im = 0 := by
  let K := ULift.{u + 1} (PadicAlgCl ell)
  let G := CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) z ⋙
    NativeCondensedModule.pointSections ell D.k
  let V : Fin 2 → ModuleCat K := fun a ↦ G.obj (F a).carrier
  let A : (a : Fin 2) → Module.End K (V a) := fun a ↦
    (operator ell D g.hom (F a).carrier (F a).str z r h).hom
  let S := sumWeil ell g 2 F
  let B := (operator ell D g.hom S.carrier S.str z r h).hom
  obtain ⟨hs, he⟩ := hc.sum_frobenius 2 F hF
  let := hs
  let e := twoProductLinearEquiv G (fun a ↦ (F a).carrier)
  have hconj : e.conj B = (A 0).prodMap (A 1) := by
    apply twoProductLinearEquiv_conj G (fun a ↦ (F a).carrier)
      (operator ell D g.hom S.carrier S.str z r h)
      (fun a ↦ operator ell D g.hom (F a).carrier (F a).str z r h)
    intro a
    simpa only [S, G, sumWeil, Endofunctor.IsoAlgebra.mk_carrier,
      Endofunctor.IsoAlgebra.mk_str, NativeCondensedModule.fibre,
      Functor.comp_obj] using he a
  let (a : Fin 2) : FiniteDimensional K (V a) := hfd a
  let : FiniteDimensional K (G.obj (∏ᶜ fun a ↦ (F a).carrier)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let : FiniteDimensional K (fibre ell D S.carrier z) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hr := real_coeff_of_trace_product φ e B (A 0) (A 1) hconj ht j
  change (φ (((LinearMap.toMatrix b b B).charpoly.reverse).coeff j)).im = 0
  simpa only [LinearMap.charpolyRev, LinearMap.charpoly_toMatrix] using hr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Specializing the scalar and closed-point comparisons needs a larger normalization budget.
/-- A finite sum of two actual condensed Weil modules is real if its summands have
conjugate traces at every power of every local Frobenius. The comparison is the
canonical product comparison on actual scalar fibres.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-sum-conjugate-traces).
Proof: The fibre comparison identifies the sum operator with the product of the
summand operators. Hence every power trace is the sum of two conjugate numbers,
which is real. Newton identities imply reality of the reverse characteristic
polynomial. The argument works also for zero-dimensional fibres. -/
theorem real_sum_two_of_conjugate_traces
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : Fin 2 → NativeL2.WeilModule D ell X₀)
    (hF : ∀ a, IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber X₀).left (F a).carrier)
    (hfd : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (a : Fin 2), FiniteDimensional (ULift.{u + 1} (PadicAlgCl ell))
        (fibre ell D (F a).carrier (localClosedPoint D X₀ x i hi)))
    (iota : PadicAlgCl ell →+* ℂ)
    (ht : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (m : ℕ),
      iota (LinearMap.trace (ULift.{u + 1} (PadicAlgCl ell))
        (fibre ell D (F 1).carrier (localClosedPoint D X₀ x i hi))
        ((NativeL2.closedOperator D ell X₀ (F 1) x i hi).hom ^ m)).down =
      starRingEnd ℂ (iota (LinearMap.trace (ULift.{u + 1} (PadicAlgCl ell))
        (fibre ell D (F 0).carrier (localClosedPoint D X₀ x i hi))
        ((NativeL2.closedOperator D ell X₀ (F 0) x i hi).hom ^ m)).down)) :
    Real D ell X₀ (sumWeil ell (D.geometricFrobenius X₀) 2 F) iota := by
  intro x i hi n b j
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨c, hc⟩ := (condensed_fibre_linear_operations D ell hell X₀).2.2 x i hi
  let φ : ULift.{u + 1} (PadicAlgCl ell) →+* ℂ :=
    iota.comp ULift.ringEquiv.toRingHom
  have hφ (v : ULift.{u + 1} (PadicAlgCl ell)) : φ v = iota v.down := rfl
  have hr := real_coeff_native_sum D ell (D.geometricFrobenius X₀) F hF
    (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi) c hc (hfd x i hi) φ
    (by simpa only [hφ, NativeL2.closedOperator] using ht x i hi) n b j
  simpa only [localFactorInBasis, hφ] using hr

end WeilConjectures.NativeCondensedWeil
