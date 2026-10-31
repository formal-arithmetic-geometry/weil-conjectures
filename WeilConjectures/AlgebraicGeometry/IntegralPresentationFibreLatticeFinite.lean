/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Module.Lattice

/-! Finite reduction images of a stable integral fibre lattice. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.LisseQlbar

namespace AlgebraicGeometry.ProEtale.RealIntegral

set_option linter.style.haveILetI false in
private theorem finite_stable_mk_range
    {A N G ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Finite ι]
    (I : Ideal A) (b : Module.Basis ι A N)
    [Finite (A ⧸ I)] (F : G → N →ₗ[A] N) :
    Set.Finite (Set.range (fun g : G => fun z : N =>
      Submodule.Quotient.mk (p := I • (⊤ : Submodule A N)) (F g z))) := by
  classical
  letI := Module.Finite.of_basis b
  letI : Finite (N ⧸ I • (⊤ : Submodule A N)) :=
    Submodule.finite_quotient_smul I Module.Finite.fg_top
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (N ⧸ I • (⊤ : Submodule A N)) :=
    Fintype.ofFinite _
  let eval : (N → (N ⧸ I • (⊤ : Submodule A N))) → (ι → (N ⧸ I • (⊤ : Submodule A N))) :=
    fun f i => f (b i)
  have heval : Set.Finite (Set.range (fun g : G => eval (fun z : N =>
      Submodule.Quotient.mk (p := I • (⊤ : Submodule A N)) (F g z)))) := by
    exact Set.toFinite _
  have himage : (eval '' Set.range (fun g : G => fun z : N =>
      Submodule.Quotient.mk (p := I • (⊤ : Submodule A N)) (F g z))).Finite := by
    rw [← Set.range_comp]
    exact heval
  have hinj : Set.InjOn eval (Set.range (fun g : G => fun z : N =>
      Submodule.Quotient.mk (p := I • (⊤ : Submodule A N)) (F g z))) := by
    intro f₁ hf₁ f₂ hf₂ h
    rcases hf₁ with ⟨g₁, rfl⟩
    rcases hf₂ with ⟨g₂, rfl⟩
    have hlin :
        (I • (⊤ : Submodule A N)).mkQ.comp (F g₁) =
          (I • (⊤ : Submodule A N)).mkQ.comp (F g₂) := by
      apply b.ext
      intro j
      simpa [eval] using congrFun h j
    funext z
    exact congrArg (fun f => f z) hlin
  exact himage.of_finite_image hinj


private theorem finite_stable_range
    {A N Q G ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [AddCommGroup Q] [Module A Q] [Finite ι]
    (I : Ideal A) (b : Module.Basis ι A N) [Finite (A ⧸ I)]
    (q : N →ₗ[A] Q) (hq : I • (⊤ : Submodule A N) ≤ LinearMap.ker q)
    (F : G → N →ₗ[A] N) :
    Set.Finite (Set.range (fun g : G => fun z : N => q (F g z))) := by
  classical
  let qbar : (N ⧸ I • (⊤ : Submodule A N)) →ₗ[A] Q :=
    (I • (⊤ : Submodule A N)).liftQ q hq
  have hmk := finite_stable_mk_range I b F
  have himage : ((fun f z => qbar (f z)) '' Set.range (fun g : G => fun z : N =>
      Submodule.Quotient.mk (p := I • (⊤ : Submodule A N)) (F g z))).Finite :=
    hmk.image (fun f z => qbar (f z))
  rw [← Set.range_comp] at himage
  exact himage


variable (l : ℕ) [Fact l.Prime]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
  (c : Correspondence l x G)

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
/-- A stable finite-free integral lattice has finite images in every normalized reduction.
Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-integral, the finite-image
paragraph of `p-real-integral.proof.md`.
(blueprint: lem-real-integral-presentation-fibre-lattice-finite).

Proof in words:
For positive n, the DVR with finite residue field has finite A/m^n. A basis gives
N/m^n N = (A/m^n)^r, so its automorphism group is finite. Stability and A-linearity
make the action factor through that group. Although V/m^n N need not be finite, the
map in the conclusion factors through this finite group followed by the inclusion
of N/m^n N into V/m^n N, proving finiteness of its range. For n = 0 every value is
zero, so its image is a singleton. These arguments include the zero-rank case. -/
theorem integralPresentation_fibre_lattice_finite
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)))
    (i : L.obj ⟶ (Mod.comap (coefficientMap (integerInclusion l E ≫
      Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj F.obj)
    (_hi : Mono i)
    (_he : IsIso (((Mod.extendRestrictAdjunction (coefficientMap
      (integerInclusion l E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).homEquiv
      L.obj F.obj).symm i)) :
  let j := (c.integral E).comparison.hom.app L ≫
    fibreMap (integerRing l E) (Profinite.padicAlgClRingObj l) x L.obj F.obj i.hom ≫
    c.algebraic.comparison.inv.app F
  let A := Padic.coefficientExtensionIntegers l E
  let V := (c.algebraic.functor.obj F).V
  let M := ((c.integral E).functor.obj L).V
  let a := (algebraMap E (PadicAlgCl l)).comp A.subtype
  letI : Algebra A (PadicAlgCl l) := a.toAlgebra
  letI : Module A V := Module.compHom V a
  ∀ N : Submodule A V,
    Nonempty (Module.Basis (Fin (Module.finrank (PadicAlgCl l) V)) A N) →
      (∀ g : G, (c.algebraic.functor.obj F).ρ g '' (N : Set V) = (N : Set V)) →
      ∀ n : ℕ,
        (Set.range fun g : G ↦ fun z : N ↦
          Submodule.Quotient.mk
            (p := (Padic.coefficientExtensionMaximalIdeal l E ^ n) • N)
            ((c.algebraic.functor.obj F).ρ g z)).Finite := by
  dsimp
  -- finite coordinate reduction
  intros N hN hstable n
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let V := (c.algebraic.functor.obj F).V
  let J := Padic.coefficientExtensionMaximalIdeal l E ^ n
  letI : Algebra A (PadicAlgCl l) :=
    ((algebraMap E (PadicAlgCl l)).comp (Padic.coefficientExtensionIntegers l E).subtype).toAlgebra
  letI : Module A V := Module.compHom V (algebraMap A (PadicAlgCl l))
  obtain ⟨b⟩ := hN
  let ρN : G → N →ₗ[A] N := fun g =>
    (((c.algebraic.functor.obj F).ρ g).restrictScalars A).restrict (p := N) (q := N) (fun z hz =>
      (hstable g).subset ⟨z, hz, rfl⟩)
  let q : N →ₗ[A] (V ⧸ J • N) :=
    (J • N).mkQ.comp N.subtype
  have hq : J • (⊤ : Submodule A N) ≤ LinearMap.ker q := by
    intro z hz
    exact (Submodule.Quotient.mk_eq_zero _).2 (by
      change (z : V) ∈ J • N
      exact Submodule.smul_induction_on hz (fun r hr m hm =>
        Submodule.smul_mem_smul hr m.property) (fun x y hx hy => by simpa using add_mem hx hy))
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hres : Finite (A ⧸ Padic.coefficientExtensionMaximalIdeal l E) :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  letI : Finite (A ⧸ Padic.coefficientExtensionMaximalIdeal l E) := hres
  have hfinA : Finite (A ⧸ J) := by
    exact Ideal.finite_quotient_pow (hgen ▸ Submodule.fg_span_singleton _) n
  letI := hfinA
  have hh := finite_stable_range J b q hq ρN
  change Set.Finite (Set.range fun g : G => fun z : N =>
    Submodule.Quotient.mk (p := J • N) ((c.algebraic.functor.obj F).ρ g z))
  convert hh using 1
  ext g
  rfl

end AlgebraicGeometry.ProEtale.RealIntegral
