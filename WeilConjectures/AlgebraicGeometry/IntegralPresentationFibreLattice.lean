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
import WeilConjectures.AlgebraicGeometry.IntegralPresentationFibreLatticeCore
import WeilConjectures.AlgebraicGeometry.IntegralPresentationFibreLatticeFinite

/-! # The normalized fibre lattice of an integral presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.LisseQlbar

namespace AlgebraicGeometry.ProEtale.RealIntegral

variable (l : ℕ) [Fact l.Prime]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
  (c : Correspondence l x G)

set_option maxHeartbeats 0 in
-- The normalized fibre and scalar transports have large module-object types.
/-- A scalar-extension presentation of an algebraic-closure sheaf identifies the
integral geometric fibre with a stable full lattice via its actual fibre map.

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-integral/
`p-real-integral.proof.md`, lattice, finite-image and scalar-extension paragraphs
(blueprint: lem-real-integral-presentation-fibre-lattice).

Proof in words: the scalar-extension lattice core
(`integralPresentation_fibre_lattice_core`, blueprint:
lem-real-integral-presentation-fibre-lattice-core) gives the lattice N with its basis,
lattice property, stability, the equivalence M = N along j, the tensor equivalence and
the equivariance of j. The finite-reduction stage
(`integralPresentation_fibre_lattice_finite`, blueprint:
lem-real-integral-presentation-fibre-lattice-finite), applied to this N with its basis
and stability, gives the finite reduction images for every n. -/
theorem integralPresentation_fibre_lattice
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
  ∃ N : Submodule A V,
      Nonempty (Module.Basis (Fin (Module.finrank (PadicAlgCl l) V)) A N) ∧
      Submodule.IsLattice (PadicAlgCl l) N ∧
      (∀ g : G, (c.algebraic.functor.obj F).ρ g '' (N : Set V) = (N : Set V)) ∧
      (∃ e : M ≃ₗ[A] N, ∀ z : M, (e z : V) = j z) ∧
      (∃ t : (PadicAlgCl l ⊗[A] N) ≃ₗ[PadicAlgCl l] V,
        ∀ (b : PadicAlgCl l) (z : N), t (b ⊗ₜ[A] z) = b • (z : V)) ∧
      (∀ (g : G) (z : M),
        j (((c.integral E).functor.obj L).ρ g z) =
          (c.algebraic.functor.obj F).ρ g (j z)) ∧
      ∀ n : ℕ,
        (Set.range fun g : G ↦ fun z : N ↦
          Submodule.Quotient.mk
            (p := (Padic.coefficientExtensionMaximalIdeal l E ^ n) • N)
            ((c.algebraic.functor.obj F).ρ g z)).Finite := by
  classical
  obtain ⟨N, hN, hLat, hStable, he, ht, hj⟩ :=
    integralPresentation_fibre_lattice_core l x G c F E L i _hi _he
  refine ⟨N, hN, hLat, hStable, he, ht, hj, ?_⟩
  exact integralPresentation_fibre_lattice_finite l x G c F E L i _hi _he N hN hStable

end AlgebraicGeometry.ProEtale.RealIntegral
