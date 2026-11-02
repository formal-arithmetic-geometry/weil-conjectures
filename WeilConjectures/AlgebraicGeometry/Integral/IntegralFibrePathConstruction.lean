/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import Mathlib.CategoryTheory.Conj
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Quotient
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorLinearTransport

/-! # Integral fibre paths from finite level evaluation

Source: Weil II (1.1.1) b), p.146.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option genSizeOfSpec false in
set_option genInjectivity false in
variable {Y : Scheme.{u}}

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber pathUnderlyingStalk

set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem finite_of_annihilated {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [Finite (R ⧸ I)] (M : Type (u + 1)) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (h : I • (⊤ : Submodule R M) = ⊥) : Finite M := by
  let : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let : Finite (M ⧸ (I • (⊤ : Submodule R M))) := Module.finite_of_finite (R ⧸ I)
  exact Finite.of_equiv _ ((I • (⊤ : Submodule R M)).quotEquivOfEqBot h).toEquiv

private theorem finite_integral_level (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (F : LisseIntegralSheaf l E Y) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
        (F.obj.obj (op n))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let p := (pointSmallEtale y).ulift.{u + 1}
  let G := F.obj.obj (op n)
  let M := p.sheafFiber.obj G
  let : Finite (R ⧸ I) := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have hfg := (F.property.1 n).toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω y
  let : Module.Finite R (((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj G) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp hfg
  let : Module.Finite R M := Module.Finite.equiv
    (((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} R)).app G).toLinearEquiv.symm
  apply finite_of_annihilated I M
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro r hr x _
  obtain ⟨U, ξ, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := G.obj) x
  have hkill : r • s = 0 := by
    have hmem : r • s ∈ I • (⊤ : Submodule R (G.obj.obj (op U))) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    have hi : I • (⊤ : Submodule R (G.obj.obj (op U))) = ⊥ := F.property.2.1 n U
    rw [hi, Submodule.mem_bot] at hmem
    exact hmem
  change r • p.toPresheafFiber U ξ G.obj s = 0
  rw [← map_smul, hkill, map_zero]

end AlgebraicGeometry.Scheme
