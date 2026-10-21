/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicNormalizedFibreData
import Sheaf.Paper.NormalizedTowerFree
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Finite free normalized lattice fibres

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded normalized stalk tower has finite free integral fibre.
Source: Bhatt--Scholze, Proposition 6.8.4(1).
(blueprint: lem-per-normalized-lattice-finite-free).

Proof: apply the finite-free normalized-tower theorem to the actual etale stalk diagram.
Its transition surjectivity and kernel equality are precisely the lisse-system condition;
its free quotient modules are the recorded finiteFree field. -/
theorem lattice_fiber_finite_free {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :
    Module.Finite (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ x) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ x) := by
  exact Padic.normalized_tower_limit_finite_free l E _ (N.finiteFree κ x) (N.lisse.2.2 κ x)

/-- Rationalizing a normalized lattice fibre gives a finite-dimensional vector space.
Source: Bhatt--Scholze, Proposition 6.8.4(4).
(blueprint: lem-per-normalized-lattice-finite-free).
Proof: the integral limit is finite, and tensor extension preserves finite generation. -/
theorem lattice_rationalFiber_finite {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :
    FiniteDimensional E (N.rationalFiber l E κ x) := by
  let : Module.Finite (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ x) :=
    (lattice_fiber_finite_free l E N κ x).1
  let : Algebra (Padic.coefficientExtensionIntegers l E) E :=
    (Padic.coefficientExtensionIntegers l E).subtype.toAlgebra
  change Module.Finite E (E ⊗[Padic.coefficientExtensionIntegers l E] N.fiber l E κ x)
  infer_instance

/-- A normalized local lattice comparison makes the intrinsic fibre finite dimensional.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6).
(blueprint: lem-per-normalized-lattice-finite-free).
Proof: choose a lattice chart through the point and use its normalization isomorphism;
transport finite dimensionality from the rationalized finite integral limit. -/
theorem intrinsic_fiber_finite (X : Base.{u} l) (a : At l E X)
    (h : LocalLattices l E X a) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme) (F : Heart l E X) :
    FiniteDimensional E ((omega l E X a κ x).obj F) := by
  obtain ⟨C, t, N, ht, hF, ⟨e⟩⟩ := h.local_chart F κ x
  rw [← ht]
  let : FiniteDimensional E (N.rationalFiber l E κ t) :=
    lattice_rationalFiber_finite l E N κ t
  exact Module.Finite.equiv (h.normalization C F hF N e κ t).toLinearEquiv.symm

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
