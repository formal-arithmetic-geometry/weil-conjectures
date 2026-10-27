/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.EquivariantAdicFibreData

/-! # Projection-normalized algebraic adic fibre data

Source: Bhatt--Scholze Proposition 6.8.4(1), equivariant expansion, steps 1--5 and 10--12
(blueprint: def-sfb-equivariant-adic-fibre-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.EquivariantAdicFibre
open ContinuousModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {l E}

/-- All algebraic and topological conclusions, with projection-normalized bases.
Source: BS Proposition 6.8.4(1), expansion steps 1--5
(blueprint: def-sfb-equivariant-adic-fibre-coordinates). -/
structure Coordinates {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) where
  finite : Module.Finite (Integers l E) (Fibre D)
  free : Module.Free (Integers l E) (Fibre D)
  basis : ∀ n : ℕ, Level D n ≃ₗ[Integers l E]
    (Fin D.rank → Padic.coefficientExtensionRing l E (n + 1))
  compatible : ∀ (n : ℕ) (v : Level D (n + 1)) (i : Fin D.rank),
    basis n (D.tower.map (homOfLE (Nat.le_succ n)).op v) i =
      Padic.coefficientExtensionTransition l E (n + 1) (basis (n + 1) v i)
  coordinates : Fibre D ≃ₗ[Integers l E] (Fin D.rank → Integers l E)
  coordinates_projection : ∀ (n : ℕ) (q : Fibre D) (i : Fin D.rank),
    basis n (projection D n q) i =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (coordinates q i)
  coordinates_homeomorph : IsHomeomorph coordinates
  adic : (nhds (0 : Fibre D)).HasBasis (fun n : ℕ ↦ 0 < n)
    (fun n ↦ ((Padic.coefficientExtensionIdeal l E n •
      (⊤ : Submodule (Integers l E) (Fibre D)) : Submodule (Integers l E) (Fibre D)) :
        Set (Fibre D)))
  projection_surjective : ∀ n, Function.Surjective (projection D n)
  projection_kernel : ∀ n, LinearMap.ker (projection D n) =
    Padic.coefficientExtensionIdeal l E (n + 1) • (⊤ : Submodule (Integers l E) (Fibre D))

/-- A pair of continuous linear actions related by the actual tensor formula.
This generic presentation keeps the scalar-module structures in their original form.
Source: BS Proposition 6.8.4(1), step 5
(blueprint: def-sfb-equivariant-adic-fibre-coordinates). -/
structure TensorActions (A K V H : Type u) [CommRing A] [CommRing K] [Algebra A K]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [TopologicalSpace (K ⊗[A] V)] [Group H] [TopologicalSpace H] where
  action : H →* (V ≃ₗ[A] V)
  continuous : Continuous (fun x : H × V ↦ action x.1 x.2)
  rho : H →* ((K ⊗[A] V) ≃ₗ[K] (K ⊗[A] V))
  rho_tensor : ∀ (g : H) (e : K) (q : V), rho g (e ⊗ₜ[A] q) = e ⊗ₜ[A] action g q
  rho_continuous : Continuous (fun x : H × (K ⊗[A] V) ↦ rho x.1 x.2)

/-- The coordinate-normalized continuous actions on the integral and rational fibres.
Source: BS Proposition 6.8.4(1), steps 4--5
(blueprint: def-sfb-equivariant-adic-fibre-coordinates). -/
structure Algebraic {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) extends Coordinates D,
      TensorActions (Integers l E) E (Fibre D) G where
  action_projection : ∀ (n : ℕ) (g : G) (q : Fibre D),
    projection D n (action g q) = D.action n g (projection D n q)

/-- Continuous equivariant maps on the actual integral and rational fibres.
The maps are fixed on every finite projection and every pure tensor.
Source: BS Proposition 6.8.4(1), steps 10--11
(blueprint: def-sfb-equivariant-adic-fibre-coordinates). -/
structure FibreNaturality {B X X' : Scheme.{u}} {u : X ⟶ B} {u' : X' ⟶ B}
    [WeaklyEtale u] [WeaklyEtale u']
    {G G' : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    [Group G'] [IsTopologicalGroup G']
    {a : ProfiniteCoefficientAction X G} {a' : ProfiniteCoefficientAction X' G'}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {hu' : a'.act ≫ u' = coefficientParameterProjection X' G' ≫ u'}
    {D : FiniteData l E G} {D' : FiniteData l E G'}
    {P : Data B X u G a hu D} {P' : Data B X' u' G' a' hu' D'}
    {r : X' ⟶ X} [WeaklyEtale r] {hr : r ≫ u = u'} {γ : G' →ₜ* G}
    (F : Morphism P P' r hr γ) (R : Algebraic D) (R' : Algebraic D') where
  integralMap : Fibre D →ₗ[Integers l E] Fibre D'
  integralMap_projection : ∀ (n : ℕ) (q : Fibre D),
    projection D' n (integralMap q) = F.finiteMap n (projection D n q)
  integralMap_continuous : Continuous integralMap
  integralMap_equivariant : ∀ (g : G') (q : Fibre D),
    integralMap (R.action (γ g) q) = R'.action g (integralMap q)
  rationalMap : Rational D →ₗ[E] Rational D'
  rationalMap_tensor : ∀ (e : E) (q : Fibre D),
    rationalMap (e ⊗ₜ[Integers l E] q) = e ⊗ₜ[Integers l E] integralMap q
  rationalMap_continuous : Continuous rationalMap
  rationalMap_equivariant : ∀ (g : G') (m : Rational D),
    rationalMap (R.rho (γ g) m) = R'.rho g (rationalMap m)
end AlgebraicGeometry.ProEtale.EquivariantAdicFibre
