/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.TorIdealHomologyFormula
import WeilConjectures.RingTheory.TorIdealHomologyExactness

/-! # The ideal connecting map for first Tor
For an ideal `I` of `R` and an `R`-module `M`, the connecting map gives an isomorphism of
`Tor₁(M, R/I)` onto the kernel of the multiplication map `I ⊗ M → M`, computed explicitly on
cycles of a free resolution.

## Implementation details

Tensoring `0 → I → R → R/I → 0` with a free resolution of `M` and applying the snake lemma in
degrees one and zero sends a cycle lifted to `y` with `d y = ∑ aⱼ • pⱼ` to `∑ aⱼ ⊗ π(pⱼ)`.

## References

* [Stacks, Tag 00M5]
* [Stacks, Tag 00M6]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- For an ideal `I` and a free resolution `P` of `M`, there is an injective linear map
`δR : Tor₁(M, R/I) → I ⊗ M` with range the kernel of the multiplication map `μR : I ⊗ M → M`,
sending the class of a cycle lifted to `y` with `d y = ∑ j, a j • p j` to
`∑ j, a j ⊗ π (p j)`. -/
theorem exists_tor_ideal_connecting_formula
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (μR : (I ⊗[R] M) →ₗ[R] M)
    (hμR : ∀ (a : I) (x : M), μR (a ⊗ₜ[R] x) = (a : R) • x) :
    ∃ δR : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I)))
      →ₗ[R] (I ⊗[R] M),
      Function.Injective δR ∧ LinearMap.range δR = LinearMap.ker μR ∧
      (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δR ((P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I)))
          1).inv (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
          I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z)) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) := by
  obtain ⟨δH, hδH⟩ := exists_tor_ideal_homology_formula I M P hP
  obtain ⟨hiH, hrH⟩ := tor_ideal_homology_exactness I M P hP μR hμR δH hδH
  let e := P.isoLeftDerivedObj
    ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))) 1
  let δR := δH.comp e.hom.hom
  refine ⟨δR, ?_, ?_, ?_⟩
  · exact hiH.comp ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)
  · change LinearMap.range (δH.comp e.hom.hom) = LinearMap.ker μR
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr
      ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance), Submodule.map_top, hrH]
  · intro z y k a p hz hy
    change δH (e.hom (e.inv (_))) = _
    simpa only [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply] using
      hδH z y k a p hz hy

end ModuleCat
