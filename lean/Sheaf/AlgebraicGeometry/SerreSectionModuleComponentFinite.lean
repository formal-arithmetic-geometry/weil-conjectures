/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.AlgebraicGeometry.TwistedSectionFiniteCoordinates
import Mathlib.RingTheory.Finiteness.Basic

/-! # SerreSectionModuleComponentFinite

Intermediate step for finite generation of graded sections. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma transport_section_equiv
    {X : Scheme.{u}} {M : Type u} [AddCommGroup M]
    (N : ℤ → AddSubgroup M) (F : ℤ → X.Modules)
    (φ : ∀ z, 0 ≤ z → N z ≃+ Γ(F z, ⊤))
    (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a = b)
    (x : M) (hx : x ∈ N a) (hy : x ∈ N b) :
    Scheme.Modules.Hom.app (eqToHom (congrArg F hab)) ⊤ (φ a ha ⟨x, hx⟩) =
      φ b hb ⟨x, hy⟩ := by
  subst b
  simp

/-- Each individual nonnegative section degree generates a finite polynomial submodule.
This is a statement for one degree at a time, and supplies no uniform bound on degrees.

Source: Stacks Project, Lemma 01YS(3) and the last paragraph of the proof of (5);
https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-module-component-finite).
Proof: O(n) is invertible, so G ⊗ O(n) is coherent by local triviality. Transport to the
standard projective line via the Proj chart isomorphism and the twist identification.
Coherent global sections are finite-dimensional over k by finiteDimensional_H in degree
zero and the identification of H⁰ with Γ. Degree-zero multiplication in hφ, applied to
constant polynomials C(c), makes φ(n) k-linear for the restricted scalar action on the
n-th subgroup: twistMul by C(c) is multiplication by c on the local fractions. Pull back
a finite k-basis of sections. Every element of the subgroup is a k-linear combination
of this finite set, hence belongs to its S-span. Conversely the set is in the subgroup,
so its S-span equals the S-span of the entire subgroup. This gives FG. In the zero
section space the empty basis suffices; n=0 uses the same argument. -/
theorem serreSectionModuleComponentFinite
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e → y ∈ 𝓜 z → a • y ∈ 𝓜 (e + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
      (𝓜 z ≃+ Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
      (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
      (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
      φ (z + e) hze ⟨a • (y : M), hay⟩ =
        Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y)) :
    ∀ n : ℕ, (Submodule.span (MvPolynomial (Fin 2) k) (𝓜 (n : ℤ) : Set M)).FG := by
  intro n
  let : Module k M := Module.compHom M (algebraMap k (MvPolynomial (Fin 2) k))
  let : IsScalarTower k (MvPolynomial (Fin 2) k) M :=
    IsScalarTower.of_compHom k (MvPolynomial (Fin 2) k) M
  have hc (c : k) (y : M) : c • y = (MvPolynomial.C c : MvPolynomial (Fin 2) k) • y := by
    change algebraMap k (MvPolynomial (Fin 2) k) c • y =
      (MvPolynomial.C c : MvPolynomial (Fin 2) k) • y
    rw [MvPolynomial.algebraMap_eq]
  let N : Submodule k M :=
    { toAddSubmonoid := (𝓜 (n : ℤ)).toAddSubmonoid
      smul_mem' := by
        intro c y hy
        rw [hc]
        simpa using hsmul 0 n (MvPolynomial.C c) y (MvPolynomial.isHomogeneous_C _ c) hy }
  obtain ⟨r, e, he⟩ := serreTwistedSectionFiniteCoordinates k G hG n
  let f : N →ₗ[k] (Fin r → k) :=
    { toFun := fun y ↦ e (φ n (Int.natCast_nonneg n) ⟨y, y.property⟩)
      map_add' := by
        intro x y
        change e (φ n _ ((⟨x, x.property⟩ : 𝓜 (n : ℤ)) + ⟨y, y.property⟩)) = _
        rw [map_add, map_add]
      map_smul' := by
        intro c y
        have ha : MvPolynomial.C c ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 0 :=
          MvPolynomial.isHomogeneous_C (Fin 2) c
        have hy : (MvPolynomial.C c : MvPolynomial (Fin 2) k) • (y : M) ∈
            𝓜 ((n : ℤ) + (0 : ℕ)) := by
          simpa using hsmul 0 n (MvPolynomial.C c) y ha y.property
        have h := hφ n (Int.natCast_nonneg n) 0 (by simp) (MvPolynomial.C c) ha
          ⟨y, y.property⟩ hy
        have h' := he c ha (φ n (Int.natCast_nonneg n) ⟨y, y.property⟩) (by simp)
        change e (φ n _ ⟨c • (y : M), _⟩) = c • e (φ n _ ⟨y, y.property⟩)
        have heq : (⟨c • (y : M), (c • y).property⟩ : 𝓜 (n : ℤ)) =
            ⟨(MvPolynomial.C c : MvPolynomial (Fin 2) k) • (y : M), by
              simpa using hy⟩ := Subtype.ext (hc c y)
        rw [heq]
        have ht := transport_section_equiv 𝓜
          (fun z ↦ G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z)
          φ ((n : ℤ) + (0 : ℕ)) n (by simp) (Int.natCast_nonneg n) (by simp)
          ((MvPolynomial.C c : MvPolynomial (Fin 2) k) • (y : M)) hy (by simpa using hy)
        rw [← ht, h]
        simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h' }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val ((φ n (Int.natCast_nonneg n)).injective (e.injective h))
  have : Module.Finite k N := Module.Finite.of_injective f hf
  have hN : N.FG := Module.Finite.iff_fg.mp inferInstance
  exact hN.span

end AlgebraicGeometry
