/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Group

/-! # Rigidity of prime-to-characteristic level on polarized abelian varieties

Source: Milne, Abelian Varieties, I Proposition 14.4(b), p.62
(blueprint: lem-sfb-polarized-abelian-odd-level-rigidity).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The translation-difference point map associated to a line-bundle class:
`x ↦ [t_x^* L tensor L⁻¹]`, read in the ambient Picard group. For an ample L on an
abelian variety this is the point map of its polarization, with image in Pic⁰.
Translation is the existing group-scheme left translation `GrpObj.mulLeft`.

Source: Milne, Abelian Varieties, I Sections 8 and 11, pp.36 and 53
(blueprint: lem-sfb-polarized-abelian-odd-level-rigidity). -/
noncomputable def abelianPolarizationPointMap {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] (L : A.left.Pic)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left.Pic :=
  Scheme.Pic.map (GrpObj.mulLeft A x).left L / L

/-- A polarization-preserving group automorphism fixing all points killed by an invertible
integer n ≥ 3 is the identity. We write the polarization using any ample representative L.
Its preservation is λ_L(x) = a^*λ_L(a(x)) in Pic(A); pullback on Pic⁰ is the dual a^∨.
Equality in Pic(A) is equality in its subgroup Pic⁰, so this is a^∨ λ_L a = λ_L.

Source: Milne, Abelian Varieties, I Proposition 14.4(b), p.62
(blueprint: lem-sfb-polarized-abelian-odd-level-rigidity).

Proof:
1. By lem-sfb-polarized-abelian-automorphisms-finite, a has finite order r ≥ 1.
2. By lem-sfb-abelian-hom-finite-free, R = End_k(A) has a finite integral basis.
   The endomorphism a - 1 vanishes on every n-torsion point by the stated hypothesis.
3. By lem-sfb-abelian-torsion-kernel-divisibility, a - 1 = n b for some b in R;
   the hypotheses hold because k is algebraically closed and n is invertible.
4. Apply lem-sfb-finite-free-ring-congruence-torsion to a^r = 1 and a = 1 + n b.
   Its conclusion is the identity of group-scheme morphisms, hence of automorphisms.
The polarization identity can be checked on k-points: A is smooth and reduced over the
algebraically closed field, its closed points are dense, and its dual is separated. -/
theorem polarized_abelian_odd_level_rigidity
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (L : A.left.Modules) [Scheme.Modules.IsInvertible L] (hL : IsAmple A.hom L)
    (n : ℕ) (hn : 3 ≤ n) (hchar : IsUnit (n : k))
    (a : A ≅ A) [IsMonHom a.hom]
    (hpolarization : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      Scheme.Pic.map a.hom.left
          (abelianPolarizationPointMap A (Scheme.Pic.ofIsInvertible L) (x ≫ a.hom)) =
        abelianPolarizationPointMap A (Scheme.Pic.ofIsInvertible L) x)
    (hlevel : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      x ≫ (𝟙 A ^ n) = 1 → x ≫ a.hom = x) :
    a = Iso.refl A := by
  sorry

end AlgebraicGeometry
