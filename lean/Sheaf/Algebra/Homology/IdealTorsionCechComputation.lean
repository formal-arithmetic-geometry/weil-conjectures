/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Derived ideal torsion and the extended alternating localization complex

Source: Stacks Project, Tag 0956, the module assertion of
`lemma-compute-local-cohomology-noetherian`
(blueprint: lem-per-ideal-torsion-cech-computation).

The complex is indexed by natural numbers, with zero terms above the number of
listed generators; its extension to negative degrees is zero. Degree zero is the
original module, including when the generator list is empty. Every helper below
belongs to the explicit complex and its canonical fraction maps in this node.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped BigOperators

namespace ModuleCat
namespace IdealTorsionCech

variable {R : Type u} [CommRing R]

/-- Canonical localization along divisibility, characterized on numerators.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation).
Proof: write b = a*c. Send m/a^n to c^n*m/b^n. The localization fraction relation
shows independence of the representation and of c, and proves additivity and
R-linearity. The map sends m/1 to m/1. Uniqueness follows because multiplication
by a is invertible after inverting b: a has inverse c/b, so the image of m/a^n
is forced by the image of m/1. This also covers zero and unit denominators. -/
theorem localizationMap_existsUnique (M : ModuleCat.{u} R) (a b : R) (h : a ∣ b) :
    ∃! f : LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away b M,
      f.comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M) =
        LocalizedModule.mkLinearMap (Submonoid.powers b) M := by
  sorry

/-- The uniquely determined canonical fraction map when a divides b.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
noncomputable def localizationMap (M : ModuleCat.{u} R) (a b : R) (h : a ∣ b) :
    LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away b M :=
  (localizationMap_existsUnique M a b h).choose

/-- Product of the generators in an increasing tuple.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
def tupleProduct {r p : ℕ} (t : Fin r → R) (s : Fin p ↪o Fin r) : R :=
  ∏ i : Fin p, t (s i)

/-- Removing an index gives a divisor of the full tuple product.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation).
Proof: split the finite product at the omitted position a. The full product is
the product over all remaining positions multiplied by t(s(a)); commutativity
allows this factor to be moved to the end. -/
theorem faceProduct_dvd {r p : ℕ} (t : Fin r → R)
    (s : Fin (p + 1) ↪o Fin r) (a : Fin (p + 1)) :
    tupleProduct t ((Fin.succAboveOrderEmb a).trans s) ∣ tupleProduct t s := by
  sorry

/-- Terms of the extended alternating localization complex, including degree zero.
The function space over the empty set is the zero module, hence degrees above r vanish.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
def term {r : ℕ} (t : Fin r → R) (M : ModuleCat.{u} R) : ℕ → ModuleCat.{u} R
  | 0 => M
  | p + 1 => ModuleCat.of R
      (∀ s : Fin (p + 1) ↪o Fin r, LocalizedModule.Away (tupleProduct t s) M)

/-- The degree-zero localization map and the alternating higher differentials.
Position a in Lean starts at zero, giving the paper's sign (-1)^(a-1) at position a.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
noncomputable def differential {r : ℕ} (t : Fin r → R) (M : ModuleCat.{u} R) :
    ∀ p : ℕ, term t M p ⟶ term t M (p + 1)
  | 0 => ModuleCat.ofHom (LinearMap.pi fun s ↦
      LocalizedModule.mkLinearMap (Submonoid.powers (tupleProduct t s)) M)
  | p + 1 => ModuleCat.ofHom (LinearMap.pi fun s ↦
      ∑ a : Fin (p + 2), (-1 : ℤ) ^ a.val •
        (localizationMap M
          (tupleProduct t ((Fin.succAboveOrderEmb a).trans s))
          (tupleProduct t s) (faceProduct_dvd t s a)).comp
            (LinearMap.proj ((Fin.succAboveOrderEmb a).trans s)))

/-- The alternating localization differential squares to zero.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation).
Proof: in each target tuple, pair the two orders of deleting two distinct indices.
The canonical localization composites agree, since they agree on all numerators
and the source denominators act invertibly in the target. The two signs differ
by one, hence cancel. Starting in degree zero the two contributions are m/1
and -m/1. Beyond r all target coordinates are absent. -/
theorem differential_sq {r : ℕ} (t : Fin r → R) (M : ModuleCat.{u} R) (p : ℕ) :
    differential t M p ≫ differential t M (p + 1) = 0 := by
  sorry

/-- The displayed extended alternating localization cochain complex.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
noncomputable def complex {r : ℕ} (t : Fin r → R) (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (term t M) (differential t M) (differential_sq t M)

/-- A module map acts on every localized coordinate by m/u ↦ f(m)/u.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
noncomputable def mapTerm {r : ℕ} (t : Fin r → R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) : ∀ p : ℕ, term t M p ⟶ term t N p
  | 0 => f
  | _p + 1 => ModuleCat.ofHom (LinearMap.pi fun s ↦
      (IsLocalizedModule.map (Submonoid.powers (tupleProduct t s))
        (LocalizedModule.mkLinearMap (Submonoid.powers (tupleProduct t s)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (tupleProduct t s)) N)
        f.hom).comp (LinearMap.proj s))

/-- Fraction maps commute with the alternating differential.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation).
Proof: in degree zero both composites send m to f(m)/1. In positive degrees,
the two maps in each summand agree on numerators and therefore on fractions,
by the uniqueness of localization maps. Linearity commutes with the finite sum
and its integer signs, giving the identity in every coordinate. -/
theorem mapTerm_comm {r : ℕ} (t : Fin r → R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (p : ℕ) :
    mapTerm t f p ≫ (complex t N).d p (p + 1) =
      (complex t M).d p (p + 1) ≫ mapTerm t f (p + 1) := by
  sorry

/-- The canonical cochain map induced by a module homomorphism.
Source: Stacks, Tag 0956 (blueprint: lem-per-ideal-torsion-cech-computation). -/
noncomputable def map {r : ℕ} (t : Fin r → R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    complex t M ⟶ complex t N :=
  CochainComplex.ofHom (mapTerm t f) (mapTerm_comm t f)

end IdealTorsionCech

/-- The extended alternating localization complex computes derived ideal-power torsion,
naturally and R-linearly in every module, without finite-generation assumptions.
Source: Stacks Project, Tag 0956, module assertion
(blueprint: lem-per-ideal-torsion-cech-computation).

Proof: the explicit construction above is the displayed localization complex:
its degree-zero term is M, higher terms have increasing tuple indices and the
stated signs, and all degrees above r vanish. Apply
lem-per-local-cohomology-cech-bound (Tag 0956) to R, the list t, its generated
ideal, and q. Its natural linear comparison has direction H^q(C) to R^q Γ_K.
The torsion conventions n >= 1 and n in N agree, since exponent zero contributes
only zero, which is also killed by K. Invert the comparison to obtain e_M.
Naturality of the original comparison implies naturality of the inverse by
composing on either side with its inverse. Inverse linear maps are linear.
For r = 0, K = 0 and the complex is M in degree zero, as required. -/
theorem idealPowerTorsion_rightDerived_iso_cech
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (r : ℕ) (t : Fin r → R) (q : ℕ) :
    ∃ e : ∀ M : ModuleCat.{u} R,
      ((idealPowerTorsion (Ideal.span (Set.range t))).rightDerived q).obj M ≅
        (IdealTorsionCech.complex t M).homology q,
      ∀ {M N : ModuleCat.{u} R} (f : M ⟶ N),
        ((idealPowerTorsion (Ideal.span (Set.range t))).rightDerived q).map f ≫
            (e N).hom =
          (e M).hom ≫ HomologicalComplex.homologyMap (IdealTorsionCech.map t f) q := by
  sorry

end ModuleCat
