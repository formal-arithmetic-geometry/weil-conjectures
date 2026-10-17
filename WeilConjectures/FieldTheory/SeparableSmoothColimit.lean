/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import WeilConjectures.FieldTheory.SeparableExtension

/-! # Separable field extensions are filtered unions of smooth subalgebras

Generic smoothness for fraction fields, and its consequence: a separable field extension
`L / K` is the directed union of its finite type smooth `K`-subalgebras.

## Main statements

* `Algebra.exists_smooth_localizationAway_of_formallySmooth`: a finite type domain over a
  field whose fraction field is formally smooth has a smooth principal localization `A_g`,
  `g ≠ 0` (generic smoothness).
* `Algebra.exists_smooth_subalgebra_of_isSeparable` (blueprint
  `lem-kun-algebraic-separable-smooth`),
* `Algebra.exists_smooth_subalgebra_of_isSeparablyGenerated` (blueprint
  `lem-kun-fg-separable-smooth`),
* `Algebra.exists_smooth_subalgebra_of_isSeparableExtension` (blueprint
  `lem-kun-separable-smooth-colimit`): every finite subset of `L` lies in a finite type smooth
  `K`-subalgebra of `L`.
* `Algebra.directedOn_smooth_finiteType_subalgebra_of_isSeparableExtension`,
  `Algebra.sSup_smooth_finiteType_subalgebra_of_isSeparableExtension`: the finite type smooth
  `K`-subalgebras of `L` form a directed family with union `L`.
-/

@[expose] public section

namespace Algebra

open scoped IntermediateField.algebraAdjoinAdjoin

section Directed

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- If every finite subset of `B` is contained in a finite type `R`-subalgebra satisfying `P`,
then the finite type `R`-subalgebras satisfying `P` form a directed family. -/
theorem directedOn_setOf_finiteType_of_forall_finset {P : Subalgebra R B → Prop}
    (h : ∀ s : Finset B, ∃ S : Subalgebra R B, P S ∧ FiniteType R S ∧ (s : Set B) ⊆ S) :
    DirectedOn (· ≤ ·) {S : Subalgebra R B | P S ∧ FiniteType R S} := by
  classical
  rintro S₁ ⟨-, h₁⟩ S₂ ⟨-, h₂⟩
  obtain ⟨t₁, rfl⟩ := (Subalgebra.fg_iff_finiteType S₁).2 h₁
  obtain ⟨t₂, rfl⟩ := (Subalgebra.fg_iff_finiteType S₂).2 h₂
  obtain ⟨S, hP, hS, hsub⟩ := h (t₁ ∪ t₂)
  refine ⟨S, ⟨hP, hS⟩, adjoin_le fun x hx ↦ hsub ?_, adjoin_le fun x hx ↦ hsub ?_⟩ <;>
    simp [hx]

/-- If every finite subset of `B` is contained in a finite type `R`-subalgebra satisfying `P`,
then the finite type `R`-subalgebras satisfying `P` have union `B`. -/
theorem sSup_setOf_finiteType_eq_top_of_forall_finset {P : Subalgebra R B → Prop}
    (h : ∀ s : Finset B, ∃ S : Subalgebra R B, P S ∧ FiniteType R S ∧ (s : Set B) ⊆ S) :
    sSup {S : Subalgebra R B | P S ∧ FiniteType R S} = ⊤ := by
  classical
  refine Algebra.eq_top_iff.2 fun x ↦ ?_
  obtain ⟨S, hP, hS, hsub⟩ := h {x}
  have hmem : S ∈ {S : Subalgebra R B | P S ∧ FiniteType R S} := ⟨hP, hS⟩
  exact le_sSup hmem (hsub (Finset.mem_coe.2 (Finset.mem_singleton_self x)))

end Directed

/-- **Generic smoothness.** Let `A` be a finite type domain over a field `K` whose fraction
field `F` is formally smooth over `K` (e.g. separably generated over `K`). Then there is a
nonzero `g ∈ A` such that `A_g` is smooth over `K`.

Proof: `A` is of finite presentation. The localization of `A` at the prime `(0)` is the
fraction field `F`, so `A` is smooth at `(0)`; the smooth locus is open, so it contains a
basic open neighbourhood `D(g)` of `(0)`. -/
theorem exists_smooth_localizationAway_of_formallySmooth (K A F : Type*) [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [FiniteType K A] [Field F] [Algebra K F] [Algebra A F]
    [IsScalarTower K A F] [IsFractionRing A F] [FormallySmooth K F] :
    ∃ g : A, g ≠ 0 ∧ Smooth K (Localization.Away g) := by
  have : FinitePresentation K A := FinitePresentation.of_finiteType.mp inferInstance
  have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  let e : Localization.AtPrime (⊥ : Ideal A) ≃ₐ[A] F :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ F
  have : IsSmoothAt K (⊥ : Ideal A) := FormallySmooth.of_equiv (e.restrictScalars K).symm
  obtain ⟨g, hg, h⟩ := IsSmoothAt.exists_notMem_smooth (R := K) (⊥ : Ideal A)
  exact ⟨g, hg, h⟩

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Let `A` be a finite type `K`-subalgebra of a field `L` whose fraction field `F` is formally
smooth over `K`. Then `A` is contained in a finite type smooth `K`-subalgebra of `L`, namely the
image of a smooth localization `A_g` (generic smoothness). -/
theorem exists_smooth_subalgebra_ge_of_formallySmooth (A : Subalgebra K L) [FiniteType K A]
    (F : Type*) [Field F] [Algebra K F] [Algebra A F] [IsScalarTower K A F]
    [IsFractionRing A F] [FormallySmooth K F] :
    ∃ S : Subalgebra K L, A ≤ S ∧ Smooth K S ∧ FiniteType K S := by
  obtain ⟨g, hg, hsm⟩ := exists_smooth_localizationAway_of_formallySmooth K A F
  have hu (y : Submonoid.powers g) : IsUnit (A.val y) := by
    refine IsUnit.mk0 _ ?_
    obtain ⟨_, n, rfl⟩ := y
    simpa using pow_ne_zero n hg
  let φ : Localization.Away g →ₐ[K] L := IsLocalization.liftAlgHom hu
  have hφ : Function.Injective φ := by
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective (Localization.Away g)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg)).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have : Smooth K φ.range := Smooth.of_equiv (AlgEquiv.ofInjective φ hφ)
  refine ⟨φ.range, fun a ha ↦ ⟨algebraMap A _ ⟨a, ha⟩, ?_⟩, this, inferInstance⟩
  simp [φ]

/-- A finitely generated intermediate field of a separable field extension (in the sense of
`Algebra.IsSeparableExtension`) is formally smooth. -/
theorem formallySmooth_of_isSeparableExtension (h : IsSeparableExtension K L)
    (F : IntermediateField K L) (hF : F.FG) : FormallySmooth K F := by
  obtain ⟨s, hs, hsep⟩ := h F hF
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F := by
    rwa [Subtype.range_coe]
  exact FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- Blueprint `lem-kun-separable-smooth-colimit`: a separable field extension `L / K` is the
filtered union of its finite type smooth `K`-subalgebras: every finite subset of `L` lies in
a finite type smooth `K`-subalgebra of `L`. See
`directedOn_smooth_finiteType_subalgebra_of_isSeparableExtension` and
`sSup_smooth_finiteType_subalgebra_of_isSeparableExtension` for the directed-union form;
`Spec L` is then the limit of the affine smooth `K`-schemes `Spec S` along the (affine)
morphisms induced by the inclusions.

Proof: for a finite `s ⊆ L`, the field `K(s)` is finitely generated, hence separably generated,
hence formally smooth over `K`; it is the fraction field of the finite type algebra `K[s]`, so
generic smoothness gives a smooth `K[s]_g ⊆ L` containing `s`. -/
theorem exists_smooth_subalgebra_of_isSeparableExtension (h : IsSeparableExtension K L)
    (s : Finset L) : ∃ S : Subalgebra K L, Smooth K S ∧ FiniteType K S ∧ (s : Set L) ⊆ S := by
  have := formallySmooth_of_isSeparableExtension h _ (IntermediateField.fg_adjoin_finset s)
  have : FiniteType K (adjoin K (s : Set L)) := .adjoin_of_finite s.finite_toSet
  obtain ⟨S, hle, hS, hft⟩ := exists_smooth_subalgebra_ge_of_formallySmooth
    (adjoin K (s : Set L)) (IntermediateField.adjoin K (s : Set L))
  exact ⟨S, hS, hft, subset_adjoin.trans hle⟩

/-- The finite type smooth `K`-subalgebras of a separable extension `L / K` form a directed
family (companion of `lem-kun-separable-smooth-colimit`). -/
theorem directedOn_smooth_finiteType_subalgebra_of_isSeparableExtension
    (h : IsSeparableExtension K L) :
    DirectedOn (· ≤ ·) {S : Subalgebra K L | Smooth K S ∧ FiniteType K S} :=
  directedOn_setOf_finiteType_of_forall_finset
    (exists_smooth_subalgebra_of_isSeparableExtension h)

/-- The finite type smooth `K`-subalgebras of a separable extension `L / K` have union `L`
(companion of `lem-kun-separable-smooth-colimit`). -/
theorem sSup_smooth_finiteType_subalgebra_of_isSeparableExtension
    (h : IsSeparableExtension K L) :
    sSup {S : Subalgebra K L | Smooth K S ∧ FiniteType K S} = ⊤ :=
  sSup_setOf_finiteType_eq_top_of_forall_finset
    (exists_smooth_subalgebra_of_isSeparableExtension h)

/-- Blueprint `lem-kun-fg-separable-smooth`: a finitely generated separably generated field
extension `L / K` (Stacks 07BV) is the filtered union of its finite type smooth
`K`-subalgebras: every finite subset of `L` lies in a finite type smooth `K`-subalgebra.

Proof: let `t` generate `L` as a field. For a finite `s ⊆ L`, the algebra `K[s ∪ t]` is of
finite type with fraction field `K(s ∪ t) = L`, which is formally smooth over `K` since it is
separably generated. Generic smoothness gives a smooth `K[s ∪ t]_g ⊆ L` containing `s`. -/
theorem exists_smooth_subalgebra_of_isSeparablyGenerated
    (hfg : (⊤ : IntermediateField K L).FG) (h : IsSeparablyGenerated K L) (s : Finset L) :
    ∃ S : Subalgebra K L, Smooth K S ∧ FiniteType K S ∧ (s : Set L) ⊆ S := by
  classical
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨b, hb, hsep⟩ := h
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : b → L))) L := by
    rwa [Subtype.range_coe]
  have : FormallySmooth K L := FormallySmooth.of_algebraicIndependent_of_isSeparable hb.1
  let u : Finset L := s ∪ t
  have hu : IntermediateField.adjoin K (u : Set L) = ⊤ :=
    top_le_iff.1 (ht ▸ IntermediateField.adjoin.mono _ _ _ (by simp [u]))
  have : FormallySmooth K (IntermediateField.adjoin K (u : Set L)) := by
    rw [hu]
    exact .of_equiv IntermediateField.topEquiv.symm
  have : FiniteType K (adjoin K (u : Set L)) := .adjoin_of_finite u.finite_toSet
  obtain ⟨S, hle, hS, hft⟩ := exists_smooth_subalgebra_ge_of_formallySmooth
    (adjoin K (u : Set L)) (IntermediateField.adjoin K (u : Set L))
  exact ⟨S, hS, hft, fun x hx ↦ hle (subset_adjoin (by simp [u, hx]))⟩

/-- Blueprint `lem-kun-algebraic-separable-smooth`: an algebraic separable extension `L / K`
is the filtered union of its finite separable subextensions, which are finite étale, hence
smooth, `K`-algebras: every finite subset of `L` lies in a finite type smooth (indeed étale)
`K`-subalgebra of `L`.

Proof: for a finite `s ⊆ L`, the field `K(s)` is finite and separable over `K`, hence étale
over `K`. -/
theorem exists_smooth_subalgebra_of_isSeparable [Algebra.IsSeparable K L] (s : Finset L) :
    ∃ S : Subalgebra K L, Smooth K S ∧ FiniteType K S ∧ (s : Set L) ⊆ S := by
  let F := IntermediateField.adjoin K (s : Set L)
  have : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsSeparable.isSeparable K x).isIntegral
  have : Algebra.IsSeparable K F := .of_algHom K L F.val
  have : FormallyEtale K F := .of_isSeparable K F
  have : FinitePresentation K F := FinitePresentation.of_finiteType.mp inferInstance
  have : Etale K F := ⟨inferInstance, inferInstance⟩
  exact ⟨F.toSubalgebra, inferInstanceAs (Smooth K F), inferInstanceAs (FiniteType K F),
    IntermediateField.subset_adjoin K _⟩

end Algebra
