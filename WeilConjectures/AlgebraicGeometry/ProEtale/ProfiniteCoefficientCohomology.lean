/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Algebra.Group.Quotient
public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyTowerLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology

/-!
# Pro-étale cohomology with profinite coefficients

Let `L` be a compact Hausdorff topological abelian group with a decreasing sequence of open
subgroups `Uₘ` with trivial intersection, e.g. a lattice `ℤ_ℓⁿ` with `Uₘ = ℓᵐ ℤ_ℓⁿ`. The sheaf
`U ↦ C(U, L)` on `S_proét` is the limit of the tower of the sheaves `U ↦ C(U, L/Uₘ)` of
continuous functions to the finite discrete groups `L/Uₘ`, whose transition maps are
epimorphisms. By repleteness of the pro-étale topos
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isLimit_tower`), the vanishing of
`Hᵠ(S_proét, L/Uₘ)` for `q > 2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt`)
passes to `L`: the transition maps are surjective on `H^{2d}`, the kernels `Uₘ/Uₘ₊₁` having
no `H^{2d+1}`.

## Main statements

- `AlgebraicGeometry.ProEtale.epi_continuousSheafMap`: a surjection onto a discrete group
  induces an epimorphism of sheaves of continuous functions.
- `AlgebraicGeometry.ProEtale.surjective_H_map_continuousSheafMap`: right exactness of the top
  cohomology for such a surjection with finite discrete kernel.
- `AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt_of_compact`:
  `Hᵠ(S_proét, L) = 0` for `q > 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (S : Scheme.{u})

section Exact

variable {A B : Type} [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
  [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- A surjective continuous homomorphism onto a discrete group induces an epimorphism of
pro-étale sheaves of continuous functions: a continuous function to the discrete group is
constant on the open fibres, which form a Zariski cover, and constants lift. -/
lemma epi_continuousSheafMap [DiscreteTopology B] (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) : Epi (continuousSheafMap S φ) := by
  have : Presheaf.IsLocallySurjective (ProEt.topology S) (continuousSheafMap S φ).hom := by
    refine ⟨fun {U} s₀ ↦ ?_⟩
    let s : C(U.left, B) := s₀.down
    choose a ha using hφ
    refine ProEt.mem_topology_of_openImmersion _
      (fun x : U.left ↦ (U.left.fiberOpens s (s x)).ι)
      (fun x ↦ ⟨x, ⟨x, rfl⟩, Scheme.Opens.ι_apply _ _⟩)
      fun x ↦ ⟨ULift.up (ContinuousMap.const _ (a (s x))), ?_⟩
    exact congrArg ULift.up (ContinuousMap.ext fun y ↦ (ha (s x)).trans y.2.symm)
  exact (Sheaf.isLocallySurjective_iff_epi' _ _).1 this

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- A short complex of abelian sheaves which is left exact on sections and whose second map is
an epimorphism of sheaves is short exact. -/
lemma shortExact_of_sections (T : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}))
    (hf : ∀ U, Function.Injective (T.f.hom.app U))
    (hex : ∀ U y, T.g.hom.app U y = 0 → ∃ x, T.f.hom.app U x = y) [Epi T.g] :
    T.ShortExact := by
  let P := T.map (sheafToPresheaf J AddCommGrpCat.{u + 1})
  have hP : P.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro U
    rw [ShortComplex.ab_exact_iff]
    exact hex U
  have hT : T.Exact := ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso T (sheafificationNatIso J _)).symm
    (hP.map (presheafToSheaf J AddCommGrpCat.{u + 1}))
  have : Mono T.f := by
    have : Mono ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map T.f) := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (AddCommGrpCat.mono_iff_injective _).2 (hf U)
    exact (sheafToPresheaf J _).mono_of_mono_map this
  exact ShortComplex.ShortExact.mk' hT inferInstance inferInstance

variable [DiscreteTopology A] [DiscreteTopology B]

/-- The inclusion of the kernel of a continuous homomorphism, as a continuous homomorphism. -/
def kerSubtype (φ : ContinuousAddMonoidHom A B) :
    ContinuousAddMonoidHom (φ.toAddMonoidHom.ker) A :=
  ⟨φ.toAddMonoidHom.ker.subtype, continuous_subtype_val⟩

/-- The short exact sequence `0 ⟶ C(-, ker φ) ⟶ C(-, A) ⟶ C(-, B) ⟶ 0` of pro-étale sheaves of a
surjection `φ : A ⟶ B` of discrete groups. -/
lemma shortExact_continuousSheafMap (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) :
    (ShortComplex.mk (continuousSheafMap S (kerSubtype φ)) (continuousSheafMap S φ) (by
      apply Sheaf.hom_ext
      ext U f
      exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ (f.down t).2))).ShortExact := by
  have := epi_continuousSheafMap S φ hφ
  refine shortExact_of_sections _ (fun U x y h ↦ ?_) (fun U y hy ↦ ?_)
  · exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ Subtype.ext
      (congrArg (fun f : ULift.{u + 1} C(U.unop.left, A) ↦ f.down t) h))
    exact ⟨ULift.up ⟨fun t ↦ ⟨y' t, hy' t⟩, by fun_prop⟩, rfl⟩

/-- **Right exactness of the top cohomology.** For a surjection `φ : A ⟶ B` of discrete
groups whose kernel has no cohomology in degree `N + 1`, the map
`H^N(S_proét, A) ⟶ H^N(S_proét, B)` is surjective. -/
lemma surjective_H_map_continuousSheafMap (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) (N : ℕ)
    (h : Subsingleton (Sheaf.H (continuousSheaf S φ.toAddMonoidHom.ker) (N + 1))) :
    Function.Surjective (Sheaf.H.map (continuousSheafMap S φ) N) := fun y ↦
  ((Sheaf.H.exact_map_δSucc (shortExact_continuousSheafMap S φ hφ) N) y).1
    (Subsingleton.elim _ _)

end Exact

end AlgebraicGeometry.ProEtale
