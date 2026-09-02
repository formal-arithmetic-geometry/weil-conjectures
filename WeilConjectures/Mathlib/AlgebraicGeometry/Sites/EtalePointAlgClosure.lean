/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Geometric points with algebraically closed residue fields

For a scheme `S : Scheme.{u}` and a point `s : S`, the algebraic closure of the residue field
of `s` gives a geometric point `AlgebraicGeometry.Scheme.algClosurePoint s : Spec Ω ⟶ S` with
`Ω` algebraically closed. These points form a conservative family
(`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_algClosurePoint`),
exactly as the geometric points given by the separable closures of the residue fields of
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. They are used where the
algebraic closedness of the residue field is needed, as in the stalk formula for finite direct
images.

## Main results

- `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map_algClosurePoint`: a morphism of
  `A`-valued étale sheaves which is invertible on the fibres at all these points is invertible.
- `AlgebraicGeometry.Scheme.eq_zero_of_forall_sheafFiber_map_algClosurePoint_eq_zero`: a
  morphism of étale sheaves vanishing on all these fibres is zero.
- `AlgebraicGeometry.Scheme.epi_of_forall_epi_sheafFiber_map_algClosurePoint`: a morphism
  of étale sheaves which is an epimorphism on all these fibres is an epimorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The geometric point of `S` at `s` given by the algebraic closure of the residue field. -/
noncomputable def algClosurePoint (s : S) :
    Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  (SpecToEquivOfField (AlgebraicClosure (S.residueField s)) _).2
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩

/-- **The universe-lifted geometric points of `S` with algebraically closed residue fields form
a conservative family.** -/
lemma isConservativeFamilyOfPoints_ulift_pointSmallEtale_algClosurePoint :
    (ObjectProperty.ofObj fun s : S ↦
      (pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}).IsConservativeFamilyOfPoints :=
  have h : ⋃ s, Set.range (S.algClosurePoint s) = Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, by simp [algClosurePoint, SpecToEquivOfField]⟩
  (isConservative_pointSmallEtale (fun s ↦ S.algClosurePoint s) h).ulift.{u + 1, u, u, u + 1, u} _

variable (A : Type u') [Category.{u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {S A}

include hJ in
/-- A morphism of `A`-valued sheaves on the small étale site of `S` whose fibre at every
geometric point with algebraically closed residue field is invertible is invertible. -/
lemma isIso_of_isIso_sheafFiber_map_algClosurePoint {F G : Sheaf S.smallEtaleTopology A}
    (φ : F ⟶ G)
    (h : ∀ s : S,
      IsIso (((pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map φ)) :
    IsIso φ :=
  (((isConservativeFamilyOfPoints_ulift_pointSmallEtale_algClosurePoint
    S).jointlyReflectIsomorphisms A).isIso_iff φ).2 (by
      rintro ⟨-, ⟨s⟩⟩
      exact h s)

section Abelian

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

include hJ in
/-- A morphism of `A`-valued étale sheaves whose fibre at every geometric point with
algebraically closed residue field vanishes is zero: its kernel inclusion is invertible on all
fibres, since the fibre functors are exact. -/
lemma eq_zero_of_forall_sheafFiber_map_algClosurePoint_eq_zero
    {F G : Sheaf S.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ s : S, ((pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map φ = 0) :
    φ = 0 := by
  have : IsIso (kernel.ι φ) := by
    refine isIso_of_isIso_sheafFiber_map_algClosurePoint (kernel.ι φ) fun s ↦ ?_
    set Φ := (pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}
    rw [← kernelComparison_comp_ι φ Φ.sheafFiber]
    have : IsIso (kernel.ι (Φ.sheafFiber.map φ)) := kernel.ι_of_zero (h s)
    infer_instance
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

include hJ in
/-- A morphism of `A`-valued étale sheaves which is an epimorphism on the fibres at all
geometric points with algebraically closed residue fields is an epimorphism: its cokernel
projection vanishes on all fibres, since the fibre functors are exact. -/
lemma epi_of_forall_epi_sheafFiber_map_algClosurePoint
    {F G : Sheaf S.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ s : S, Epi (((pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map φ)) :
    Epi φ := by
  refine Abelian.epi_of_cokernel_π_eq_zero φ
    (eq_zero_of_forall_sheafFiber_map_algClosurePoint_eq_zero _ fun s ↦ ?_)
  set Φ := (pointSmallEtale (S.algClosurePoint s)).ulift.{u + 1}
  have := h s
  rw [← π_comp_cokernelComparison φ Φ.sheafFiber, cokernel.π_of_epi, zero_comp]

end Abelian

end AlgebraicGeometry.Scheme
