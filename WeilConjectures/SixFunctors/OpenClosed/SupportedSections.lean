/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Supports
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Sections supported on a closed subscheme

Let `s : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. For an étale sheaf `M`
on `X` the subsheaf of *sections supported on `Z`* is

`𝒢_Z M = ker (M ⟶ j_* j^* M)`,

the kernel of the unit of `j^* ⊣ j_*`. Its restriction to `U` vanishes, so it is the pushforward
of a sheaf on `Z`, namely of `s^! M := s^* 𝒢_Z M`, and `s_* s^! M ≅ 𝒢_Z M`. The functor `s^!` is
right adjoint to `s_*`: a map `s_* N ⟶ M` vanishes after restriction to `U`, hence factors
uniquely through `𝒢_Z M`. It is left exact but differs from `s^*`.

A sheaf `I` is *flasque for the pair* if `I ⟶ j_* j^* I` is an epimorphism; injective sheaves
are flasque.

## Main definitions

- `AlgebraicGeometry.Etale.supportedSections`: the functor `𝒢_Z`.
- `AlgebraicGeometry.Etale.closedUpperShriek`: the functor `s^!`.
- `AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`: the adjunction `s_* ⊣ s^!`.
- `AlgebraicGeometry.Etale.IsFlasqueFor`: flasque sheaves for the pair.

## Main statements

- `AlgebraicGeometry.Etale.closedUpperShriekCompLowerStarIso`: `s_* s^! ≅ 𝒢_Z`.
- `AlgebraicGeometry.Etale.isFlasqueFor_of_injective`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (s : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion s]

/-- Blueprint `def-pur-flasque-support`: Supported sections and flasque objects

The subsheaf `𝒢_Z M = ker (M ⟶ j_* j^* M)` of sections of `M` supported on the closed
complement `Z` of the open immersion `j : U ⟶ X`: the kernel of the unit of `j^* ⊣ j_*`. -/
@[simps]
noncomputable def supportedSections :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A where
  obj M := kernel ((upperStarLowerStarAdjunction A j).unit.app M)
  map {M N} f := kernel.map _ _ f ((j)_*[A].map ((j)^*[A].map f))
    ((upperStarLowerStarAdjunction A j).unit.naturality f).symm
  map_id M := by apply equalizer.hom_ext; simp
  map_comp f g := by apply equalizer.hom_ext; simp

/-- The inclusion `𝒢_Z M ⟶ M` of the supported sections. -/
@[simps]
noncomputable def supportedSectionsι : supportedSections A j ⟶ 𝟭 _ where
  app M := kernel.ι _

instance (M : Sheaf X.smallEtaleTopology A) : Mono ((supportedSectionsι A j).app M) := by
  change Mono (kernel.ι _); infer_instance

omit [IsOpenImmersion j] in
@[reassoc (attr := simp)]
lemma supportedSectionsι_app_comp_unit_app (M : Sheaf X.smallEtaleTopology A) :
    (supportedSectionsι A j).app M ≫ (upperStarLowerStarAdjunction A j).unit.app M = 0 :=
  kernel.condition _

/-- The supported sections vanish on the open part: `j^* 𝒢_Z M = 0`, since `j^*` is exact and
`j^*` of the unit `M ⟶ j_* j^* M` is an isomorphism. -/
lemma isZero_upperStar_obj_supportedSections (M : Sheaf X.smallEtaleTopology A) :
    IsZero ((j)^*[A].obj ((supportedSections A j).obj M)) :=
  (isZero_kernel_of_mono ((j)^*[A].map ((upperStarLowerStarAdjunction A j).unit.app M))).of_iso
    (PreservesKernel.iso (j)^*[A] _)

omit [IsOpenImmersion j] in
/-- A morphism `f : N ⟶ M` from a sheaf vanishing on the open part is supported on `Z`: its
composite with the unit `M ⟶ j_* j^* M` vanishes. -/
lemma comp_unit_app_eq_zero_of_isZero {N M : Sheaf X.smallEtaleTopology A}
    (hN : IsZero ((j)^*[A].obj N)) (f : N ⟶ M) :
    f ≫ (upperStarLowerStarAdjunction A j).unit.app M = 0 := by
  have h := (upperStarLowerStarAdjunction A j).unit.naturality f
  dsimp at h
  rw [h, ((j)_*[A].map_isZero hN).eq_of_tgt ((upperStarLowerStarAdjunction A j).unit.app N) 0,
    zero_comp]

omit [IsOpenImmersion j] in
/-- On a sheaf vanishing on the open part, the inclusion of the supported sections is an
isomorphism. -/
lemma isIso_supportedSectionsι_app_of_isZero {M : Sheaf X.smallEtaleTopology A}
    (hM : IsZero ((j)^*[A].obj M)) : IsIso ((supportedSectionsι A j).app M) := by
  have h : (upperStarLowerStarAdjunction A j).unit.app M = 0 := by
    simpa using comp_unit_app_eq_zero_of_isZero A j hM (𝟙 M)
  change IsIso (kernel.ι ((upperStarLowerStarAdjunction A j).unit.app M))
  have : IsSplitEpi (kernel.ι ((upperStarLowerStarAdjunction A j).unit.app M)) :=
    ⟨⟨kernel.lift _ (𝟙 M) (by rw [h, comp_zero]), by simp⟩⟩
  exact isIso_of_mono_of_epi _

variable {j s}

/-- A sheaf `K` with `j^* K = 0` is supported on the closed complement `s` of `j`: the unit
`K ⟶ s_* s^* K` of `s^* ⊣ s_*` is an isomorphism. Indeed `K ≅ s_* G`
(`AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`), and the unit at `s_* G`
is inverse to `s_*` of the counit at `G`, which is invertible as `s_*` is fully faithful. -/
lemma isIso_unit_app_of_isZero_upperStar (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    {K : Sheaf X.smallEtaleTopology A} (hK : IsZero ((j)^*[A].obj K)) :
    IsIso ((upperStarLowerStarAdjunction A s).unit.app K) := by
  let : Reflective ((s)_*[A]) := { L := (s)^*[A], adj := upperStarLowerStarAdjunction A s }
  exact Functor.essImage.unit_isIso (mem_essImage_lowerStar_of_isZero_upperStar s hjs hK)

variable (j s)

/-- Blueprint `def-pur-flasque-support`: Supported sections and flasque objects

The functor `s^! M = s^* 𝒢_Z M` of a closed immersion `s : Z ⟶ X` with open complement
`j : U ⟶ X`: the supported sections, regarded as a sheaf on `Z`. It is left exact and right
adjoint to `s_*` (`AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`), and it is
distinct from the ordinary restriction `s^*`. -/
noncomputable def closedUpperShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A :=
  supportedSections A j ⋙ (s)^*[A]

/-- `s_* s^! M ≅ 𝒢_Z M`: the supported sections are the pushforward of `s^! M`, through the unit
of `s^* ⊣ s_*`, which is invertible on sheaves vanishing on the open part. -/
noncomputable def closedUpperShriekCompLowerStarIso
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) :
    closedUpperShriek A j s ⋙ (s)_*[A] ≅ supportedSections A j :=
  NatIso.ofComponents (fun M ↦
    haveI := isIso_unit_app_of_isZero_upperStar A hjs (isZero_upperStar_obj_supportedSections A j M)
    (asIso ((upperStarLowerStarAdjunction A s).unit.app ((supportedSections A j).obj M))).symm)
    (fun f ↦ by
      dsimp [closedUpperShriek]
      rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp]
      exact ((upperStarLowerStarAdjunction A s).unit.naturality _).symm)

/-- The counit `s_* s^! M ⟶ M` of `s_* ⊣ s^!`: the identification `s_* s^! M ≅ 𝒢_Z M` followed by
the inclusion of the supported sections. -/
noncomputable def closedUpperShriekCounit (hjs : Set.range s.base = (Set.range j.base)ᶜ) :
    closedUpperShriek A j s ⋙ (s)_*[A] ⟶ 𝟭 _ :=
  (closedUpperShriekCompLowerStarIso A j s hjs).hom ≫ supportedSectionsι A j

instance (hjs : Set.range s.base = (Set.range j.base)ᶜ) (M : Sheaf X.smallEtaleTopology A) :
    Mono ((closedUpperShriekCounit A j s hjs).app M) := by
  dsimp [closedUpperShriekCounit]
  infer_instance

/-- Every map `s_* N ⟶ M` factors uniquely through the counit `s_* s^! M ⟶ M`, as a map
`s_* N ⟶ s_* s^! M`, hence as `s_*` of a unique map `N ⟶ s^! M`. -/
lemma bijective_lowerStar_map_comp_closedUpperShriekCounit
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) (N : Sheaf Z.smallEtaleTopology A)
    (M : Sheaf X.smallEtaleTopology A) :
    Function.Bijective (fun g : N ⟶ (closedUpperShriek A j s).obj M ↦
      (s)_*[A].map g ≫ (closedUpperShriekCounit A j s hjs).app M) := by
  have hdisj : Disjoint (Set.range j.base) (Set.range s.base) := by
    rw [hjs]; exact disjoint_compl_right
  have hN : IsZero ((j)^*[A].obj ((s)_*[A].obj N)) :=
    isZero_upperStar_lowerStar_of_disjoint_range A j s hdisj N
  refine ⟨fun g g' h ↦ (s)_*[A].map_injective ((cancel_mono _).1 h), fun f ↦ ?_⟩
  let φ : (s)_*[A].obj N ⟶ (supportedSections A j).obj M :=
    kernel.lift _ f (comp_unit_app_eq_zero_of_isZero A j hN f)
  refine ⟨(s)_*[A].preimage (φ ≫ (closedUpperShriekCompLowerStarIso A j s hjs).inv.app M), ?_⟩
  simp [closedUpperShriekCounit, φ]

/-- Maps `N ⟶ s^! M` are maps `s_* N ⟶ M`, by composition with the counit `s_* s^! M ⟶ M`. -/
noncomputable def closedUpperShriekHomEquiv (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (N : Sheaf Z.smallEtaleTopology A) (M : Sheaf X.smallEtaleTopology A) :
    (N ⟶ (closedUpperShriek A j s).obj M) ≃ ((s)_*[A].obj N ⟶ M) :=
  Equiv.ofBijective _ (bijective_lowerStar_map_comp_closedUpperShriekCounit A j s hjs N M)

@[simp]
lemma closedUpperShriekHomEquiv_apply (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    {N : Sheaf Z.smallEtaleTopology A} {M : Sheaf X.smallEtaleTopology A}
    (g : N ⟶ (closedUpperShriek A j s).obj M) :
    closedUpperShriekHomEquiv A j s hjs N M g =
      (s)_*[A].map g ≫ (closedUpperShriekCounit A j s hjs).app M :=
  rfl

/-- Blueprint `def-pur-flasque-support`: Supported sections and flasque objects

The adjunction `s_* ⊣ s^!`: every map `s_* N ⟶ M` has image supported on `Z`, hence factors
uniquely through `𝒢_Z M = s_* s^! M`, and `s_*` is fully faithful. -/
noncomputable def lowerStarClosedUpperShriekAdjunction
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) :
    (s)_*[A] ⊣ closedUpperShriek A j s :=
  Adjunction.mkOfHomEquiv
    { homEquiv N M := (closedUpperShriekHomEquiv A j s hjs N M).symm
      homEquiv_naturality_left_symm f g := by simp
      homEquiv_naturality_right {N M M'} f g := by
        apply (closedUpperShriekHomEquiv A j s hjs N M').injective
        have h := (closedUpperShriekCounit A j s hjs).naturality g
        dsimp at h
        simp only [Equiv.apply_symm_apply, closedUpperShriekHomEquiv_apply, Functor.map_comp,
          assoc, h]
        rw [← assoc, ← closedUpperShriekHomEquiv_apply, Equiv.apply_symm_apply] }

@[simp]
lemma lowerStarClosedUpperShriekAdjunction_counit_app
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) (M : Sheaf X.smallEtaleTopology A) :
    (lowerStarClosedUpperShriekAdjunction A j s hjs).counit.app M =
      (closedUpperShriekCounit A j s hjs).app M := by
  simp [lowerStarClosedUpperShriekAdjunction, Adjunction.mkOfHomEquiv]

/-- Blueprint `def-pur-flasque-support`: Supported sections and flasque objects

A sheaf `I` on `X` is *flasque for the pair* `(Z, U)` if the restriction `I ⟶ j_* j^* I` to the
open part is an epimorphism; then `0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0` is exact. -/
def IsFlasqueFor (I : Sheaf X.smallEtaleTopology A) : Prop :=
  Epi ((upperStarLowerStarAdjunction A j).unit.app I)

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
/-- Injective sheaves are flasque for the pair: the restriction `I ⟶ j_* j^* I` is even a split
epimorphism
(`AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`). -/
lemma isFlasqueFor_of_injective (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : Sheaf X.smallEtaleTopology A) [Injective I] : IsFlasqueFor A j I := by
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A j s hjs I
  unfold IsFlasqueFor; infer_instance

end Concrete

end Etale

end AlgebraicGeometry
