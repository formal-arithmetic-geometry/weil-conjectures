/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Simple constructible sheaves

TODO
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X Y : Scheme.{u}}

lemma isZero_sheafFiber_of_isZero {I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hI : IsZero I) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsZero ((pointSmallEtale s).sheafFiber.obj I) :=
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  (pointSmallEtale s).sheafFiber.map_isZero hI

lemma isZero_iff_stalkZeroLocus_eq_univ (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero I ↔ stalkZeroLocus I = Set.univ := by
  refine ⟨fun hI ↦ Set.eq_univ_of_forall fun x Ω _ _ s _ ↦ isZero_sheafFiber_of_isZero hI s,
    fun hall ↦ ?_⟩
  have : IsIso (0 : I ⟶ I) := isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj I) :=
      ((hall ▸ Set.mem_univ x : x ∈ stalkZeroLocus I) _ (X.algClosurePoint x)
        (X.algClosurePoint_base x _)).of_iso
        (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app I)
    exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : I ⟶ I), zero_comp]

lemma mem_stalkZeroLocus_upperStar (f : Y ⟶ X)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {y : Y}
    (hy : f.base y ∈ stalkZeroLocus I) :
    y ∈ stalkZeroLocus (((f)^*[ModuleCat.{u + 1} Λ]).obj I) := fun Ω _ _ s hs ↦
  (hy Ω (s ≫ f) (by rw [← hs]; rfl)).of_iso
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f s).app I)

lemma mem_stalkZeroLocus_of_upperStar (f : Y ⟶ X) [IsImmersion f]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {y : Y}
    (hy : y ∈ stalkZeroLocus (((f)^*[ModuleCat.{u + 1} Λ]).obj I)) :
    f.base y ∈ stalkZeroLocus I := by
  intro Ω _ _ s hs
  have h₁ : Set.range s.base ⊆ Set.range f.coborderRange.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint Ω), hs]
    exact ⟨f.liftCoborder.base y, by rw [← Scheme.Hom.comp_apply, f.liftCoborder_ι]⟩
  set s' := IsOpenImmersion.lift f.coborderRange.ι s h₁
  have hs' : s' ≫ f.coborderRange.ι = s := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨t, ht, -⟩ := IsClosedImmersion.existsUnique_fac_of_field f.liftCoborder s' (by
    refine ⟨y, f.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, f.liftCoborder_ι, ← hs, ← hs']
    rfl)
  have htf : t ≫ f = s := by rw [← f.liftCoborder_ι, ← Category.assoc, ht, hs']
  subst htf
  refine (hy Ω t ?_).of_iso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f t).app I).symm
  exact f.isEmbedding.injective hs

/-- The closed complement of an open subscheme, with its range. -/
lemma range_closedComplement_eq_compl_range_ι (W : X.Opens) :
    Set.range W.closedComplement.base = (Set.range W.ι.base)ᶜ := by
  rw [W.range_closedComplement, Scheme.Opens.range_ι]

variable [IsNoetherianRing Λ] [TopologicalSpace.NoetherianSpace X]

/-- A constructible sheaf all of whose constructible subsheaves are zero or everything is
supported either inside or outside a given open. -/
lemma subset_stalkZeroLocus_or_compl_subset (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (hF : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : G ⟶ F), Mono ι →
      IsConstructibleSheaf G → IsZero G ∨ IsIso ι) (W : X.Opens) :
    (W : Set X) ⊆ stalkZeroLocus F ∨ (W : Set X)ᶜ ⊆ stalkZeroLocus F := by
  have hij := range_closedComplement_eq_compl_range_ι W
  have hS := Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement F hij
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsConstructibleSheaf (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    IsConstructibleSheaf.upperStar _ _
  have := IsConstructibleSheaf.openImmersionLowerShriek W.ι W.closedComplement hij
    (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)
  rcases hF _ _ hS.mono_f this with h | h
  · left
    intro x hx
    have hz : IsZero (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      (((W.ι)^*[ModuleCat.{u + 1} Λ]).map_isZero h).of_iso
        (asIso (((W.ι)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).counit.app F))).symm
    have := mem_stalkZeroLocus_of_upperStar W.ι F (y := ⟨x, hx⟩)
      ((isZero_iff_stalkZeroLocus_eq_univ _).1 hz ▸ Set.mem_univ _)
    exact this
  · right
    intro x hx
    have h₃ : IsZero ((W.closedComplement)_*[ModuleCat.{u + 1} Λ].obj
        (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F)) := hS.isIso_f_iff.1 h
    have hz : IsZero (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).map_isZero h₃).of_iso
        (asIso ((Etale.upperStarLowerStarAdjunction _ W.closedComplement).counit.app _)).symm
    obtain ⟨z, rfl⟩ : x ∈ Set.range W.closedComplement.base := by
      rw [hij, Scheme.Opens.range_ι]; exact hx
    exact mem_stalkZeroLocus_of_upperStar W.closedComplement F
      ((isZero_iff_stalkZeroLocus_eq_univ _).1 hz ▸ Set.mem_univ _)

/-- A nonzero constructible sheaf all of whose constructible subsheaves are zero or everything
is supported at a single point. -/
lemma exists_compl_stalkZeroLocus_eq_singleton
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF₀ : ¬ IsZero F)
    (hF : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : G ⟶ F), Mono ι →
      IsConstructibleSheaf G → IsZero G ∨ IsIso ι) :
    ∃ x : X, (stalkZeroLocus F)ᶜ = {x} := by
  obtain ⟨x, hx⟩ : ((stalkZeroLocus F)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun h ↦ hF₀ ((isZero_iff_stalkZeroLocus_eq_univ F).2 h)
  refine ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy ↦ ?_⟩⟩
  by_contra hxy
  obtain ⟨U, hU, hUxy⟩ := exists_isOpen_xor_mem hxy
  rcases subset_stalkZeroLocus_or_compl_subset F hF ⟨U, hU⟩ with h | h <;>
    rcases hUxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hy (h h₁)
  · exact hx (h h₁)
  · exact hx (h h₂)
  · exact hy (h h₂)

omit [IsNoetherianRing Λ] [TopologicalSpace.NoetherianSpace X] in
/-- If a constructible sheaf is supported at a single point `x`, then `{x}` is locally closed:
on the stratum through `x` the sheaf is locally constant, so its support there is open. -/
lemma isLocallyClosed_singleton_of_compl_stalkZeroLocus_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] {x : X}
    (hx : (stalkZeroLocus F)ᶜ = {x}) : IsLocallyClosed ({x} : Set X) := by
  obtain ⟨str, hstr⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (str.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  set h := str.immersion i
  have := hstr i
  have hpre : stalkZeroLocus (((h)^*[ModuleCat.{u + 1} Λ]).obj F) =
      h.base ⁻¹' stalkZeroLocus F :=
    Set.ext fun _ ↦ ⟨mem_stalkZeroLocus_of_upperStar h F, mem_stalkZeroLocus_upperStar h F⟩
  have hopen : IsOpen (h.base ⁻¹' {x}) := by
    rw [← hx, Set.preimage_compl, ← hpre]
    exact (isClopen_stalkZeroLocus _).isClosed.isOpen_compl
  obtain ⟨V, hV, hVpre⟩ := h.isEmbedding.isInducing.isOpen_iff.1 hopen
  rw [← str.range_immersion i] at hi
  obtain ⟨d, hd⟩ := hi
  have : ({x} : Set X) = V ∩ Set.range h.base := by
    refine Set.ext fun z ↦ ⟨?_, ?_⟩
    · rintro rfl
      refine ⟨?_, d, hd⟩
      have : d ∈ h.base ⁻¹' V := by rw [hVpre]; exact hd
      rwa [Set.mem_preimage, hd] at this
    · rintro ⟨hzV, e, rfl⟩
      have : e ∈ h.base ⁻¹' V := hzV
      rwa [hVpre] at this
  rw [this]
  exact hV.isLocallyClosed.inter h.isLocallyClosed_range

omit [IsNoetherianRing Λ] [TopologicalSpace.NoetherianSpace X] in
/-- For a point `x` with `{x}` locally closed, the open `W = X ∖ (closure {x} ∖ {x})` contains
`x` as a closed point, and `Spec κ(x) ⟶ X` factors through a closed immersion into `W`. -/
lemma exists_isClosedImmersion_fromSpecResidueField {x : X} (hx : IsLocallyClosed ({x} : Set X)) :
    ∃ (W : X.Opens) (g : Spec (X.residueField x) ⟶ W), x ∈ W ∧ IsClosedImmersion g ∧
      g ≫ W.ι = X.fromSpecResidueField x := by
  let W : X.Opens := ⟨coborder {x}, hx.isOpen_coborder⟩
  have hxW : x ∈ W := subset_coborder rfl
  have hr : Set.range (X.fromSpecResidueField x).base ⊆ Set.range W.ι.base := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact hxW
  let g := IsOpenImmersion.lift W.ι (X.fromSpecResidueField x) hr
  have hg : g ≫ W.ι = X.fromSpecResidueField x := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W, g, hxW, ?_, hg⟩
  have : IsPreimmersion (g ≫ W.ι) := by rw [hg]; infer_instance
  have : IsPreimmersion g := .of_comp g W.ι
  refine .of_isPreimmersion g ?_
  have : Set.range g.base = W.ι.base ⁻¹' closure {x} := by
    refine Set.ext fun w ↦ ⟨?_, fun hw ↦ ?_⟩
    · rintro ⟨p, rfl⟩
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hg]
      exact subset_closure (Scheme.range_fromSpecResidueField x ▸ ⟨p, rfl⟩)
    · have hw' : W.ι.base w ∈ (W : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
      have : W.ι.base w ∈ coborder {x} ∩ closure {x} := ⟨hw', hw⟩
      rw [coborder_inter_closure, Set.mem_singleton_iff] at this
      obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecResidueField x).base := by
        rw [Scheme.range_fromSpecResidueField]; rfl
      refine ⟨p, W.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hg, hp, this]
  rw [this]
  exact isClosed_closure.preimage W.ι.base.hom.continuous

/-- A sheaf supported at a point `x`, closed in an open `W`, is the extension by zero along
`W ⟶ X` of the direct image of its restriction to `x`. -/
lemma nonempty_iso_of_compl_stalkZeroLocus_subset
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {x : X}
    (hx : (stalkZeroLocus F)ᶜ ⊆ {x}) (W : X.Opens) (hxW : x ∈ W)
    (g : Spec (X.residueField x) ⟶ W) [IsClosedImmersion g]
    (hg : g ≫ W.ι = X.fromSpecResidueField x) :
    Nonempty (F ≅ (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj
      (((g)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)))) := by
  have hmem : ∀ y, y ≠ x → y ∈ stalkZeroLocus F := fun y hy ↦ by
    by_contra h; exact hy (hx h)
  -- the restriction to the closed complement of `W` vanishes
  have hij := range_closedComplement_eq_compl_range_ι W
  let S := Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement
    (disjoint_range_of_range_eq_compl _ _ hij) F
  have hS : S.ShortExact :=
    Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement F hij
  have hZ : IsZero (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F) := by
    refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun z ↦ ?_)
    refine mem_stalkZeroLocus_upperStar _ _ (hmem _ fun h ↦ ?_)
    have : W.closedComplement.base z ∈ (Set.range W.ι.base)ᶜ := hij ▸ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, h] at this
    exact this hxW
  have : IsIso S.f :=
    hS.isIso_f_iff.2 (((W.closedComplement)_*[ModuleCat.{u + 1} Λ]).map_isZero hZ)
  let e₁ := asIso S.f
  -- on `W`, the sheaf is supported on the closed point `x`
  set G := ((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F
  let W' := openComplementOfIsClosedImmersion g
  have hij' : Set.range g.base = (Set.range W'.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm
  let S' := Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) W'.ι g
    (disjoint_range_of_range_eq_compl _ _ hij') G
  have hS' : S'.ShortExact :=
    Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W'.ι g G hij'
  have hZ' : IsZero (((W'.ι)^*[ModuleCat.{u + 1} Λ]).obj G) := by
    refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun w ↦ ?_)
    refine mem_stalkZeroLocus_upperStar _ _ (mem_stalkZeroLocus_upperStar _ _ (hmem _ fun h ↦ ?_))
    have hw : W'.ι.base w ∈ (W' : Set W) := by rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    apply hw
    obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecResidueField x).base := by
      rw [Scheme.range_fromSpecResidueField]; rfl
    refine ⟨p, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg, hp, ← h]
  have : IsIso S'.g := hS'.isIso_g_iff.2
    (((W'.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero hZ')
  let e₂ := asIso S'.g
  exact ⟨e₁.symm ≪≫ ((W.ι)_!open[ModuleCat.{u + 1} Λ]).mapIso e₂⟩

end Etale

end AlgebraicGeometry
