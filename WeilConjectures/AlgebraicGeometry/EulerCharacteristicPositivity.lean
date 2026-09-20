/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.Dimension

/-!
# Positivity of the Euler characteristic in dimension zero

Let `X` be a Noetherian scheme proper over a field `k` and let `F` be a non-zero coherent sheaf
of `𝒪_X`-modules whose support has dimension at most zero. Then

`χ(X, F) > 0`.

This is the base case of the induction proving `prop:deg-ample-positive`, the positivity of the
top self-intersection number of an ample invertible sheaf. That induction — the hyperplane
recursion of `WeilConjectures.AlgebraicGeometry.IntersectionPositivity` — runs on the
*coefficient sheaf* rather than on the scheme, so the base case is the statement above and not
the blueprint's `χ(X, 𝒪_X) > 0` for a zero-dimensional `X`.

## The proof

The sheaf `F` is taken apart by the dévissage
`AlgebraicGeometry.Scheme.Modules.exists_devissage`: a finite filtration
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_t = F` whose graded pieces are direct images `ι_* 𝓘` of non-zero ideal
sheaves on integral closed subschemes `ι : Z ⟶ X`. The Euler characteristic is additive along
the filtration, so it is enough to see that each graded piece has positive Euler characteristic
and that there is at least one of them, the latter because `F` is non-zero.

For a graded piece `P ≅ ι_* 𝓘` the argument is that `Z` is a single point. Indeed `𝓘` is
non-zero, so its stalk at the generic point `η` of `Z` is non-zero — this is
`AlgebraicGeometry.Scheme.IdealSheafData.genericRank_toModules` — and the stalk of a direct
image along a topological embedding at the image of a point is the stalk upstairs, so
`ι η ∈ Supp P`. The support of a coherent sheaf is closed and `Z` is the closure of `η`, so the
whole of `ι(Z)` lies in `Supp P`, whose dimension is at most zero; as `ι` is an embedding, `Z`
itself has dimension at most zero, and an irreducible space of dimension at most zero in which
the closure of a non-generic point would be a proper closed subset has no non-generic point.

A one-point scheme is affine, and an ideal sheaf on it whose zero locus misses the only point is
the unit ideal sheaf, so `𝓘 = 𝒪_Z`. The Euler characteristic is unchanged by the direct image
along the finite morphism `ι` (`eulerChar_pushforward`) and is positive for the structure sheaf
of a non-empty affine scheme proper over `k` (`eulerChar_unit_pos`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.eulerChar_pos_of_supportDim_le_zero`: the Euler
  characteristic of a non-zero coherent sheaf whose support has dimension at most zero, on a
  Noetherian scheme proper over a field, is positive.
* `AlgebraicGeometry.Scheme.Modules.eulerChar_pos_of_isPushforwardIdealSheaf`: the same for a
  graded piece of the dévissage, which is the step the induction rests on.

## Blueprint

This is the base case of the proof of `prop:deg-ample-positive` of
`curve_estimates/28_degree_of_the_isogeny.tex`; it is not a node of the blueprint graph of its
own. It rests on the dévissage `lem:deg-devissage`, which is stated and not proved.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The direct image of a sheaf of modules on the empty scheme vanishes**: every open of the
target has empty preimage, so every module of sections is trivial. -/
theorem isZero_pushforward_of_isEmpty {Y : Scheme.{u}} (f : Y ⟶ X) [IsEmpty Y] (N : Y.Modules) :
    IsZero ((pushforward f).obj N) := by
  have hsub : ∀ U : X.Opens, Subsingleton Γ((pushforward f).obj N, U) := fun U ↦ by
    rw [show Γ((pushforward f).obj N, U) = Γ(N, f ⁻¹ᵁ U) from pushforward_obj_obj f N U,
      show f ⁻¹ᵁ U = ⊥ from TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext _ _ fun U ↦ ?_
  rw [Hom.id_app, Hom.zero_app, ← IsZero.iff_id_eq_zero, AddCommGrpCat.isZero_iff_subsingleton]
  exact hsub U

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **A graded piece of the dévissage supported in dimension zero has positive Euler
characteristic.**

Such a piece is `ι_* 𝓘` for `ι : Z ⟶ X` a closed immersion of an integral scheme and `𝓘 ≠ 0`
an ideal sheaf on `Z`. The hypothesis on the dimension of the support forces `Z` to be a single
point, hence affine, and then `𝓘` to be the unit ideal sheaf, so that the piece is `ι_* 𝒪_Z`;
its Euler characteristic is that of `𝒪_Z`, which is `dim_k Γ(Z, 𝒪_Z) > 0`. -/
theorem eulerChar_pos_of_isPushforwardIdealSheaf (P : X.Modules) [P.IsCoherent]
    (hP : IsPushforwardIdealSheaf P) (hd : P.supportDim ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    0 < eulerChar k P := by
  obtain ⟨Z, ι, hι, hZ, I, hI, ⟨e⟩⟩ := hP
  have hι' : IsClosedImmersion ι := hι
  have hZ' : IsIntegral Z := hZ
  set η := genericPoint Z
  -- the stalk of the ideal sheaf at the generic point is non-trivial
  have hnt : Nontrivial (I.toModules.presheaf.stalk η) := by
    have h1 : genericRank I.toModules = 1 := Scheme.IdealSheafData.genericRank_toModules hI
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have : Subsingleton (I.toModules.presheaf.stalk η) := hs
    rw [genericRank, Module.finrank_zero_of_subsingleton] at h1
    exact zero_ne_one h1
  -- hence so is the stalk of the direct image at the image of the generic point
  have hind : Topology.IsInducing ι.base := ι.isClosedEmbedding.isInducing
  have hiso : IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} ι.base I.toModules.presheaf η) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{u} hind _ _
  have hsurj : Function.Surjective
      (TopCat.Presheaf.stalkPushforward Ab.{u} ι.base I.toModules.presheaf η) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  have hmem : ι.base η ∈ P.support := by
    rw [support_congr e]
    obtain ⟨a, b, hab⟩ := hnt
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    exact (mem_support_iff _ _).2 ⟨a', b', fun h ↦ hab (congrArg _ h)⟩
  -- the image of `ι` is the closure of that point, hence contained in the support of `P`
  have hrange : Set.range ι.base ⊆ P.support := by
    have h1 : Set.range ι.base = closure {ι.base η} := by
      rw [← Set.image_univ, ← (genericPoint_spec Z).def, ← Set.image_singleton,
        ι.isClosedEmbedding.closure_image_eq]
    rw [h1]
    exact (isClosed_support P).closure_subset_iff.2 (by simpa using hmem)
  -- so `Z` has dimension at most zero
  have hdimZ : topologicalKrullDim Z ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    refine le_trans (Topology.IsInducing.topologicalKrullDim_le
      (f := fun z : Z ↦ (⟨ι.base z, hrange ⟨z, rfl⟩⟩ : P.support)) ?_) hd
    exact Topology.IsInducing.of_comp (hind.continuous.subtype_mk _) continuous_subtype_val hind
  -- an irreducible space of dimension at most zero has a single point
  have hpt : ∀ z : Z, z = η := by
    intro z
    by_contra hne
    have hcl : closure ({z} : Set Z) ≠ Set.univ := fun h ↦
      hne (IsGenericPoint.eq h (genericPoint_spec Z))
    have hle := (topologicalKrullDim_add_one_le isClosed_closure hcl).trans hdimZ
    have hbot : topologicalKrullDim (closure ({z} : Set Z)) = ⊥ :=
      ENat.WithBot.lt_natCast_zero_iff.1 (ENat.WithBot.add_one_le_natCast_iff.mp hle)
    exact (topologicalKrullDim_eq_bot_iff.1 hbot).elim ⟨z, subset_closure rfl⟩
  -- a one-point scheme is affine
  obtain ⟨V, hV, hηV⟩ : ∃ V : Z.Opens, IsAffineOpen V ∧ η ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
    exact ⟨V, hV, hηV⟩
  have hVtop : V = ⊤ := by
    ext z
    simpa using hpt z ▸ hηV
  have hZaff : IsAffine Z := (IsAffine.iff_of_isIso Z.topIso.hom).1 (hVtop ▸ hV)
  -- a non-zero ideal sheaf on a one-point integral scheme is the unit ideal sheaf
  have hItop : I = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    obtain ⟨U, hU⟩ : ∃ U : Z.affineOpens, I.ideal U ≠ ⊥ :=
      Function.ne_iff.1 fun hc ↦ hI (Scheme.IdealSheafData.ext hc)
    obtain ⟨a, haI, ha0⟩ := (Submodule.ne_bot_iff _).1 hU
    have hba : (Z.basicOpen a : Set Z).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact ha0 ((basicOpen_eq_bot_iff a).1 (TopologicalSpace.Opens.ext (by simpa using h)))
    have hηba : η ∈ Z.basicOpen a :=
      ((genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen).mpr (by simpa using hba)
    have hnot : η ∉ I.support := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (Z.basicOpen_le a hηba),
        Scheme.mem_zeroLocus_iff]
      exact fun h ↦ h a haI hηba
    refine TopologicalSpace.Closeds.ext (Set.eq_empty_iff_forall_notMem.2 fun z hz ↦ ?_)
    exact hnot (hpt z ▸ hz)
  subst hItop
  -- the closed subscheme cut out by the unit ideal sheaf is empty, so the ideal sheaf is `𝒪_Z`
  have eI : (⊤ : Z.IdealSheafData).toModules ≅ Z.structureModules :=
    kernelIsoOfEq ((isZero_pushforward_of_isEmpty (⊤ : Z.IdealSheafData).subschemeι
      (⊤ : Z.IdealSheafData).subscheme.structureModules).eq_zero_of_tgt _) ≪≫ kernelZeroIsoSource
  -- and the Euler characteristic of `𝒪_Z` on the non-empty affine scheme `Z` is positive
  let hover : Z.Over (Spec (.of k)) := ⟨ι ≫ X ↘ Spec (.of k)⟩
  have hιover : ι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hprop : IsProper (Z ↘ Spec (.of k)) := by
    change IsProper (ι ≫ X ↘ Spec (.of k))
    infer_instance
  have hne : Nonempty Z := ⟨η⟩
  have h1 : eulerChar k P = eulerChar k ((pushforward ι).obj Z.structureModules) :=
    (eulerChar_congr k e).trans (eulerChar_congr k ((pushforward ι).mapIso eI))
  rw [h1, eulerChar_pushforward k ι Z.structureModules]
  exact eulerChar_unit_pos k

/-- **The Euler characteristic of a non-zero coherent sheaf whose support has dimension at most
zero, on a Noetherian scheme proper over a field, is positive.**

This is the base case of the induction proving `prop:deg-ample-positive`. The proof is the
dévissage `AlgebraicGeometry.Scheme.Modules.exists_devissage` together with the additivity of
the Euler characteristic along the resulting filtration: every graded piece has positive Euler
characteristic by
`AlgebraicGeometry.Scheme.Modules.eulerChar_pos_of_isPushforwardIdealSheaf`, and there is at
least one piece because `F` is non-zero. -/
theorem eulerChar_pos_of_supportDim_le_zero [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : ¬ IsZero F) (hd : F.supportDim ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    0 < eulerChar k F := by
  obtain ⟨t, G, φ, hG0, ⟨eF⟩, hstep⟩ := exists_devissage F
  have hmono : ∀ j : Fin t, Mono (φ j) := fun j ↦ (hstep j).2.1
  -- the filtration is increasing, so every one of its terms is supported inside `Supp F`
  have hsupp : ∀ j : Fin (t + 1), (G j).support ⊆ F.support := by
    have h : ∀ j : Fin (t + 1), (G j).support ⊆ (G (Fin.last t)).support := by
      refine Fin.reverseInduction (fun _ hx ↦ hx) fun i ih ↦ ?_
      have := hmono i
      exact (support_subset_of_mono (φ i)).trans ih
    exact fun j ↦ (h j).trans (support_congr eF).le
  have hcoh0 : (G 0).IsCoherent :=
    (SheafOfModules.isCoherent X.ringCatSheaf).prop_of_iso
      ((isZero_cokernel_of_epi (𝟙 X.structureModules)).iso hG0)
      (isCoherent_cokernel (𝟙 X.structureModules) inferInstance inferInstance)
  -- the Euler characteristic increases strictly along the filtration
  have key : ∀ j : Fin (t + 1), (G j).IsCoherent ∧ 0 ≤ eulerChar k (G j) ∧
      ((j : ℕ) ≠ 0 → 0 < eulerChar k (G j)) := by
    refine Fin.induction ⟨hcoh0, ?_, ?_⟩ ?_
    · rw [eulerChar_eq_zero_of_isZero k hG0]
    · simp
    · rintro j ⟨hcoh, hle, -⟩
      have hcoh1 : (G j.castSucc).IsCoherent := hcoh
      have hcoh2 : (G j.succ).IsCoherent := (hstep j).1
      have hmj := hmono j
      have hcohc : (cokernel (φ j)).IsCoherent :=
        isCoherent_cokernel (φ j) ((SheafOfModules.isCoherent_iff (G j.castSucc)).mp hcoh1).1
          hcoh2
      have hw : φ j ≫ cokernel.π (φ j) = 0 := cokernel.condition (φ j)
      have hSE : (ShortComplex.mk (φ j) (cokernel.π (φ j)) hw).ShortExact :=
        { exact := ShortComplex.exact_cokernel (φ j) }
      have h₁ : (ShortComplex.mk (φ j) (cokernel.π (φ j)) hw).X₁.IsCoherent := hcoh1
      have h₂ : (ShortComplex.mk (φ j) (cokernel.π (φ j)) hw).X₂.IsCoherent := hcoh2
      have h₃ : (ShortComplex.mk (φ j) (cokernel.π (φ j)) hw).X₃.IsCoherent := hcohc
      have hadd := eulerChar_add_eulerChar k hSE
      dsimp only at hadd
      have hp : 0 < eulerChar k (cokernel (φ j)) := by
        refine eulerChar_pos_of_isPushforwardIdealSheaf k _ (hstep j).2.2
          ((supportDim_le_of_support_subset ?_).trans hd)
        exact (support_cokernel_subset (φ j)).trans (hsupp j.succ)
      exact ⟨hcoh2, by omega, fun _ ↦ by omega⟩
  -- and the filtration is non-trivial, because `F` is non-zero
  have ht : t ≠ 0 := by
    rintro rfl
    exact hF (hG0.of_iso ((eqToIso (congrArg G (Subsingleton.elim (0 : Fin 1) _))).trans eF).symm)
  obtain ⟨-, -, hlast⟩ := key (Fin.last t)
  rw [← eulerChar_congr k eF]
  exact hlast (by simpa using ht)

end AlgebraicGeometry.Scheme.Modules
