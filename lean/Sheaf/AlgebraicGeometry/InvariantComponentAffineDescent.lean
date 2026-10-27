/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat

/-!
# Affine descent of an invariant section component

Source: literature/stacks-project/more-morphisms.tex, Tag 057I,
`lemma-descent-connected-fibres`, affine shrinking, descent and quasi-compactness paragraphs
(blueprint: lem-trf-invariant-component-affine-descent).

The auxiliary maps are the canonical fibre-product projections and restriction map used
in that argument. No geometric connectedness of the distinguished fibre is required once
its invariant neighbourhood is supplied.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

namespace InvariantComponentAffineDescent

/-- The structure map of the double overlap of a multisection.
Source: Stacks, Tag 057I, affine shrinking paragraph
(blueprint: lem-trf-invariant-component-affine-descent). -/
noncomputable def overlapBase {Z B : Scheme.{u}} (p : Z ⟶ B) : pullback p p ⟶ B :=
  pullback.fst p p ≫ p

/-- The map `1_X × pr₀` from the base change to the double overlap.
Source: Stacks, Tag 057I, comparison of the two section components
(blueprint: lem-trf-invariant-component-affine-descent). -/
noncomputable def overlapLeft {X Z B : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B) :
    pullback f (overlapBase p) ⟶ pullback f p :=
  pullback.map f (overlapBase p) f p (𝟙 X) (pullback.fst p p) (𝟙 B)
    (Category.comp_id f |>.trans (Category.id_comp f).symm)
    (Category.comp_id (overlapBase p))

/-- The map `1_X × pr₁` from the base change to the double overlap.
Source: Stacks, Tag 057I, comparison of the two section components
(blueprint: lem-trf-invariant-component-affine-descent). -/
noncomputable def overlapRight {X Z B : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B) :
    pullback f (overlapBase p) ⟶ pullback f p :=
  pullback.map f (overlapBase p) f p (𝟙 X) (pullback.snd p p) (𝟙 B)
    (Category.comp_id f |>.trans (Category.id_comp f).symm)
    ((Category.comp_id (overlapBase p)).trans pullback.condition)

/-- The canonical map `X_V ×_V Z_V → X ×_B Z` defining the restricted component open.
Source: Stacks, Tag 057I, replacement of the base by its affine open neighbourhood
(blueprint: lem-trf-invariant-component-affine-descent). -/
noncomputable def restrictionMap {X Z B : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (V : B.Opens) :
    pullback (pullback.snd f V.ι) (pullback.snd p V.ι) ⟶ pullback f p :=
  pullback.map (pullback.snd f V.ι) (pullback.snd p V.ι) f p
    (pullback.fst f V.ι) (pullback.fst p V.ι) V.ι
    pullback.condition.symm pullback.condition.symm

-- Shrink simultaneously into the image of p and away from q(R ∖ W).
private theorem exists_affine_shrinking {Z B : Scheme.{u}} (p : Z ⟶ B)
    [p.IsFiniteLocallyFree] (b₀ : B) (hb₀ : Nonempty (p.fiber b₀))
    (W : (pullback p p).Opens) (hW : (overlapBase p) ⁻¹' {b₀} ⊆ W.carrier) :
    ∃ V : B.Opens, b₀ ∈ V ∧ IsAffineOpen V ∧
      (overlapBase p) ⁻¹' (V : Set B) ⊆ W.carrier ∧ (V : Set B) ⊆ Set.range p := by
  have : IsFinite (overlapBase p) := inferInstanceAs
    (IsFinite (pullback.fst p p ≫ p))
  let D : Set B := overlapBase p '' (W.carrier)ᶜ
  have hD : IsClosed D := (overlapBase p).isClosedMap _ W.isOpen.isClosed_compl
  have hbD : b₀ ∉ D := by
    rintro ⟨z, hz, he⟩
    exact hz (hW he)
  have hbr : b₀ ∈ Set.range p := by
    obtain ⟨z⟩ := hb₀
    exact ⟨p.fiberι b₀ z, (p.fiberHomeo b₀ z).property⟩
  let O : B.Opens := ⟨Set.range p ∩ Dᶜ, p.isOpenMap.isOpen_range.inter hD.isOpen_compl⟩
  obtain ⟨V, hVa, hbV, hVO⟩ := exists_isAffineOpen_mem_and_subset (U := O) ⟨hbr, hbD⟩
  refine ⟨V, hbV, hVa, ?_, fun b hb ↦ (hVO hb).1⟩
  intro z hz
  by_contra hn
  exact (hVO hz).2 ⟨z, hn, rfl⟩

-- The two descriptions of the restriction are related by pullback pasting.
private theorem restriction_isPullback {X Z B : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (V : B.Opens) :
    IsPullback (restrictionMap f p V)
      (pullback.snd (pullback.snd f V.ι) (pullback.snd p V.ι))
      (pullback.snd f p) (pullback.fst p V.ι) := by
  have h := (IsPullback.of_hasPullback (pullback.snd f V.ι)
    (pullback.snd p V.ι)).paste_horiz (IsPullback.of_hasPullback f V.ι)
  have h' : IsPullback (restrictionMap f p V ≫ pullback.fst f p)
      (pullback.snd (pullback.snd f V.ι) (pullback.snd p V.ι))
      f (pullback.fst p V.ι ≫ p) := by
    simpa only [restrictionMap, pullback.map, pullback.lift_fst, pullback.condition] using h
  exact h'.of_right (by simp [restrictionMap]) (IsPullback.of_hasPullback f p)

-- Base change the component locus over Z, where the restricted base is affine.
private theorem compact_restricted_component {X Z B : Scheme.{u}} (f : X ⟶ B)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (p : Z ⟶ B) (σ : Z ⟶ X) (hσ : σ ≫ f = p) (C : (pullback f p).Opens)
    (hC : C.carrier = {y | y ∈ connectedComponentIn
      ((pullback.snd f p) ⁻¹' {(pullback.snd f p) y})
      ((pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm))
        ((pullback.snd f p) y))})
    (V : B.Opens) [IsAffine (pullback p V.ι)] :
    IsCompact ((restrictionMap f p V) ⁻¹' C.carrier) := by
  let g : pullback f p ⟶ Z := pullback.snd f p
  let r : pullback p V.ι ⟶ Z := pullback.fst p V.ι
  let s := pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm)
  have hs : s ≫ g = 𝟙 Z := by simp [s, g]
  have : CompactSpace (pullback (C := Scheme.{u}) g r) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd g r)
  have : QuasiSeparatedSpace (pullback (C := Scheme.{u}) g r) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd g r)
  have hc : IsCompact (pullback.fst g r ⁻¹' C.carrier) := by
    rw [hC, preimage_setOf_mem_connectedComponentIn_preimage_singleton g s hs r]
    exact isCompact_setOf_mem_connectedComponentIn_preimage_singleton
      (pullback.snd g r) (pullback.lift (r ≫ s) (𝟙 _) (by simp [hs])) (by simp)
  let e := (restriction_isPullback f p V).isoPullback
  have he : e.hom ≫ pullback.fst g r = restrictionMap f p V :=
    (restriction_isPullback f p V).isoPullback_hom_fst
  have hc' := e.hom.isCompact_preimage (U := pullback.fst g r ⁻¹ᵁ C) hc
  convert hc' using 1
  ext x
  change restrictionMap f p V x ∈ C ↔ pullback.fst g r (e.hom x) ∈ C
  rw [← Scheme.Hom.comp_apply, he]

-- Compare the two restricted projections by a universal lift to the original overlap.
private theorem restricted_invariance {X Z B : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (C : (pullback f p).Opens) (W : (pullback p p).Opens)
    (hInv : ((pullback.snd f (overlapBase p)) ⁻¹ᵁ W) ⊓
        ((overlapLeft f p) ⁻¹ᵁ C) =
      ((pullback.snd f (overlapBase p)) ⁻¹ᵁ W) ⊓ ((overlapRight f p) ⁻¹ᵁ C))
    (V : B.Opens) (hVW : (overlapBase p) ⁻¹' (V : Set B) ⊆ W.carrier) :
    pullback.fst
        (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι))
        (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)) ⁻¹ᵁ
        ((restrictionMap f p V) ⁻¹ᵁ C) =
      pullback.snd
        (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι))
        (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)) ⁻¹ᵁ
        ((restrictionMap f p V) ⁻¹ᵁ C) := by
  let fV := pullback.snd f V.ι
  let pV := pullback.snd p V.ι
  let rX := pullback.fst f V.ι
  let rZ := pullback.fst p V.ι
  let π := pullback.fst fV pV
  let ρ := pullback.snd fV pV
  let l := pullback.fst π π
  let r := pullback.snd π π
  have hπ : π ≫ fV = ρ ≫ pV := pullback.condition
  have hlr : l ≫ π = r ≫ π := pullback.condition
  have hrZ : rZ ≫ p = pV ≫ V.ι := pullback.condition
  have hrX : rX ≫ f = fV ≫ V.ι := pullback.condition
  have hρ : l ≫ ρ ≫ pV ≫ V.ι = r ≫ ρ ≫ pV ≫ V.ι := by
    calc
      _ = l ≫ π ≫ fV ≫ V.ι := by
        simpa only [Category.assoc] using
          (congrArg (fun k ↦ l ≫ k ≫ V.ι) hπ).symm
      _ = r ≫ π ≫ fV ≫ V.ι := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ fV ≫ V.ι) hlr
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k ↦ r ≫ k ≫ V.ι) hπ
  have hd : (l ≫ ρ ≫ rZ) ≫ p = (r ≫ ρ ≫ rZ) ≫ p := by
    simpa only [Category.assoc, hrZ] using hρ
  let d := pullback.lift (l ≫ ρ ≫ rZ) (r ≫ ρ ≫ rZ) hd
  have he : (l ≫ π ≫ rX) ≫ f = d ≫ overlapBase p := by
    calc
      _ = l ≫ π ≫ fV ≫ V.ι := by simp only [Category.assoc, hrX]
      _ = l ≫ ρ ≫ pV ≫ V.ι := by
        simpa only [Category.assoc] using congrArg (fun k ↦ l ≫ k ≫ V.ι) hπ
      _ = _ := by simp [d, overlapBase, Category.assoc, hrZ]
  let e := pullback.lift (l ≫ π ≫ rX) d he
  have h₀ : e ≫ overlapLeft f p = l ≫ restrictionMap f p V := by
    apply pullback.hom_ext <;>
      simp [e, d, overlapLeft, restrictionMap, π, ρ, rX, rZ, fV, pV, Category.assoc]
  have h₁ : e ≫ overlapRight f p = r ≫ restrictionMap f p V := by
    apply pullback.hom_ext
    · calc
        _ = l ≫ π ≫ rX := by simp [e, overlapRight, Category.assoc]
        _ = r ≫ π ≫ rX := by
          simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ rX) hlr
        _ = _ := by simp [restrictionMap, π, rX, fV, pV, Category.assoc]
    · simp [e, d, overlapRight, restrictionMap, ρ, rZ, fV, pV, Category.assoc]
  have hB : e ≫ pullback.snd f (overlapBase p) ≫ overlapBase p =
      l ≫ ρ ≫ pV ≫ V.ι := by
    simp [e, d, overlapBase, Category.assoc, hrZ]
  apply SetLike.ext
  intro x
  have hw : pullback.snd f (overlapBase p) (e x) ∈ W := by
    apply hVW
    change overlapBase p (pullback.snd f (overlapBase p) (e x)) ∈ V
    have hx := congrArg (fun k ↦ k x) hB
    simp only [Scheme.Hom.comp_apply] at hx
    rw [hx]
    exact (pV (ρ (l x))).property
  have hx₀ := congrArg (fun k ↦ k x) h₀
  have hx₁ := congrArg (fun k ↦ k x) h₁
  simp only [Scheme.Hom.comp_apply] at hx₀ hx₁
  have hi : (pullback.snd f (overlapBase p) (e x) ∈ W ∧
      overlapLeft f p (e x) ∈ C) ↔
      (pullback.snd f (overlapBase p) (e x) ∈ W ∧ overlapRight f p (e x) ∈ C) :=
    SetLike.ext_iff.mp hInv (e x)
  change restrictionMap f p V (l x) ∈ C ↔ restrictionMap f p V (r x) ∈ C
  simpa only [hw, true_and, hx₀, hx₁] using hi

end InvariantComponentAffineDescent

open InvariantComponentAffineDescent

/-- An invariant section component descends to a quasi-compact open after affine shrinking.

Source: literature/stacks-project/more-morphisms.tex, Tag 057I,
`lemma-descent-connected-fibres`, affine shrinking, descent and final quasi-compactness
paragraphs (blueprint: lem-trf-invariant-component-affine-descent).

Proof plan:
1. Finite locally free implies finite, flat and locally of finite presentation. The map
   `q = overlapBase p` is finite by base change and composition
   (lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-finite-composition).
   Thus `q(R \ W)` is closed (lem-weil-pbc-finite-closed-map-finite-fibres) and avoids `b₀`.
   The image of `p` is open (lem-weil-pbc-flat-lfp-open) and contains `b₀` by the nonempty
   fibre. Choose an affine neighbourhood `V` in the complement of that closed set and
   in this image (lem-weil-pbc-affine-opens-basis). Then `q⁻¹V ⊆ W`.
2. Base change preserves finiteness, flatness and local finite presentation
   (lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence). The restricted `p` is surjective and its source
   is affine, since it is finite over affine `V`. The inverse image of any affine open
   is affine and surjects onto it, verifying the singleton fpqc covering condition
   (def-weil-pbc-fpqc-covering). Its base change `π` is an fpqc covering too
   (lem-galois-fpqc-covering-base-change).
3. Identify the double overlap of `π` with the restriction of `X ×_B (Z ×_B Z)`
   (def-pc-base-change, def-pc-fibre-product). The equality on `h⁻¹W` now gives equal
   pullbacks of `C_V` under its two projections. Apply
   lem-weil-pbc-open-subscheme-fpqc-descent to obtain `U`, unique for this `V` and `C_V`.
4. The projection to `Z_V` is flat, finitely presented and qcqs by base change.
   Its fibres remain geometrically reduced, since further field extension is still a
   field extension of the original residue field (def-pc-geometrically-irreducible).
   Restricting the section does not change its fibre components. The base `Z_V` is
   affine, so lem-trf-section-component-quasi-compact gives quasi-compactness of `C_V`.
5. Surjectivity of `π` and `π⁻¹U = C_V` give `π(C_V) = U`. Pull back an open cover of
   `U`, extract a finite subcover of `C_V`, and use surjectivity to cover `U`. Thus `U`
   is quasi-compact. Geometric connectedness of `X_{b₀}` was never used.
-/
theorem exists_affine_open_invariant_component_descent
    {X Z B : Scheme.{u}} (f : X ⟶ B) [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] [GeometricallyReduced f]
    (p : Z ⟶ B) [p.IsFiniteLocallyFree] (σ : Z ⟶ X) (hσ : σ ≫ f = p)
    (C : (pullback f p).Opens)
    (hC : C.carrier = {y | y ∈ connectedComponentIn
      ((pullback.snd f p) ⁻¹' {(pullback.snd f p) y})
      ((pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm))
        ((pullback.snd f p) y))})
    (b₀ : B) (hb₀ : Nonempty (p.fiber b₀)) (W : (pullback p p).Opens)
    (hW : (overlapBase p) ⁻¹' {b₀} ⊆ W.carrier)
    (hInv : ((pullback.snd f (overlapBase p)) ⁻¹ᵁ W) ⊓
        ((overlapLeft f p) ⁻¹ᵁ C) =
      ((pullback.snd f (overlapBase p)) ⁻¹ᵁ W) ⊓
        ((overlapRight f p) ⁻¹ᵁ C)) :
    ∃ V : B.Opens, b₀ ∈ V ∧ IsAffineOpen V ∧
      (overlapBase p) ⁻¹' (V : Set B) ⊆ W.carrier ∧
      (pullback.snd p V.ι).IsFiniteLocallyFree ∧ Surjective (pullback.snd p V.ι) ∧
      IsAffine (pullback p V.ι) ∧
      Presieve.singleton (pullback.snd p V.ι) ∈ Scheme.fpqcPrecoverage V.toScheme ∧
      Presieve.singleton (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)) ∈
        Scheme.fpqcPrecoverage (pullback f V.ι) ∧
      IsCompact ((restrictionMap f p V) ⁻¹' C.carrier) ∧
      ∃ U : (pullback f V.ι).Opens, IsCompact U.carrier ∧
        (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)) ⁻¹ᵁ U =
          (restrictionMap f p V) ⁻¹ᵁ C ∧
        ∀ U' : (pullback f V.ι).Opens,
          (pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)) ⁻¹ᵁ U' =
            (restrictionMap f p V) ⁻¹ᵁ C → U' = U := by
  obtain ⟨V, hbV, hVa, hVW, hVr⟩ := exists_affine_shrinking p b₀ hb₀ W hW
  have : IsAffine V.toScheme := hVa
  have hpV : (pullback.snd p V.ι).IsFiniteLocallyFree := {}
  have hpVs : Surjective (pullback.snd p V.ι) := by
    constructor
    intro v
    have hv : v ∈ Set.range (pullback.snd p V.ι) := by
      rw [Scheme.Pullback.range_snd]
      exact hVr v.property
    exact hv
  have hZa : IsAffine (pullback p V.ι) :=
    isAffine_of_isAffineHom (pullback.snd p V.ι)
  let π := pullback.fst (pullback.snd f V.ι) (pullback.snd p V.ι)
  have hpqc := (pullback.snd p V.ι).singleton_mem_fpqcPrecoverage
  have hπqc := π.singleton_mem_fpqcPrecoverage
  have hcompact := compact_restricted_component f p σ hσ C hC V
  have hinv := restricted_invariance f p C W hInv V hVW
  have hcover : Presieve.ofArrows (fun _ : PUnit.{1} ↦ _)
      (fun _ : PUnit.{1} ↦ π) ∈ Scheme.fpqcPrecoverage (pullback f V.ι) := by
    simpa only [Presieve.ofArrows_pUnit.{0}] using hπqc
  obtain ⟨U, hU, huniq⟩ := openSubscheme_existsUnique_of_fpqc
    (fun _ : PUnit.{1} ↦ π) hcover (fun _ ↦ restrictionMap f p V ⁻¹ᵁ C)
    (fun _ _ ↦ hinv)
  have hUeq : π ⁻¹ᵁ U = restrictionMap f p V ⁻¹ᵁ C := hU PUnit.unit
  have himage : π '' ((restrictionMap f p V) ⁻¹' C.carrier) = U.carrier := by
    rw [← show π ⁻¹' U.carrier = (restrictionMap f p V) ⁻¹' C.carrier from
      congrArg (fun O ↦ O.carrier) hUeq]
    exact Set.image_preimage_eq _ π.surjective
  refine ⟨V, hbV, hVa, hVW, hpV, hpVs, hZa, hpqc, hπqc, hcompact,
    U, ?_, hUeq, ?_⟩
  · rw [← himage]
    exact hcompact.image π.continuous
  · intro U' hU'
    exact huniq U' (fun _ ↦ hU')

end AlgebraicGeometry
