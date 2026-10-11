/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Points of fppf coverings

A covering sieve of the fppf topology is jointly surjective, through flat morphisms locally of
finite presentation: every point of the base lies in the image of such a morphism of the sieve.
We record this for the fppf topology on `Scheme` and for its localization to `Over S`.

# Descent of properties of morphisms along fpqc coverings

A property of morphisms which is local at the target and descends along faithfully flat
quasi-compact morphisms descends along every covering sieve of the fpqc topology
(`AlgebraicGeometry.Scheme.of_isPullback_of_mem_fpqcTopology`).

Over an affine scheme, a covering sieve of the fpqc topology is refined by a finite covering
family of flat morphisms from affine schemes
(`AlgebraicGeometry.Scheme.exists_finite_affine_flat_of_mem_fpqcTopology`).

# The structure sheaf is a sheaf for subcanonical topologies

The étale topology is coarser than the fppf topology, hence subcanonical. For every
subcanonical topology on `Scheme`, for instance the fpqc, fppf and étale topologies, the global
sections functor `Γ` is a sheaf (`AlgebraicGeometry.Scheme.isSheaf_Γ`): for a ring `R`, the
presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` is represented by `Spec R`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A covering sieve of the fppf topology on a scheme `X` is jointly surjective through flat
morphisms locally of finite presentation: every point of `X` is in the image of some flat
morphism locally of finite presentation `g : Y ⟶ X` of the sieve. -/
lemma exists_flat_mem_of_mem_fppfTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ fppfTopology X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g.base := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)), inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hR₁, hR₂⟩, hle⟩ := hS
  obtain ⟨_, _, h, hx⟩ := hR₁ x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, (hR₂ hg).1, (hR₂ hg).2, hx⟩

/-- A covering sieve of the fppf topology on `Over S` is jointly surjective through morphisms
whose underlying morphism of schemes is flat and locally of finite presentation. -/
lemma exists_flat_mem_of_mem_fppfTopology_over {S : Scheme.{u}} {T : Over S} {R : Sieve T}
    (hR : R ∈ fppfTopology.over S T) (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T), R g ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      t ∈ Set.range g.left.base := by
  obtain ⟨Y, g, ⟨Z, h, k, hh, rfl⟩, hg₁, hg₂, hx⟩ :=
    exists_flat_mem_of_mem_fppfTopology ((GrothendieckTopology.mem_over_iff _ _).1 hR) t
  refine ⟨Over.mk (k ≫ Z.hom), Over.homMk k ≫ h, R.downward_closed hh _, ?_, ?_, ?_⟩
  all_goals simpa using ‹_›

section Descent

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine case of `AlgebraicGeometry.Scheme.of_isPullback_of_mem_fpqcTopology`. -/
private lemma of_isPullback_of_mem_fpqcTopology_of_isAffine {T Z : Scheme.{u}} [IsAffine T]
    {S : Sieve T} (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ := QuasiCompactCover.exists_hom 𝒰
  have : Small.{u} 𝒱.cover.I₀ := Countable.toSmall (α := 𝒱.I₀)
  let p : ∐ 𝒱.cover.X ⟶ T := Sigma.desc 𝒱.cover.f
  have hflat : Flat p := by
    have : ∀ j, Flat (𝒱.cover.f j) := 𝒱.map_prop
    infer_instance
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have : IsAffine (∐ 𝒱.cover.X) := inferInstance
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p :=
    ⟨⟨Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range, hflat⟩, inferInstance⟩
  refine MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) hp ?_
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover _)]
  intro j
  have hsq := (IsPullback.of_hasPullback (pullback.fst p f) (Sigma.ι 𝒱.cover.X j)).paste_horiz
    (IsPullback.of_hasPullback p f).flip
  have hj : Sigma.ι 𝒱.cover.X j ≫ p = 𝒱.cover.f j := Sigma.ι_desc _ _
  rw [hj] at hsq
  refine H _ _ _ ?_ hsq
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (𝒰.toPreZeroHypercover.presieve₀_f (φ.s₀ j))) _

set_option backward.isDefEq.respectTransparency.types false in
/-- **Descent of properties of morphisms along fpqc coverings.** Let `P` be a property of
morphisms of schemes which is local at the target and descends along faithfully flat
quasi-compact morphisms. If every base change of `f : Z ⟶ T` along a morphism of an fpqc
covering sieve of `T` has `P`, then `f` has `P`. -/
lemma of_isPullback_of_mem_fpqcTopology {T Z : Scheme.{u}} {S : Sieve T}
    (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover T.affineCover fun i ↦ ?_
  refine of_isPullback_of_mem_fpqcTopology_of_isAffine
    (fpqcTopology.pullback_stable (T.affineCover.f i) hS) _ fun Y W h a b hh hab ↦ ?_
  exact H _ _ _ hh (hab.paste_horiz (IsPullback.of_hasPullback f (T.affineCover.f i)))

set_option backward.isDefEq.respectTransparency.types false in
/-- **Descent of properties of morphisms along fpqc coverings**, for a covering family
`{g i : T' i ⟶ T}`: if `P` is moreover stable under base change and the base changes `b i` of
`f` along the `g i` have `P`, then `f` has `P`. -/
lemma of_isPullback_of_ofArrows_mem_fpqcTopology [P.IsStableUnderBaseChange] {T Z : Scheme.{u}}
    {ι : Type*} {T' : ι → Scheme.{u}} {g : ∀ i, T' i ⟶ T}
    (hg : Sieve.ofArrows T' g ∈ fpqcTopology T) (f : Z ⟶ T) {Z' : ι → Scheme.{u}}
    (a : ∀ i, Z' i ⟶ Z) (b : ∀ i, Z' i ⟶ T' i) (hab : ∀ i, IsPullback (a i) (b i) f (g i))
    (H : ∀ i, P (b i)) : P f := by
  refine of_isPullback_of_mem_fpqcTopology hg f fun Y W h a' b' hh hpb ↦ ?_
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hh
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_right' hpb (hab i)) (H i)

end Descent

/-- A covering sieve of the fpqc topology on a scheme `X` is jointly surjective: every point of
`X` is in the image of some morphism of the sieve. -/
lemma exists_mem_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ fpqcTopology X)
    (x : X) : ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g.base := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨-, hR, -⟩, hle⟩ := hS
  obtain ⟨_, g, h, hx⟩ := hR x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, hx⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A covering sieve of the fpqc topology on an affine scheme `V` contains a finite family of flat
morphisms from affine schemes which itself generates a covering sieve. -/
lemma exists_finite_affine_flat_of_mem_fpqcTopology {V : Scheme.{u}} [IsAffine V] {S : Sieve V}
    (hS : S ∈ fpqcTopology V) :
    ∃ (κ : Type u) (W : κ → Scheme.{u}) (f : ∀ j, W j ⟶ V), Finite κ ∧ (∀ j, IsAffine (W j)) ∧
      (∀ j, Flat (f j)) ∧ (∀ j, S (f j)) ∧ Sieve.ofArrows W f ∈ fpqcTopology V := by
  have hS' := hS
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS'
  obtain ⟨R, hR, hle⟩ := hS'
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ : ∃ (𝒱 : Scheme.AffineCover.{u} @Flat V) (φ : 𝒱.cover ⟶ 𝒰.qculift),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (φ.h₀ j) := QuasiCompactCover.exists_hom _
  have h𝒰 (k : 𝒰.qculift.I₀) : 𝒰.presieve₀ (𝒰.qculift.f k) := by
    rcases k with k | k
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  refine ⟨𝒱.cover.I₀, 𝒱.cover.X, 𝒱.cover.f, inferInstance, fun j ↦ inferInstanceAs
    (IsAffine (Spec _)), fun j ↦ 𝒱.map_prop j, fun j ↦ ?_, Cover.mem_propQCTopology 𝒱.cover⟩
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (h𝒰 _)) _

/-- Étale coverings are fppf coverings. -/
lemma etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono
    (precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)

/-- **Zariski coverings are fppf coverings.** A family of open immersions covering a scheme `T` is
an fppf covering of `T`: open immersions are flat and locally of finite presentation (on the level
of covering families this is Mathlib's `zariskiPrecoverage_le_fppfPrecoverage`), so every Zariski
covering sieve is an fppf covering sieve.

(blueprint: `lem-pc-zariski-coverings-are-fppf`) -/
lemma zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

instance : etaleTopology.{u}.Subcanonical :=
  .of_le etaleTopology_le_fppfTopology

/-- The global sections functor `Γ` is a sheaf for every subcanonical topology on `Scheme`:
for a ring `R`, the presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` is represented by `Spec R`. -/
lemma isSheaf_Γ (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf J Scheme.Γ := fun R ↦
  have := (ΓSpec.representableBy R).isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end AlgebraicGeometry.Scheme
