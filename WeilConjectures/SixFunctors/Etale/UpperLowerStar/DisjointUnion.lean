/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# Sections over disjoint unions on the small étale site

The sections of an étale sheaf over an étale `X`-scheme `P` that is the disjoint union of open
subschemes `Uₛ` are the product of the sections over the `Uₛ`
(`AlgebraicGeometry.Scheme.Etale.existsUnique_of_pairwise_disjoint`). This generalises the
two-piece splitting `AlgebraicGeometry.Scheme.Etale.existsUnique_of_isCompl`. It is the first
step towards computing the pushforward along a trivial finite étale cover `∐ₛ U ⟶ U`, an
input to the constructibility of extensions by zero along étale maps [Stacks 03SA].
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] {X : Scheme.{u}}
  (G : Sheaf X.smallEtaleTopology A) {P : X.Etale} {ι : Type u} (U : ι → X.Etale)
  (i : ∀ s, U s ⟶ P) [∀ s, IsOpenImmersion (i s).left]

/-- **Sections over a disjoint union.** The sections of a sheaf on the small étale site over `P`
are determined by their restrictions to a family of open subschemes of `P` with pairwise disjoint
images covering `P`, and any family of sections over them glues. -/
lemma Etale.existsUnique_of_pairwise_disjoint
    (hdisj : Pairwise fun s t ↦ Disjoint (Set.range (i s).left.base) (Set.range (i t).left.base))
    (hcov : ⋃ s, Set.range (i s).left.base = Set.univ) {a : A}
    (x : ∀ s, a ⟶ G.obj.obj (op (U s))) :
    ∃! σ : a ⟶ G.obj.obj (op P), ∀ s, σ ≫ G.obj.map (i s).op = x s := by
  have hcov' : Sieve.ofArrows U i ∈ X.smallEtaleTopology P := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact hcov
  have hsh := (G.property a).isSheafFor (Presieve.ofArrows U i) hcov'
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hmono (s : ι) : Mono (i s) := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono (i s).left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  have hempty {T : X.Etale} {s t : ι} (hst : s ≠ t) (g₁ : T ⟶ U s) (g₂ : T ⟶ U t)
      (hg : g₁ ≫ i s = g₂ ≫ i t) : IsEmpty T.left := by
    refine ⟨fun z ↦ ?_⟩
    have h₁ : (i s).left (g₁.left z) = (i t).left (g₂.left z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun g ↦ g.left z) hg
    have h₂ : (i s).left (g₁.left z) ∈ Set.range (i t).left.base := ⟨_, h₁.symm⟩
    exact Set.disjoint_iff.1 (hdisj hst) ⟨⟨_, rfl⟩, h₂⟩
  obtain ⟨σ, hσ, hσu⟩ := hsh (fun s ↦ x s) (by
    intro s t T g₁ g₂ hg
    by_cases hst : s = t
    · subst hst
      obtain rfl : g₁ = g₂ := (cancel_mono (i s)).1 hg
      rfl
    · have := hempty hst g₁ g₂ hg
      exact (Etale.isTerminalSectionsOfIsEmpty G T).hom_ext _ _)
  exact ⟨σ, hσ, fun σ' hσ' ↦ hσu σ' hσ'⟩

section TrivialCover

variable {U W : Scheme.{u}} {S : Type u} (w : W ⟶ U)

/-- The fold map `∐ₛ U ⟶ U` of a trivial cover. -/
noncomputable abbrev trivialCoverFold (U : Scheme.{u}) (S : Type u) : (∐ fun _ : S ↦ U) ⟶ U :=
  Sigma.desc fun _ ↦ 𝟙 U

/-- The `s`-th section `W ⟶ W ×_U ∐ₛ U` of the base change of a trivial cover. -/
noncomputable def trivialCoverSection (s : S) : W ⟶ pullback w (trivialCoverFold U S) :=
  pullback.lift (𝟙 W) (w ≫ Sigma.ι (fun _ : S ↦ U) s) (by simp)

lemma isPullback_trivialCoverSection (s : S) :
    IsPullback (trivialCoverSection w s) w (pullback.snd w (trivialCoverFold U S))
      (Sigma.ι (fun _ : S ↦ U) s) := by
  refine IsPullback.of_right ?_ (by simp [trivialCoverSection])
    (IsPullback.of_hasPullback w (trivialCoverFold U S))
  have h₁ : trivialCoverSection w s ≫ pullback.fst w (trivialCoverFold U S) = 𝟙 W := by
    simp [trivialCoverSection]
  have h₂ : Sigma.ι (fun _ : S ↦ U) s ≫ trivialCoverFold U S = 𝟙 U := by simp
  rw [h₁, h₂]
  exact IsPullback.id_horiz w

instance (s : S) : IsOpenImmersion (trivialCoverSection w s) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_trivialCoverSection w s).flip
    inferInstance

lemma range_trivialCoverSection (s : S) :
    Set.range (trivialCoverSection w s) =
      pullback.snd w (trivialCoverFold U S) ⁻¹' Set.range (Sigma.ι (fun _ : S ↦ U) s) := by
  have h := isPullback_trivialCoverSection w s
  rw [← Pullback.range_fst]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

lemma pairwise_disjoint_range_trivialCoverSection :
    Pairwise fun s t : S ↦ Disjoint (Set.range (trivialCoverSection w s))
      (Set.range (trivialCoverSection w t)) := fun s t hst ↦ by
  change Disjoint (Set.range (trivialCoverSection w s)) (Set.range (trivialCoverSection w t))
  rw [range_trivialCoverSection, range_trivialCoverSection]
  exact Disjoint.preimage _
    (TopologicalSpace.Opens.coe_disjoint.2 (disjoint_opensRange_sigmaι (fun _ : S ↦ U) s t hst))

lemma iUnion_range_trivialCoverSection :
    ⋃ s : S, Set.range (trivialCoverSection w s) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
  obtain ⟨⟨s, y⟩, hy⟩ := (sigmaMk (fun _ : S ↦ U)).surjective
    (pullback.snd w (trivialCoverFold U S) x)
  refine ⟨s, ?_⟩
  rw [range_trivialCoverSection]
  exact ⟨y, by rw [← sigmaMk_mk, hy]⟩

variable {A : Type*} [Category.{u + 1} A]

/-- The `s`-th section of the base change of a trivial cover, as a morphism of the small étale
site of `∐ₛ U`. -/
noncomputable def trivialCoverSectionHom (W : U.Etale) (s : S) :
    Etale.mk (W.hom ≫ Sigma.ι (fun _ : S ↦ U) s) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (trivialCoverFold U S)).obj W :=
  MorphismProperty.Over.homMk (trivialCoverSection W.hom s) (pullback.lift_snd _ _ _)

instance (W : U.Etale) (s : S) : IsOpenImmersion (trivialCoverSectionHom W s).left :=
  inferInstanceAs (IsOpenImmersion (trivialCoverSection W.hom s))

/-- **Sections of the pushforward along a trivial cover.** For a sheaf `F` on `∐ₛ U` and an
étale `W ⟶ U`, the sections of the pushforward of `F` along the fold map over `W` are the
product of the sections of `F` over the `s`-th copies `W ⟶ U ⟶ ∐ₛ U`. -/
lemma existsUnique_sections_pullback_trivialCoverFold
    (F : Sheaf (∐ fun _ : S ↦ U).smallEtaleTopology A) (W : U.Etale) {a : A}
    (x : ∀ s : S, a ⟶ F.obj.obj (Opposite.op (Etale.mk (W.hom ≫ Sigma.ι (fun _ : S ↦ U) s)))) :
    ∃! σ : a ⟶ F.obj.obj (Opposite.op
        ((MorphismProperty.Over.pullback @Etale ⊤ (trivialCoverFold U S)).obj W)),
      ∀ s, σ ≫ F.obj.map (trivialCoverSectionHom W s).op = x s :=
  Etale.existsUnique_of_pairwise_disjoint F _ (trivialCoverSectionHom W)
    (pairwise_disjoint_range_trivialCoverSection W.hom)
    (iUnion_range_trivialCoverSection W.hom) x


end TrivialCover

end AlgebraicGeometry.Scheme
