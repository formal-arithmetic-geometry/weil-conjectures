/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# Graphs of partial sections of a fibre product

For a partial section `γ : U ⟶ X ×_S Y` of the first projection, defined on an open
`j : U ⟶ X` and with `Y ⟶ S` separated, the graph of `γ` is a closed immersion
`U ⟶ U ×_S Y`, and the scheme-theoretic image of `γ` restricts over `U ×_S Y` to that
graph.

This is the elimination-of-indeterminacy input for the graph-extension and
common-modification steps of the Nagata compactification proof (Stacks Project
Tags 0F3X–0F3Z; revised blueprint `lemma:nagata-scheme-image-partial-section`).

## Main definitions and results

- `AlgebraicGeometry.partialSection`: the graph `U ⟶ U ×_S Y` of a partial
  section, a closed immersion since `Y ⟶ S` is separated;
- `AlgebraicGeometry.partialSection_openι`: the factorization of `γ` through
  the base-changed open immersion `U ×_S Y ⟶ X ×_S Y`;
- `AlgebraicGeometry.isPullback_partialSectionOpenι` and
  `AlgebraicGeometry.isIso_partialSectionOpenι_restrict`: the base-changed open
  immersion square is cartesian, so `j` being an isomorphism over an open `V ⊆ X`
  makes `U ×_S Y ⟶ X ×_S Y` an isomorphism over the preimage of `V`;
- `AlgebraicGeometry.isPullback_partialSection`: the graph is the pullback of
  `γ` along the base-changed open immersion;
- `AlgebraicGeometry.ker_comap_partialSectionOpenι`: the kernel ideal sheaf of
  `γ` restricted to `U ×_S Y` is the kernel of its graph;
- `AlgebraicGeometry.partialSectionRestrictIso`: the induced isomorphism
  `U ≅ (U ×_S Y) ×_{X ×_S Y} Z` of `U` with the restriction of the scheme-theoretic
  image of `γ` over `U ×_S Y`, compatible with the graph
  (`partialSectionRestrictIso_hom_fst`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S X Y U : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (j : U ⟶ X)
variable (γ : U ⟶ pullback x y)

/-- The base-changed open immersion `U ×_S Y ⟶ X ×_S Y` induced by `j : U ⟶ X`. -/
def partialSectionOpenι : pullback (j ≫ x) y ⟶ pullback x y :=
  pullback.map (j ≫ x) y x y j (𝟙 Y) (𝟙 S) rfl (by simp)

@[reassoc (attr := simp)]
lemma partialSectionOpenι_fst :
    partialSectionOpenι x y j ≫ pullback.fst x y = pullback.fst (j ≫ x) y ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma partialSectionOpenι_snd :
    partialSectionOpenι x y j ≫ pullback.snd x y = pullback.snd (j ≫ x) y :=
  pullback.lift_snd _ _ _

instance [IsOpenImmersion j] : IsOpenImmersion (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› inferInstance rfl (by simp)

instance [QuasiCompact j] : QuasiCompact (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @QuasiCompact) ‹_› inferInstance rfl (by simp)

/-- **The base-changed open immersion square is cartesian**: `U ×_S Y` is the fibre
product of `j : U ⟶ X` and the first projection `X ×_S Y ⟶ X`. -/
lemma isPullback_partialSectionOpenι :
    IsPullback (partialSectionOpenι x y j) (pullback.fst (j ≫ x) y)
      (pullback.fst x y) j :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (j ≫ x) y).flip)
    (partialSectionOpenι_fst x y j) (IsPullback.of_hasPullback x y).flip

/-- **The base change of an isomorphism over an open stays an isomorphism**: if
`j : U ⟶ X` restricts to an isomorphism over an open `V ⊆ X` — in the application `j`
is an admissible blow-up and `V` the complement of its center — then the base-changed
morphism `U ×_S Y ⟶ X ×_S Y` restricts to an isomorphism over the preimage of `V`
under the first projection. -/
lemma isIso_partialSectionOpenι_restrict (V : X.Opens) [IsIso (j ∣_ V)] :
    IsIso (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) := by
  -- `(U ×_S Y)|_{ρ⁻¹V}` is `U ×_X (X ×_S Y)|_V` by pasting the restriction square onto
  -- the cartesian square above, ...
  have hA : IsPullback (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V))
      (partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι
      (pullback.fst x y ⁻¹ᵁ V).ι (partialSectionOpenι x y j) :=
    isPullback_morphismRestrict _ _
  have hpaste := hA.paste_vert (isPullback_partialSectionOpenι x y j)
  -- ... and `(X ×_S Y)|_V ⟶ X` factors through `V`, so it is `j|_V` base-changed.
  have ht : IsPullback (j ⁻¹ᵁ V).ι (j ∣_ V) j V.ι :=
    (isPullback_morphismRestrict j V).flip
  have hs : IsPullback ((partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι ≫
        pullback.fst (j ≫ x) y)
      (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) j
      ((pullback.fst x y ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

variable (hγ : γ ≫ pullback.fst x y = j)

/-- The graph of a partial section `γ` of the first projection over `j : U ⟶ X`: the
induced section `U ⟶ U ×_S Y` of the projection to `U`. -/
def partialSection : U ⟶ pullback (j ≫ x) y :=
  pullback.lift (𝟙 U) (γ ≫ pullback.snd x y)
    (by rw [Category.id_comp, Category.assoc, ← pullback.condition, ← Category.assoc, hγ])

@[reassoc (attr := simp)]
lemma partialSection_fst : partialSection x y j γ hγ ≫ pullback.fst (j ≫ x) y = 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma partialSection_snd :
    partialSection x y j γ hγ ≫ pullback.snd (j ≫ x) y = γ ≫ pullback.snd x y :=
  pullback.lift_snd _ _ _

/-- The partial section factors through the base-changed open immersion as its
graph. -/
@[reassoc]
lemma partialSection_openι :
    partialSection x y j γ hγ ≫ partialSectionOpenι x y j = γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, partialSectionOpenι_fst, partialSection_fst_assoc, hγ]
  · rw [Category.assoc, partialSectionOpenι_snd, partialSection_snd]

/-- The graph of a partial section of a separated projection is a closed immersion. -/
instance [IsSeparated y] : IsClosedImmersion (partialSection x y j γ hγ) := by
  have hsep : IsSeparated (pullback.fst (j ≫ x) y) :=
    MorphismProperty.pullback_fst _ _ ‹_›
  have : IsClosedImmersion
      (partialSection x y j γ hγ ≫ pullback.fst (j ≫ x) y) := by
    rw [partialSection_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (partialSection x y j γ hγ) (pullback.fst (j ≫ x) y)

include hγ in
/-- A partial section over a quasi-compact open immersion is quasi-compact. -/
lemma quasiCompact_of_partialSection [IsSeparated y] [IsOpenImmersion j] [QuasiCompact j] :
    QuasiCompact γ := by
  have : QuasiCompact (partialSection x y j γ hγ ≫ partialSectionOpenι x y j) :=
    inferInstance
  rw [partialSection_openι x y j γ hγ] at this
  exact this

/-- The graph square: the graph of a partial section is the pullback of `γ` along the
base-changed open immersion `U ×_S Y ⟶ X ×_S Y`. -/
lemma isPullback_partialSection [IsOpenImmersion j] :
    IsPullback (𝟙 U) (partialSection x y j γ hγ) γ (partialSectionOpenι x y j) :=
  IsPullback.of_horiz_isIso_mono
    ⟨by rw [Category.id_comp, partialSection_openι]⟩

section KernelIdentity

variable [IsSeparated y] [IsOpenImmersion j] [QuasiCompact j]

/-- **The scheme-theoretic image of a partial section restricts to its graph**: the
kernel ideal sheaf of `γ` pulled back to `U ×_S Y` is the kernel of the (closed
immersion) graph of `γ`.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`, kernel form.) -/
theorem ker_comap_partialSectionOpenι :
    γ.ker.comap (partialSectionOpenι x y j) = (partialSection x y j γ hγ).ker := by
  have := quasiCompact_of_partialSection x y j γ hγ
  rw [← Scheme.Hom.ker_pullback_snd γ (partialSectionOpenι x y j)]
  have H := isPullback_partialSection x y j γ hγ
  have hsnd : pullback.snd γ (partialSectionOpenι x y j) =
      H.isoPullback.inv ≫ partialSection x y j γ hγ :=
    ((Iso.inv_comp_eq _).mpr H.isoPullback_hom_snd.symm).symm
  rw [hsnd, Scheme.Hom.ker_comp_of_isIso]

/-- The isomorphism of `U` with the restriction of the scheme-theoretic image of a
partial section over `U ×_S Y`: the composite of the identification of `U` with the
image of its graph and the flat base change identification of images.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
def partialSectionRestrictIso : U ≅ pullback (partialSectionOpenι x y j) γ.imageι :=
  asIso (partialSection x y j γ hγ).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (ker_comap_partialSectionOpenι x y j γ hγ).symm) ≪≫
    γ.ker.comapIso (partialSectionOpenι x y j)

/-- The restriction isomorphism is compatible with the graph: composing with the
first projection of the fibre product recovers the graph of the partial section. -/
@[reassoc (attr := simp)]
lemma partialSectionRestrictIso_hom_fst :
    (partialSectionRestrictIso x y j γ hγ).hom ≫
        pullback.fst (partialSectionOpenι x y j) γ.imageι =
      partialSection x y j γ hγ := by
  simp only [partialSectionRestrictIso, Iso.trans_hom, asIso_hom, eqToIso.hom,
    Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  rw [Scheme.IdealSheafData.subschemeι_eqToHom ((ker_comap_partialSectionOpenι x y j γ hγ).symm)]
  exact (partialSection x y j γ hγ).toImage_imageι

end KernelIdentity

/-- **The graph image is proper over the base**: if `Y ⟶ S` is proper, the
scheme-theoretic image of a partial section `γ : U ⟶ X ×_S Y`, projected to `X`, is
proper. This is the properness half of the graph-extension lemma: together with
`partialSectionRestrictIso` (the image restricts to `U` over `U ×_S Y`) it yields the
proper extension `SIm(γ) ⟶ X` of the partial section
(Stacks Project Tag 0F3Z; revised blueprint `lemma:nagata-graph-extension`). -/
theorem isProper_imageι_fst [IsProper y] :
    IsProper (γ.imageι ≫ pullback.fst x y) := by
  have : IsProper (pullback.fst x y) := MorphismProperty.pullback_fst _ _ ‹_›
  infer_instance

end AlgebraicGeometry
