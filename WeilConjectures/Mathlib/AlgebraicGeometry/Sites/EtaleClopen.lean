/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Clopen decompositions on the small étale site

Let `X` be a scheme and let `X = Z ⊔ W` be a decomposition of `X` into two disjoint opens.
Every étale `X`-scheme `V` then decomposes as `V = V_Z ⊔ V_W` with `V_Z = V ×_X Z` the open
subscheme of `V` lying over `Z`, and this decomposition is a covering for the small étale
topology. Consequently the sections of a sheaf over `V` are the product of the sections over
the two pieces.

This is the local input to `j_! ≅ j_*` for an open immersion `j` with clopen range: on the
complement of `j` the extension by zero is initial and the pushforward is terminal, so with a
zero object in the coefficient category the two agree, and the decomposition above glues that
statement back to an arbitrary `V`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.isTerminalSectionsOfIsEmpty`: a sheaf on the small étale
  site has terminal sections over an object whose underlying scheme is empty. This is the
  sheaf condition for the empty covering, and it is what makes the two pieces of a clopen
  decomposition *disjoint* from the point of view of the sheaf condition.
- `AlgebraicGeometry.Scheme.Etale.ofArrows_clopenι_mem_smallEtaleTopology`: the two pieces
  of the decomposition of `V` are a covering.
- `AlgebraicGeometry.Scheme.Etale.isLimitClopenFan`: the sections of a sheaf over `V` are
  the product of the sections over the two pieces.
- `AlgebraicGeometry.Scheme.Etale.isIso_app_of_isIso_clopen`: a morphism of sheaves which is
  an isomorphism on both pieces is an isomorphism over `V`.
- `AlgebraicGeometry.Scheme.Etale.isCompl_clopenComplOpens`: the range of an open immersion
  with clopen range and its complement are complementary opens of `X`.

## Implementation notes

The decomposition is indexed by `Bool` rather than by a two-element inductive type, because
`CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows` and `.hom_ext_ofArrows` take a family of
arrows indexed by an arbitrary type, and `Bool` makes the two case splits (`b = c` and
`b ≠ c`) in the compatibility check mechanical.

`AlgebraicGeometry.Scheme.Etale.str` is a spelling of the structure morphism of an étale
`X`-scheme whose codomain is literally `X`. The field `V.hom` has codomain
`(Functor.fromPUnit X).obj V.right`, which is definitionally but not syntactically `X`; every
`rw` along an open of `X` fails against the latter, so the abbreviation is not cosmetic.
-/

@[expose] public section

universe v' u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable {A : Type u'} [Category.{v'} A] {X : Scheme.{u}}

namespace Scheme.Etale

/-! ### Objects with empty underlying scheme -/

/-- The empty sieve on an object of the small étale site whose underlying scheme is empty is
a covering: the empty family of morphisms is (vacuously) jointly surjective. -/
lemma bot_mem_smallEtaleTopology (T : X.Etale) [IsEmpty T.left] :
    (⊥ : Sieve T) ∈ X.smallEtaleTopology T := by
  have h := Scheme.ofArrows_mem_smallEtaleTopology_iff
    (W := T) (Z := (Empty.elim : Empty → X.Etale)) (fun i ↦ i.elim)
  have hu : ⋃ (i : Empty), Set.range ((fun i : Empty ↦ i.elim : ∀ i, Empty.elim i ⟶ T) i).left =
      (Set.univ : Set T.left) := by
    simp [Set.eq_univ_iff_forall, IsEmpty.forall_iff]
  have hbot : Sieve.ofArrows (Empty.elim : Empty → X.Etale) (fun i ↦ i.elim) = (⊥ : Sieve T) := by
    ext W f
    simp only [Sieve.ofArrows, Sieve.generate_apply, Sieve.bot_apply, iff_false]
    rintro ⟨W', g, -, ⟨i⟩, -⟩
    exact i.elim
  exact hbot ▸ h.mpr hu

/-- A sheaf on the small étale site has terminal sections over an object whose underlying
scheme is empty. -/
noncomputable def isTerminalSectionsOfIsEmpty
    (G : Sheaf X.smallEtaleTopology A) (T : X.Etale) [IsEmpty T.left] :
    IsTerminal (G.obj.obj (op T)) := by
  refine IsTerminal.ofUnique (h := fun E ↦ ?_)
  have h := G.property E (⊥ : Sieve T) (bot_mem_smallEtaleTopology T)
    (fun _ _ hf ↦ hf.elim) (by rintro _ _ _ _ _ _ _ h₁ - -; exact h₁.elim)
  exact ⟨⟨h.choose⟩, fun a ↦ h.choose_spec.2 a (by rintro _ _ hf; exact hf.elim)⟩

/-! ### The part of an étale scheme lying over an open -/

/-- The structure morphism of an étale `X`-scheme, with codomain spelled as `X`. This is
definitionally `V.hom`, whose codomain is `(Functor.fromPUnit X).obj V.right`; the difference
is invisible to `exact` but fatal to `rw` along opens of `X`. -/
abbrev str (V : X.Etale) : V.left ⟶ X := V.hom

/-- The part of an étale `X`-scheme `V` lying over an open `Z ⊆ X`, that is, the open
subscheme `V ×_X Z` of `V`, again as an étale `X`-scheme. -/
noncomputable def part (V : X.Etale) (Z : X.Opens) : X.Etale :=
  MorphismProperty.Over.mk ⊤ ((V.str ⁻¹ᵁ Z).ι ≫ V.hom)
    (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)

@[simp] lemma part_left (V : X.Etale) (Z : X.Opens) :
    (V.part Z).left = ((V.str ⁻¹ᵁ Z : V.left.Opens) : Scheme.{u}) := rfl

@[simp] lemma part_hom (V : X.Etale) (Z : X.Opens) :
    (V.part Z).hom = (V.str ⁻¹ᵁ Z).ι ≫ V.hom := rfl

/-- The inclusion of the part of `V` lying over `Z` into `V`. -/
noncomputable def partι (V : X.Etale) (Z : X.Opens) : V.part Z ⟶ V :=
  MorphismProperty.Over.homMk (V.str ⁻¹ᵁ Z).ι rfl

@[simp] lemma partι_left (V : X.Etale) (Z : X.Opens) :
    (V.partι Z).left = (V.str ⁻¹ᵁ Z).ι := rfl

lemma range_partι (V : X.Etale) (Z : X.Opens) :
    Set.range (V.partι Z).left = ((V.str ⁻¹ᵁ Z : V.left.Opens) : Set V.left) :=
  Scheme.Opens.range_ι (V.str ⁻¹ᵁ Z)

/-- The part of `V` lying over `Z` maps into `Z`: a point of `V ×_X Z` is by construction a
point of `V` whose image lies in `Z`. -/
lemma range_part_hom_base_subset (V : X.Etale) (Z : X.Opens) :
    Set.range (V.part Z).hom.base ⊆ (Z : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact x.2

/-! ### The decomposition along a clopen -/

variable (Z W : X.Opens) (V : X.Etale)

/-- The two pieces into which a decomposition `X = Z ⊔ W` into opens cuts an étale
`X`-scheme `V`. The index `false` is the piece over `Z`, the index `true` the piece
over `W`. -/
noncomputable def clopenObj (b : Bool) : X.Etale := V.part (bif b then W else Z)

/-- The inclusion of the `b`-th piece of the decomposition of `V` into `V`. -/
noncomputable def clopenι (b : Bool) : clopenObj Z W V b ⟶ V := V.partι _

lemma range_clopenι (b : Bool) :
    Set.range (clopenι Z W V b).left =
      ((V.str ⁻¹ᵁ (bif b then W else Z) : V.left.Opens) : Set V.left) :=
  range_partι V _

variable {Z W}

/-- If `Z` and `W` cover `X`, the two pieces of the decomposition cover `V`. -/
lemma ofArrows_clopenι_mem_smallEtaleTopology (hu : Z ⊔ W = ⊤) :
    Sieve.ofArrows _ (clopenι Z W V) ∈ X.smallEtaleTopology V := by
  refine (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr ?_
  have hV : (V.str ⁻¹ᵁ Z) ⊔ (V.str ⁻¹ᵁ W) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hu, Scheme.Hom.preimage_top]
  ext v
  simp only [range_clopenι, Set.mem_iUnion, Set.mem_univ, iff_true]
  have hv : v ∈ (⊤ : V.left.Opens) := trivial
  rw [← hV] at hv
  rcases hv with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- An object of the small étale site mapping compatibly into two *different* pieces of the
decomposition has empty underlying scheme: its image lies in `Z ⊓ W = ⊥`. -/
lemma isEmpty_of_clopen (hd : Z ⊓ W = ⊥) {T : X.Etale} {b c : Bool} (hbc : b ≠ c)
    (a : T ⟶ clopenObj Z W V b) (d : T ⟶ clopenObj Z W V c)
    (h : a ≫ clopenι Z W V b = d ≫ clopenι Z W V c) : IsEmpty T.left := by
  have hV : (V.str ⁻¹ᵁ Z) ⊓ (V.str ⁻¹ᵁ W) = ⊥ := by
    rw [← Scheme.Hom.preimage_inf, hd, Scheme.Hom.preimage_bot]
  refine ⟨fun t ↦ ?_⟩
  have hl : a.left ≫ (clopenι Z W V b).left = d.left ≫ (clopenι Z W V c).left :=
    congrArg (fun f : T ⟶ V ↦ f.left) h
  set x : V.left := (clopenι Z W V b).left (a.left t) with hx
  have hb : x ∈ ((V.str ⁻¹ᵁ (bif b then W else Z) : V.left.Opens) : Set V.left) := by
    rw [← range_clopenι]; exact ⟨_, rfl⟩
  have hc : x ∈ ((V.str ⁻¹ᵁ (bif c then W else Z) : V.left.Opens) : Set V.left) := by
    rw [← range_clopenι]
    refine ⟨d.left t, ?_⟩
    rw [hx]
    exact (congrArg (fun f : T.left ⟶ V.left ↦ f.base t) hl).symm
  have hbot : x ∈ ((⊥ : V.left.Opens) : Set V.left) := by
    rw [← hV]
    cases b <;> cases c
    · exact absurd rfl hbc
    · exact ⟨hb, hc⟩
    · exact ⟨hc, hb⟩
    · exact absurd rfl hbc
  simp at hbot

/-- Any family of sections of a sheaf over the two pieces of the decomposition of `V` is
compatible: two morphisms into the *same* piece agreeing over `V` are equal because the
inclusion is a monomorphism, and two morphisms into *different* pieces have empty source, so
the sections there are terminal. -/
lemma clopen_compatible (hd : Z ⊓ W = ⊥) (G : Sheaf X.smallEtaleTopology A) {E : A}
    (x : ∀ b, E ⟶ G.obj.obj (op (clopenObj Z W V b))) ⦃T : X.Etale⦄ ⦃b c : Bool⦄
    (a : T ⟶ clopenObj Z W V b) (d : T ⟶ clopenObj Z W V c)
    (hcomm : a ≫ clopenι Z W V b = d ≫ clopenι Z W V c) :
    x b ≫ G.obj.map a.op = x c ≫ G.obj.map d.op := by
  by_cases hbc : b = c
  · subst hbc
    have hmono : Mono (clopenι Z W V b).left :=
      inferInstanceAs (Mono (V.str ⁻¹ᵁ (bif b then W else Z)).ι)
    have had : a = d := by
      apply MorphismProperty.Over.Hom.ext
      exact (cancel_mono (clopenι Z W V b).left).mp (congrArg (fun f : T ⟶ V ↦ f.left) hcomm)
    rw [had]
  · have : IsEmpty T.left := isEmpty_of_clopen V hd hbc a d hcomm
    exact (isTerminalSectionsOfIsEmpty G T).hom_ext _ _

/-- **The sheaf condition for a clopen decomposition.** If `X = Z ⊔ W` is a decomposition
into disjoint opens, then for every sheaf `G` on the small étale site of `X` and every
`V : X.Etale` the sections of `G` over `V` are the product of the sections over the two
pieces `V ×_X Z` and `V ×_X W`. -/
noncomputable def isLimitClopenFan (hd : Z ⊓ W = ⊥) (hu : Z ⊔ W = ⊤)
    (G : Sheaf X.smallEtaleTopology A) :
    IsLimit (Fan.mk (G.obj.obj (op V)) (fun b ↦ G.obj.map (clopenι Z W V b).op)) := by
  have hcov := ofArrows_clopenι_mem_smallEtaleTopology V hu
  refine Fan.IsLimit.mk _
    (fun s ↦ G.property.amalgamateOfArrows _ hcov (fun b ↦ s.proj b)
      (clopen_compatible V hd G _)) (fun s b ↦ ?_) (fun s m hm ↦ ?_)
  · exact G.property.amalgamateOfArrows_map _ hcov _ _ b
  · refine G.property.hom_ext_ofArrows _ hcov (fun b ↦ ?_)
    rw [G.property.amalgamateOfArrows_map]
    exact hm b

/-- **Locality of isomorphy along a clopen decomposition.** A morphism of sheaves on the
small étale site which is an isomorphism on both pieces of the decomposition of `V` is an
isomorphism over `V`. -/
lemma isIso_app_of_isIso_clopen (hd : Z ⊓ W = ⊥) (hu : Z ⊔ W = ⊤)
    {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G')
    (h : ∀ b, IsIso (φ.hom.app (op (clopenObj Z W V b)))) :
    IsIso (φ.hom.app (op V)) := by
  have hG := isLimitClopenFan V hd hu G
  have hG' := isLimitClopenFan V hd hu G'
  let w : (Discrete.functor fun b ↦ G.obj.obj (op (clopenObj Z W V b))) ≅
      Discrete.functor fun b ↦ G'.obj.obj (op (clopenObj Z W V b)) :=
    Discrete.natIso fun b ↦ @asIso _ _ _ _ _ (h b.as)
  have key : φ.hom.app (op V) = (IsLimit.conePointsIsoOfNatIso hG hG' w).hom := by
    refine hG'.hom_ext fun b ↦ ?_
    refine Eq.trans ?_ (IsLimit.conePointsIsoOfNatIso_hom_comp hG hG' w b).symm
    exact (φ.hom.naturality (clopenι Z W V b.as).op).symm
  rw [key]
  infer_instance

/-! ### The decomposition attached to an open immersion with clopen range -/

section OpenImmersion

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (hj : IsClopen (Set.range j))

include hj

/-- The open complement of the range of an open immersion with clopen range. -/
def clopenComplOpens : X.Opens := ⟨(Set.range j)ᶜ, hj.1.isOpen_compl⟩

lemma inf_clopenComplOpens : j.opensRange ⊓ clopenComplOpens j hj = ⊥ := by
  ext x
  simp [clopenComplOpens, Scheme.Hom.opensRange]

lemma sup_clopenComplOpens : j.opensRange ⊔ clopenComplOpens j hj = ⊤ := by
  ext x
  simp [clopenComplOpens, Scheme.Hom.opensRange]

lemma isCompl_clopenComplOpens : IsCompl j.opensRange (clopenComplOpens j hj) :=
  ⟨disjoint_iff.mpr (inf_clopenComplOpens j hj), codisjoint_iff.mpr (sup_clopenComplOpens j hj)⟩

omit [IsOpenImmersion j] in
lemma range_ι_clopenComplOpens :
    Set.range (clopenComplOpens j hj).ι.base = (Set.range j.base)ᶜ :=
  Scheme.Opens.range_ι (clopenComplOpens j hj)

end OpenImmersion

end Scheme.Etale

end AlgebraicGeometry
