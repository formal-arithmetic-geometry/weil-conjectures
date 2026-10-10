/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The direct image along a finite étale morphism is left adjoint to the pullback

Let `f : X ⟶ Y` be separated and étale. For an étale `X`-scheme `u : U ⟶ X` the graph
`Γ_u : U ⟶ U ×_Y X` is a section of the separated étale projection `U ×_Y X ⟶ U`, hence an open
and closed immersion. A sheaf `G` on `X_ét` therefore has
`G(U ×_Y X) = G(U) × G(U ×_Y X ∖ Γ_u)`, and extending a section of `G` over `U` by zero
off the graph defines a natural map

`η_G : G ⟶ f^* f_* G`,

a section of the counit `f^* f_* G ⟶ G`, which is restriction to the graph.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.isLimitBinaryFanOfIsCompl`: the sections of a sheaf on the
  small étale site over an object split as a product along a decomposition into two
  complementary open subschemes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] {X : Scheme.{u}}

section Clopen

variable (G : Sheaf X.smallEtaleTopology A) {P U W : X.Etale} (i : U ⟶ P) (j : W ⟶ P)
  [IsOpenImmersion i.left] [IsOpenImmersion j.left]
  (h : IsCompl (Set.range i.left.base) (Set.range j.left.base))

include h in
/-- The sections of a sheaf on the small étale site over `P` are determined by their
restrictions to two complementary open subschemes `U` and `W` of `P`, and any pair of sections
over `U` and `W` glues. -/
lemma Etale.existsUnique_of_isCompl {a : A} (s : a ⟶ G.obj.obj (op U))
    (t : a ⟶ G.obj.obj (op W)) :
    ∃! σ : a ⟶ G.obj.obj (op P), σ ≫ G.obj.map i.op = s ∧ σ ≫ G.obj.map j.op = t := by
  let Z : Bool → X.Etale := fun b ↦ bif b then U else W
  let π : ∀ b, Z b ⟶ P := fun b ↦ match b with
    | true => i
    | false => j
  have hcov : Sieve.ofArrows Z π ∈ X.smallEtaleTopology P := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    have hx : x ∈ Set.range i.left.base ∪ Set.range j.left.base := by
      have h₀ : x ∈ (⊤ : Set P.left) := trivial
      rwa [← h.sup_eq_top] at h₀
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hsh := (G.property a).isSheafFor (Presieve.ofArrows Z π) hcov
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  let x : ∀ b, (G.obj ⋙ coyoneda.obj (op a)).obj (op (Z b)) := fun b ↦ match b with
    | true => s
    | false => t
  have hmono : Mono i := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono i.left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  have hmono' : Mono j := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono j.left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  -- maps into both `U` and `W` over `P` have empty source
  have hempty {T : X.Etale} (g₁ : T ⟶ U) (g₂ : T ⟶ W) (hg : g₁ ≫ i = g₂ ≫ j) :
      IsEmpty T.left := by
    refine ⟨fun z ↦ ?_⟩
    have h₁ : i.left (g₁.left z) = j.left (g₂.left z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun g ↦ g.left z) hg
    have h₂ : j.left (g₂.left z) ∈ Set.range i.left := ⟨_, h₁⟩
    exact Set.disjoint_iff.1 h.disjoint ⟨h₂, ⟨_, rfl⟩⟩
  obtain ⟨σ, hσ, hσu⟩ := hsh x (by
    intro b b' T g₁ g₂ hg
    have hsub : ∀ (T : X.Etale) [IsEmpty T.left] (c c' : a ⟶ G.obj.obj (op T)), c = c' :=
      fun T _ c c' ↦ (Etale.isTerminalSectionsOfIsEmpty G T).hom_ext _ _
    cases b <;> cases b'
    · obtain rfl : g₁ = g₂ := (cancel_mono j).1 hg
      rfl
    · have := hempty g₂ g₁ hg.symm
      exact hsub _ _ _
    · have := hempty g₁ g₂ hg
      exact hsub _ _ _
    · obtain rfl : g₁ = g₂ := (cancel_mono i).1 hg
      rfl)
  refine ⟨σ, ⟨hσ true, hσ false⟩, fun σ' hσ' ↦ hσu σ' ?_⟩
  rintro (_ | _)
  · exact hσ'.2
  · exact hσ'.1

/-- The sections of a sheaf on the small étale site over `P` are the product of its sections
over two complementary open subschemes `U` and `W` of `P`. -/
noncomputable def Etale.isLimitBinaryFanOfIsCompl :
    IsLimit (BinaryFan.mk (G.obj.map i.op) (G.obj.map j.op)) :=
  BinaryFan.IsLimit.mk _
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose)
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec.1)
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec.2)
    (fun s t _ h₁ h₂ ↦ (Etale.existsUnique_of_isCompl G i j h s t).unique ⟨h₁, h₂⟩
      (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec)

end Clopen

section Graph

variable {Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f] [IsSeparated f]

/-- For an étale `X`-scheme `U`, the étale `X`-scheme `U ×_Y X`, with structure morphism the
second projection: the sections of `f^* f_* G` over `U` are the sections of `G` over it. -/
noncomputable abbrev Etale.graphTarget (U : X.Etale) : X.Etale :=
  f.Etale.obj ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U)

/-- The graph `U ⟶ U ×_Y X` of the structure morphism of an étale `X`-scheme `U`, the unit of
the adjunction between `MorphismProperty.Over.map` and base change along `f`. -/
noncomputable def Etale.graph (U : X.Etale) : U ⟶ Etale.graphTarget f U :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ f
    ‹AlgebraicGeometry.Etale f› _root_.trivial).unit.app U

lemma Etale.graph_left (U : X.Etale) :
    (Etale.graph f U).left = pullback.lift (𝟙 U.left) U.hom (by simp) := rfl


@[reassoc (attr := simp)]
lemma Etale.graph_left_snd (U : X.Etale) :
    (Etale.graph f U).left ≫
      pullback.snd ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U).hom f =
        U.hom := by
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma Etale.graph_left_fst (U : X.Etale) :
    (Etale.graph f U).left ≫
      pullback.fst ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U).hom f =
        𝟙 U.left := by
  exact pullback.lift_fst _ _ _

instance (U : X.Etale) : IsOpenImmersion (Etale.graph f U).left :=
  IsOpenImmersion.of_section_of_etale (pullback.fst (U.hom ≫ f) f) _ (Etale.graph_left_fst f U)

lemma Etale.isClosed_range_graph_left (U : X.Etale) :
    IsClosed (Set.range (Etale.graph f U).left) :=
  (IsClosedImmersion.of_section_of_isSeparated (pullback.fst (U.hom ≫ f) f) _
    (Etale.graph_left_fst f U)).isClosedEmbedding.isClosed_range

/-- The open subscheme of `U ×_Y X` complementary to the graph of `U ⟶ X`. -/
noncomputable def Etale.graphCompl (U : X.Etale) : (Etale.graphTarget f U).left.Opens :=
  ⟨(Set.range (Etale.graph f U).left)ᶜ, (Etale.isClosed_range_graph_left f U).isOpen_compl⟩

/-- The complement of the graph of `U ⟶ X` in `U ×_Y X`, as an étale `X`-scheme. -/
noncomputable abbrev Etale.graphComplObj (U : X.Etale) : X.Etale :=
  MorphismProperty.Over.mk ⊤ ((Etale.graphCompl f U).ι ≫ (Etale.graphTarget f U).hom)
    inferInstance

/-- The inclusion of the complement of the graph of `U ⟶ X` into `U ×_Y X`. -/
noncomputable abbrev Etale.graphComplι (U : X.Etale) :
    Etale.graphComplObj f U ⟶ Etale.graphTarget f U :=
  MorphismProperty.Over.homMk (Etale.graphCompl f U).ι rfl trivial

instance (U : X.Etale) : IsOpenImmersion (Etale.graphComplι f U).left :=
  inferInstanceAs (IsOpenImmersion (Etale.graphCompl f U).ι)

lemma Etale.isCompl_range_graph (U : X.Etale) :
    IsCompl (Set.range (Etale.graph f U).left) (Set.range (Etale.graphComplι f U).left) := by
  change IsCompl _ (Set.range (Etale.graphCompl f U).ι)
  rw [Scheme.Opens.range_ι]
  exact isCompl_compl

lemma Etale.graph_comp_map {U U' : X.Etale} (φ : U' ⟶ U) :
    (Etale.graph f U').left ≫
        (f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)).left =
      φ.left ≫ (Etale.graph f U).left :=
  (congrArg (fun g ↦ g.left) ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤
    f ‹AlgebraicGeometry.Etale f› _root_.trivial).unit.naturality φ)).symm

/-- The graphs are compatible with base change: for `φ : U' ⟶ U` the square
```
U' ──graph──→ U' ×_Y X
│φ               │φ × 𝟙
U ───graph──→ U ×_Y X
```
is cartesian. -/
lemma Etale.isPullback_graph {U U' : X.Etale} (φ : U' ⟶ U) :
    IsPullback (Etale.graph f U').left φ.left
      (f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)).left
      (Etale.graph f U).left := by
  refine IsPullback.of_isLimit' ⟨Etale.graph_comp_map f φ⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ s.fst ≫ pullback.fst _ _) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ _ ↦ ?_))
  · have h₁ : (f.Etale.map ((MorphismProperty.Over.map ⊤
        ‹AlgebraicGeometry.Etale f›).map φ)).left ≫ pullback.fst _ f =
        pullback.fst _ f ≫ φ.left :=
      Hom.etale_map_left_comp_fst f _
    have h₂ := Hom.etale_map_left_comp_snd f ((MorphismProperty.Over.map ⊤
      ‹AlgebraicGeometry.Etale f›).map φ)
    have hc := s.condition
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Etale.graph_left_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, Etale.graph_left_snd, ← h₂, reassoc_of% hc,
        Etale.graph_left_snd, ← MorphismProperty.Over.w φ, ← reassoc_of% h₁,
        reassoc_of% hc, Etale.graph_left_fst_assoc]
  · have h₁ : (f.Etale.map ((MorphismProperty.Over.map ⊤
        ‹AlgebraicGeometry.Etale f›).map φ)).left ≫ pullback.fst _ f =
        pullback.fst _ f ≫ φ.left :=
      Hom.etale_map_left_comp_fst f _
    rw [Category.assoc, ← h₁, reassoc_of% s.condition, Etale.graph_left_fst, Category.comp_id]
  · rw [← h₁, Category.assoc, Etale.graph_left_fst, Category.comp_id]

/-- The base change `U' ×_Y X ⟶ U ×_Y X` of a morphism `φ : U' ⟶ U` of étale `X`-schemes. -/
noncomputable abbrev Etale.graphTargetMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphTarget f U' ⟶ Etale.graphTarget f U :=
  f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)

lemma Etale.graph_comp_graphTargetMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graph f U' ≫ Etale.graphTargetMap f φ = φ ≫ Etale.graph f U :=
  MorphismProperty.Over.Hom.ext (Etale.graph_comp_map f φ)

/-- The base change of a morphism of étale `X`-schemes carries the complement of the graph into
the complement of the graph. -/
noncomputable def Etale.graphComplMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphComplObj f U' ⟶ Etale.graphComplObj f U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift (Etale.graphComplι f U).left
    ((Etale.graphComplι f U').left ≫ (Etale.graphTargetMap f φ).left) (by
      rintro _ ⟨z, rfl⟩
      change _ ∈ Set.range (Etale.graphCompl f U).ι
      rw [Scheme.Opens.range_ι]
      intro hz
      have h := Scheme.range_snd_of_isPullback (Etale.isPullback_graph f φ).flip
      have hz' : (Etale.graphComplι f U').left z ∈ Set.range (Etale.graph f U').left := by
        rw [h]
        exact hz
      have : (Etale.graphComplι f U').left z ∈ Etale.graphCompl f U' := z.2
      exact this hz')) (by
        change _ ≫ (Etale.graphComplι f U).left ≫ _ = (Etale.graphComplι f U').left ≫ _
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
          MorphismProperty.Over.w]) trivial

@[reassoc (attr := simp)]
lemma Etale.graphComplMap_comp_graphComplι {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphComplMap f φ ≫ Etale.graphComplι f U =
      Etale.graphComplι f U' ≫ Etale.graphTargetMap f φ :=
  MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

end Graph

section Unit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f] [IsSeparated f]
  [HasZeroMorphisms A] (G : Sheaf X.smallEtaleTopology A)

lemma Etale.graph_hom_ext {U : X.Etale} {a : A} {σ σ' : a ⟶ G.obj.obj (op (Etale.graphTarget f U))}
    (h₁ : σ ≫ G.obj.map (Etale.graph f U).op = σ' ≫ G.obj.map (Etale.graph f U).op)
    (h₂ : σ ≫ G.obj.map (Etale.graphComplι f U).op = σ' ≫ G.obj.map (Etale.graphComplι f U).op) :
    σ = σ' :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) _ _).unique
    ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

/-- The extension by zero of a section of `G` over an étale `X`-scheme `U` to `U ×_Y X`: the
section restricting to the given one on the graph of `U ⟶ X` and to zero off it. -/
noncomputable def Etale.graphExtend (U : X.Etale) :
    G.obj.obj (op U) ⟶ G.obj.obj (op (Etale.graphTarget f U)) :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose

@[reassoc (attr := simp)]
lemma Etale.graphExtend_graph (U : X.Etale) :
    Etale.graphExtend f G U ≫ G.obj.map (Etale.graph f U).op = 𝟙 _ :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma Etale.graphExtend_graphComplι (U : X.Etale) :
    Etale.graphExtend f G U ≫ G.obj.map (Etale.graphComplι f U).op = 0 :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose_spec.2

@[reassoc]
lemma Etale.graphExtend_naturality {U U' : X.Etale} (φ : U' ⟶ U) :
    G.obj.map φ.op ≫ Etale.graphExtend f G U' =
      Etale.graphExtend f G U ≫ G.obj.map (Etale.graphTargetMap f φ).op := by
  refine Etale.graph_hom_ext f G ?_ ?_
  · rw [Category.assoc, Etale.graphExtend_graph, Category.comp_id, Category.assoc,
      ← Functor.map_comp, ← op_comp, Etale.graph_comp_graphTargetMap, op_comp,
      Functor.map_comp, Etale.graphExtend_graph_assoc]
  · rw [Category.assoc, Etale.graphExtend_graphComplι, comp_zero, Category.assoc,
      ← Functor.map_comp, ← op_comp, ← Etale.graphComplMap_comp_graphComplι, op_comp,
      Functor.map_comp, Etale.graphExtend_graphComplι_assoc, zero_comp]

lemma Etale.graphExtend_natural {G G' : Sheaf X.smallEtaleTopology A} (ψ : G ⟶ G')
    (U : X.Etale) :
    ψ.hom.app (op U) ≫ Etale.graphExtend f G' U =
      Etale.graphExtend f G U ≫ ψ.hom.app (op (Etale.graphTarget f U)) := by
  refine Etale.graph_hom_ext f G' ?_ ?_
  · rw [Category.assoc, Etale.graphExtend_graph, Category.comp_id, Category.assoc,
      ← ψ.hom.naturality, Etale.graphExtend_graph_assoc]
  · rw [Category.assoc, Etale.graphExtend_graphComplι, comp_zero, Category.assoc,
      ← ψ.hom.naturality, Etale.graphExtend_graphComplι_assoc, zero_comp]
end Unit

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Etale



variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [AlgebraicGeometry.Etale f] [IsSeparated f]

/-- For a separated étale `f : X ⟶ Y`, extension by zero off the graphs is a natural map
`G ⟶ f^* f_* G`, where `f^*` is computed as the restriction along `X_ét ⟶ Y_ét`. It is a
section of the counit of `f^* ⊣ f_*` (`AlgebraicGeometry.Etale.lowerStarUnit_comp_counit`), and
for a finite étale `f` it is the unit of an adjunction `f_* ⊣ f^*`. -/
noncomputable def Etale.lowerStarUnit :
    𝟭 (Sheaf X.smallEtaleTopology A) ⟶ (f)_*[A] ⋙ Etale.localizationRestriction A f ‹_› where
  app G := ObjectProperty.homMk
    { app U := Scheme.Etale.graphExtend f G U.unop
      naturality _ _ φ := Scheme.Etale.graphExtend_naturality f G φ.unop }
  naturality _ _ ψ := by
    ext U
    exact Scheme.Etale.graphExtend_natural f ψ U.unop

lemma Etale.lowerStarUnit_app_hom_app (G : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((Etale.lowerStarUnit A f).app G).hom.app U = Scheme.Etale.graphExtend f G U.unop :=
  rfl

lemma Etale.localizationRestrictionLowerStarAdjunction_counit_app_hom_app
    (G : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((Etale.localizationRestrictionLowerStarAdjunction A f ‹_›).counit.app G).hom.app U =
      G.obj.map (Scheme.Etale.graph f U.unop).op := by
  simp [Etale.localizationRestrictionLowerStarAdjunction, Scheme.Etale.graph]

/-- Extension by zero off the graphs is a section of the counit of `f^* ⊣ f_*`, which is
restriction to the graphs. -/
@[reassoc (attr := simp)]
lemma Etale.lowerStarUnit_comp_counit :
    Etale.lowerStarUnit A f ≫ (Etale.localizationRestrictionLowerStarAdjunction A f ‹_›).counit =
      𝟙 _ := by
  ext G U
  simp [Etale.localizationRestrictionLowerStarAdjunction_counit_app_hom_app,
    Etale.lowerStarUnit_app_hom_app]

end AlgebraicGeometry
