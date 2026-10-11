/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.InjectiveModuleAcyclic
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapEtale

/-!
# Higher direct images whose classes die locally

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `G` an étale sheaf of `Λ`-modules on
`Y`. The sheaf `R^q h_* G` is the sheafification of `W ↦ H^q(W ×_X Y, G|)`
(`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`), so it vanishes
as soon as every class of `H^q(W ×_X Y, G|)`, for `W` affine étale over `X`, dies on an étale
cover of `W`. The cohomology `H^q(W ×_X Y, G|)` is computed with sheaves of `Λ`-modules, while
the classes of the vanishing criteria we have in mind are classes of abelian sheaves; we show
that if the classes of the underlying abelian sheaf of `G` die locally, so do the classes of `G`
(`AlgebraicGeometry.Etale.classesDieLocally_of_classesDieLocallyAb`). The proof is by dimension
shifting along an embedding of `G` into an injective sheaf of `Λ`-modules, whose underlying
abelian sheaf has no higher cohomology over the quasi-compact quasi-separated schemes
`W ×_X Y` (`AlgebraicGeometry.Scheme.subsingleton_H_forget₂_of_injective`); in degree `0` we use
that the pullback of cohomology classes along an étale morphism is the restriction of sections
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap`).

## Main definitions

- `AlgebraicGeometry.Etale.ClassesDieLocallyAb`: every class of the abelian cohomology of
  `A|_{W ×_X Y}`, `W` affine, dies on an étale cover of `W`.
- `AlgebraicGeometry.Etale.ClassesDieLocally`: the same for the cohomology of a sheaf of
  `Λ`-modules, written as `Ext^n(h^* Λ[W], G)`.

## Main statements

- `AlgebraicGeometry.Etale.classesDieLocally_of_classesDieLocallyAb`: the comparison.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Sections

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- Morphisms out of `h^* Λ[W]` are the sections over `W ×_X Y`: the adjunction `h^* ⊣ h_*`
followed by `AlgebraicGeometry.Etale.freeSheafHomEquiv`. -/
noncomputable def Etale.upperStarFreeSheafHomEquivSections (W : X.Etale)
    (C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ C) ≃
      C.obj.obj (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W)) :=
  ((Etale.upperStarLowerStarAdjunction _ h).homEquiv _ _).trans (Etale.freeSheafHomEquiv Λ W _)

lemma Etale.upperStarFreeSheafHomEquivSections_comp (W : X.Etale)
    {C C' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (s : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ C) (π : C ⟶ C') :
    Etale.upperStarFreeSheafHomEquivSections Λ h W C' (s ≫ π) =
      π.hom.app _ (Etale.upperStarFreeSheafHomEquivSections Λ h W C s) := by
  simp only [Etale.upperStarFreeSheafHomEquivSections, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_right, Etale.freeSheafHomEquiv_comp]
  rfl

lemma Etale.upperStarFreeSheafHomEquivSections_map {W W' : X.Etale} (g : W' ⟶ W)
    {C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (s : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ C) :
    Etale.upperStarFreeSheafHomEquivSections Λ h W' C
        ((h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ X).map g) ≫ s) =
      C.obj.map ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).map g).op
        (Etale.upperStarFreeSheafHomEquivSections Λ h W C s) := by
  simp only [Etale.upperStarFreeSheafHomEquivSections, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left, Etale.freeSheafHomEquiv_map]
  rfl

lemma Etale.upperStarFreeSheafHomEquivSections_zero (W : X.Etale)
    (C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.upperStarFreeSheafHomEquivSections Λ h W C 0 = 0 := by
  have := Etale.upperStarFreeSheafHomEquivSections_comp Λ h W (0 : _ ⟶ C) (0 : C ⟶ C)
  rw [Limits.comp_zero] at this
  rw [this]
  rfl

end Sections

section Terminal

variable {Y : Scheme.{u}}

/-- The structure morphism of the terminal object of the small étale site of a scheme `S` is
an isomorphism. -/
instance Etale.isIso_terminal_hom (S : Scheme.{u}) : IsIso (⊤_ S.Etale).hom := by
  let φ := (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale S).from (⊤_ S.Etale)
  have : IsIso φ := isIso_of_isTerminal terminalIsTerminal
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale S) φ
  have hφ : φ.left ≫ 𝟙 S = (⊤_ S.Etale).hom := MorphismProperty.Over.w φ
  rw [← hφ, Category.comp_id]
  exact inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).map φ))

/-- The étale `Y`-scheme `V`, seen as the image of the terminal object of `V_ét`, maps to `V`. -/
noncomputable def Etale.overMapTerminalHom (V : Y.Etale) :
    (MorphismProperty.Over.map ⊤ V.prop).obj (⊤_ V.left.Etale) ⟶ V :=
  MorphismProperty.Over.homMk (⊤_ V.left.Etale).hom rfl

/-- For a morphism `k : V' ⟶ V` of étale `Y`-schemes, the image in `Y_ét` of the terminal object
of `V'_ét`, seen as an étale `V`-scheme along `k`, is `V'`. -/
noncomputable def Etale.overMapOverMapTerminalIso {V V' : Y.Etale} (k : V' ⟶ V) :
    (MorphismProperty.Over.map ⊤ V.prop).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale k.left)).obj
          (⊤_ V'.left.Etale)) ≅ V' :=
  MorphismProperty.Over.isoMk (asIso (⊤_ V'.left.Etale).hom) (by
    change (⊤_ V'.left.Etale).hom ≫ V'.hom = ((⊤_ V'.left.Etale).hom ≫ k.left) ≫ V.hom
    rw [Category.assoc, MorphismProperty.Over.w k])

/-- A degree-`0` class of the restriction of an abelian sheaf `A` to the étale `Y`-scheme `V`,
given by a section of `A` over `V`. -/
noncomputable def Etale.classOfSection (V : Y.Etale)
    {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : A.obj.obj (op V)) :
    Sheaf.H ((Etale.localizationRestriction AddCommGrpCat.{u + 1} V.hom V.prop).obj A) 0 :=
  (Sheaf.H.equiv₀ _ terminalIsTerminal).symm (A.obj.map (Etale.overMapTerminalHom V).op a)

/-- Pulling back the class of a section along a morphism `k : V' ⟶ V` of étale `Y`-schemes is
restricting the section along `k`. -/
lemma Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap_classOfSection
    {V V' : Y.Etale} (k : V' ⟶ V) {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : A.obj.obj (op V)) :
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} k.left
        inferInstance).hom.app
        ((Etale.localizationRestriction AddCommGrpCat.{u + 1} V.hom V.prop).obj A)).hom.app
        (op (⊤_ V'.left.Etale)) (Sheaf.H.equiv₀ _ terminalIsTerminal
          (Etale.cohomologyMap k.left _ 0 (Etale.classOfSection V a))) =
      A.obj.map (Etale.overMapOverMapTerminalIso k).hom.op (A.obj.map k.op a) := by
  rw [Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap,
    Etale.classOfSection, AddEquiv.apply_symm_apply]
  change A.obj.map _ (A.obj.map _ a) = _
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 3
  apply MorphismProperty.Over.Hom.ext
  change _ ≫ (⊤_ V.left.Etale).hom = (⊤_ V'.left.Etale).hom ≫ k.left
  exact MorphismProperty.Over.w _

/-- A section of a presheaf which vanishes after restriction along an isomorphism vanishes. -/
lemma Etale.eq_zero_of_map_iso_hom_op {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {V₁ V₂ : Y.Etale} (e : V₁ ≅ V₂) (x : A.obj.obj (op V₂)) (hx : A.obj.map e.hom.op x = 0) :
    x = 0 := by
  have := congrArg (A.obj.map e.inv.op) hx
  rwa [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.inv_hom_id,
    op_id, Functor.map_id, ConcreteCategory.id_apply] at this

end Terminal

section Exactness

variable {V U : Scheme.{u}} (f : V ⟶ U) (hf : AlgebraicGeometry.Etale f)

/-- Restriction along an étale morphism is additive. -/
instance Etale.additive_localizationRestriction :
    (Etale.localizationRestriction AddCommGrpCat.{u + 1} f hf).Additive :=
  Functor.additive_of_iso (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf)

/-- Restriction along an étale morphism is exact. -/
lemma Etale.shortExact_map_localizationRestriction
    {S : ShortComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact) :
    (S.map (Etale.localizationRestriction AddCommGrpCat.{u + 1} f hf)).ShortExact := by
  have := preservesFiniteLimits_of_natIso
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf)
  have := preservesFiniteColimits_of_natIso
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf)
  exact hS.map_of_exact _

end Exactness

section DieLocally

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- Every class of the abelian cohomology of the restriction of `A` to `W ×_X Y`, for an
affine scheme `W` étale over `X`, dies on an étale cover of `W`. -/
def Etale.ClassesDieLocallyAb (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Prop :=
  ∀ (W : X.Etale), IsAffine W.left →
    ∀ ξ : Sheaf.H ((Etale.localizationRestriction AddCommGrpCat.{u + 1} _
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W).prop).obj A) n,
    ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g →
      Etale.cohomologyMap ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).map
        g).left _ n ξ = 0

/-- Every class of `Ext^n(h^* Λ[W], G) = H^n(W ×_X Y, G|)`, for an affine scheme `W` étale over
`X`, dies on an étale cover of `W`. -/
def Etale.ClassesDieLocally (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Prop :=
  ∀ (W : X.Etale), IsAffine W.left →
    ∀ β : Ext.{u + 1} ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) G n,
    ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g →
      (Ext.mk₀ ((h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ X).map g))).comp β
        (zero_add n) = 0

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules. -/
local notation "forget₂Sheaf" =>
  sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- The short exact sequence `0 ⟶ G ⟶ I ⟶ I / G ⟶ 0` for the chosen embedding of `G` into an
injective sheaf. -/
noncomputable abbrev Etale.injectiveShortComplex
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)

lemma Etale.shortExact_injectiveShortComplex
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.injectiveShortComplex Λ G).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- The dimension-shifting step on the side of sheaves of `Λ`-modules. -/
lemma Etale.classesDieLocally_succ (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (hC : Etale.ClassesDieLocally Λ h (cokernel (Injective.ι G)) n) :
    Etale.ClassesDieLocally Λ h G (n + 1) := by
  intro W hW β
  obtain ⟨γ, rfl⟩ := Ext.covariant_sequence_exact₁ _ (Etale.shortExact_injectiveShortComplex Λ G)
    β (Ext.eq_zero_of_injective _) rfl
  obtain ⟨S, hS, hz⟩ := hC W hW γ
  refine ⟨S, hS, fun W' g hg ↦ ?_⟩
  rw [← Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega), hz g hg, Ext.zero_comp]

/-- On a quasi-compact quasi-separated étale scheme `V'` over `V`, the restriction of the
underlying abelian sheaf of an injective sheaf of `Λ`-modules has no higher cohomology. -/
lemma Etale.subsingleton_H_upperStar_localizationRestriction_forget₂ (V : Y.Etale)
    (V' : V.left.Etale) [CompactSpace V'.left] [QuasiSeparatedSpace V'.left]
    (I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] (m : ℕ) :
    Subsingleton (Sheaf.H ((V'.hom)^*[AddCommGrpCat.{u + 1}].obj
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} V.hom V.prop).obj
        ((forget₂Sheaf).obj I))) (m + 1)) := by
  have hV : AlgebraicGeometry.Etale V.hom := V.prop
  have hV' : AlgebraicGeometry.Etale V'.hom := V'.prop
  have : Injective ((Etale.localizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).obj I) :=
    Injective.of_iso ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom
      V.prop).app I) (Etale.injective_upperStar_obj_of_etale Λ V.hom I)
  have : Injective ((V'.hom)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.localizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).obj I)) :=
    Etale.injective_upperStar_obj_of_etale Λ V'.hom _
  have := Scheme.subsingleton_H_forget₂_of_injective Λ V'.left _ m
  exact (Etale.injective_sheafHMap_of_isIso
    (Etale.upperStarForget₂Iso V' ((Etale.localizationRestriction (ModuleCat.{u + 1} Λ) V.hom
      V.prop).obj I)).hom (m + 1)).subsingleton


/-- The dimension-shifting step on the side of abelian sheaves: if the classes of degree `m + 2`
of `G` die locally, so do the classes of degree `m + 1` of `I / G`, as the underlying abelian
sheaf of the injective sheaf `I` has no cohomology in degree `m + 1` over the quasi-compact
quasi-separated schemes `W' ×_X Y`, `W'` affine. -/
lemma Etale.classesDieLocallyAb_cokernel [QuasiCompact h] [QuasiSeparated h]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (m : ℕ)
    (hG : Etale.ClassesDieLocallyAb h ((forget₂Sheaf).obj G) (m + 2)) :
    Etale.ClassesDieLocallyAb h ((forget₂Sheaf).obj (cokernel (Injective.ι G))) (m + 1) := by
  intro W hW γ
  let F := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h
  let R := Etale.localizationRestriction AddCommGrpCat.{u + 1} (F.obj W).hom (F.obj W).prop
  let SW := ((Etale.injectiveShortComplex Λ G).map forget₂Sheaf).map R
  have hSW : SW.ShortExact := Etale.shortExact_map_localizationRestriction _ _
    (Etale.shortExact_map_forget₂ Λ (Etale.shortExact_injectiveShortComplex Λ G))
  obtain ⟨S, hS, hz⟩ := hG W hW (Sheaf.H.δSucc hSW (m + 1) γ)
  -- the class dies on the members of `S` with affine source
  have key : ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g → IsAffine W'.left →
      Etale.cohomologyMap (F.map g).left _ (m + 1) γ = 0 := by
    intro W' g hg hW'
    have h₁ := hz g hg
    rw [Sheaf.H.δSucc_apply, Etale.cohomologyMap_comp_extClass] at h₁
    obtain ⟨y, hy⟩ := (Sheaf.H.exact_map_δSucc
      (hSW.map_of_exact ((F.map g).left)^*[AddCommGrpCat.{u + 1}]) (m + 1) _).1 h₁
    obtain ⟨_, _⟩ := Etale.compactSpace_and_quasiSeparatedSpace_pullback h W'
    have : Subsingleton (Sheaf.H (((F.map g).left)^*[AddCommGrpCat.{u + 1}].obj SW.X₂)
        (m + 1)) :=
      Etale.subsingleton_H_upperStar_localizationRestriction_forget₂ Λ (F.obj W)
        (MorphismProperty.Over.mk ⊤ (F.map g).left inferInstance) (Injective.under G) m
    rw [← hy, Subsingleton.elim y 0, map_zero]
  refine ⟨⟨fun W' g ↦ Etale.cohomologyMap (F.map g).left _ (m + 1) γ = 0,
    fun {W' W''} g hg k ↦ ?_⟩, ?_, fun W' g hg ↦ hg⟩
  · change Etale.cohomologyMap (F.map (k ≫ g)).left _ (m + 1) γ = 0
    rw [Functor.map_comp]
    exact Etale.cohomologyMap_comp_eq_zero (F.map k).left (F.map g).left _ _ _ hg
  · refine X.smallEtaleTopology.transitive hS _ fun W' g hg ↦ ?_
    refine X.smallEtaleTopology.superset_covering ?_
      (Functor.is_cover_of_isCoverDense (Scheme.AffineEtale.Spec X) X.smallEtaleTopology W')
    rintro W'' k ⟨⟨U, k₁, k₂, rfl⟩⟩
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
      rw [Scheme.AffineEtale.Spec_obj_left]; infer_instance
    change Etale.cohomologyMap (F.map ((k₁ ≫ k₂) ≫ g)).left _ (m + 1) γ = 0
    rw [Category.assoc, Functor.map_comp]
    exact Etale.cohomologyMap_comp_eq_zero (F.map k₁).left (F.map (k₂ ≫ g)).left _ _ _
      (key _ (S.downward_closed hg k₂) this)

/-- In degree `0` the classes of `G` are the sections of `G` over `W ×_X Y`, whose restrictions
are the pullbacks of the corresponding abelian classes. -/
lemma Etale.classesDieLocally_zero (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : Etale.ClassesDieLocallyAb h ((forget₂Sheaf).obj G) 0) :
    Etale.ClassesDieLocally Λ h G 0 := by
  intro W hW β
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 β
  let F := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h
  obtain ⟨S, hS, hz⟩ := hG W hW (Etale.classOfSection (F.obj W) (A := (forget₂Sheaf).obj G)
    (Etale.upperStarFreeSheafHomEquivSections Λ h W G s))
  refine ⟨S, hS, fun W' g hg ↦ ?_⟩
  have h₁ := Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap_classOfSection
    (F.map g) (A := (forget₂Sheaf).obj G) (Etale.upperStarFreeSheafHomEquivSections Λ h W G s)
  rw [hz g hg, map_zero, map_zero] at h₁
  have h₂ := Etale.eq_zero_of_map_iso_hom_op _ _ h₁.symm
  change G.obj.map (F.map g).op (Etale.upperStarFreeSheafHomEquivSections Λ h W G s) = 0 at h₂
  have h₃ : (h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ X).map g) ≫ s = 0 :=
    (Etale.upperStarFreeSheafHomEquivSections Λ h W' G).injective (by
      rw [Etale.upperStarFreeSheafHomEquivSections_map, h₂,
        Etale.upperStarFreeSheafHomEquivSections_zero])
  rw [Ext.mk₀_comp_mk₀, h₃, Ext.mk₀_zero]

/-- In degree `1` the classes of `G` are the sections of `I / G` over `W ×_X Y` modulo those of
the injective sheaf `I`, and a class dies exactly when the section lifts to `I`; on the abelian
side the obstruction to lifting is the connecting map. -/
lemma Etale.classesDieLocally_one (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : Etale.ClassesDieLocallyAb h ((forget₂Sheaf).obj G) 1) :
    Etale.ClassesDieLocally Λ h G 1 := by
  intro W hW β
  have hS := Etale.shortExact_injectiveShortComplex Λ G
  obtain ⟨γ, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS β (Ext.eq_zero_of_injective _) rfl
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 γ
  let F := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h
  let R := Etale.localizationRestriction AddCommGrpCat.{u + 1} (F.obj W).hom (F.obj W).prop
  let SW := ((Etale.injectiveShortComplex Λ G).map forget₂Sheaf).map R
  have hSW : SW.ShortExact := Etale.shortExact_map_localizationRestriction _ _
    (Etale.shortExact_map_forget₂ Λ hS)
  let C := cokernel (Injective.ι G)
  let π := cokernel.π (Injective.ι G)
  let c := Etale.upperStarFreeSheafHomEquivSections Λ h W C s
  obtain ⟨S, hS', hz⟩ := hG W hW
    (Sheaf.H.δSucc hSW 0 (Etale.classOfSection (F.obj W) (A := (forget₂Sheaf).obj C) c))
  refine ⟨S, hS', fun W' g hg ↦ ?_⟩
  have h₁ := hz g hg
  rw [Sheaf.H.δSucc_apply, Etale.cohomologyMap_comp_extClass] at h₁
  obtain ⟨y, hy⟩ := (Sheaf.H.exact_map_δSucc
    (hSW.map_of_exact ((F.map g).left)^*[AddCommGrpCat.{u + 1}]) 0 _).1 h₁
  let ι := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (F.map g).left
    inferInstance
  let e := Etale.overMapOverMapTerminalIso (F.map g)
  have h₂ := Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap_classOfSection
    (F.map g) (A := (forget₂Sheaf).obj C) c
  rw [← hy, ← Sheaf.H.equiv₀_naturality] at h₂
  let t := (ι.hom.app SW.X₂).hom.app (op (⊤_ (F.obj W').left.Etale))
    (Sheaf.H.equiv₀ _ terminalIsTerminal y)
  have h₃ := ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op (⊤_ (F.obj W').left.Etale))) (ι.hom.naturality SW.g))
    (Sheaf.H.equiv₀ _ terminalIsTerminal y)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h₃
  have h₄ : C.obj.map e.hom.op (C.obj.map (F.map g).op c) = π.hom.app _ t :=
    h₂.symm.trans h₃
  let t' := (Injective.under G).obj.map e.inv.op t
  have h₅ : C.obj.map (F.map g).op c = π.hom.app _ t' := by
    change _ = π.hom.app _ ((Injective.under G).obj.map e.inv.op t)
    rw [← NatTrans.naturality_apply π.hom, ← h₄, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, e.inv_hom_id, op_id, Functor.map_id,
      ConcreteCategory.id_apply]
  have h₆ : (h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ X).map g) ≫ s =
      (Etale.upperStarFreeSheafHomEquivSections Λ h W' _).symm t' ≫ π :=
    (Etale.upperStarFreeSheafHomEquivSections Λ h W' C).injective (by
      rw [Etale.upperStarFreeSheafHomEquivSections_map,
        Etale.upperStarFreeSheafHomEquivSections_comp, Equiv.apply_symm_apply, h₅])
  rw [Ext.mk₀_comp_mk₀_assoc, h₆, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  change (Ext.mk₀ _).comp ((Ext.mk₀ (Etale.injectiveShortComplex Λ G).g).comp hS.extClass
    (zero_add 1)) (zero_add 1) = 0
  rw [hS.comp_extClass, Ext.comp_zero]

/-- **Classes of sheaves of `Λ`-modules die locally when their abelian classes do.** Let
`h : Y ⟶ X` be quasi-compact and quasi-separated and `G` an étale sheaf of `Λ`-modules on `Y`.
If every class of degree `n` of the underlying abelian sheaf of `G` restricted to `W ×_X Y`,
for `W` affine étale over `X`, dies on an étale cover of `W`, then so does every class of
`H^n(W ×_X Y, G|) = Ext^n(h^* Λ[W], G)`. -/
theorem Etale.classesDieLocally_of_classesDieLocallyAb [QuasiCompact h] [QuasiSeparated h]
    (n : ℕ) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : Etale.ClassesDieLocallyAb h ((forget₂Sheaf).obj G) n) :
    Etale.ClassesDieLocally Λ h G n := by
  induction n generalizing G with
  | zero => exact Etale.classesDieLocally_zero Λ h G hG
  | succ n ih =>
    cases n with
    | zero => exact Etale.classesDieLocally_one Λ h G hG
    | succ m =>
      exact Etale.classesDieLocally_succ Λ h G (m + 1)
        (ih _ (Etale.classesDieLocallyAb_cokernel Λ h G m hG))

end DieLocally


section Vanishing

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- **Higher direct images vanish when their classes die locally.** For `h : Y ⟶ X` and an
étale sheaf `F` of `Λ`-modules on `Y`, `R^q h_* F = 0` as soon as every class of
`H^q(W ×_X Y, F|)`, for `W` affine étale over `X`, dies on an étale cover of `W`: the sheaf
`R^q h_* F` is locally generated by these classes
(`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`), and the affine
étale `X`-schemes are cover-dense. -/
theorem Etale.isZero_higherDirectImage_of_forall_isAffine_exists (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : ∀ W : X.Etale, IsAffine W.left → ∀ t : (Etale.higherDirectImagePresheaf Λ h q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op W),
      ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g →
        (Etale.higherDirectImagePresheaf Λ h q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).map g.op t = 0) :
    IsZero (Etale.higherDirectImage Λ h q F) := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let G := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (Etale.higherDirectImage Λ h q F)
  let GT := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  let φ := Etale.higherDirectImagePresheafToSheaf Λ h q K
  obtain ⟨-, hφ⟩ := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ h q K
  -- over an affine `U` the classes coming from the presheaf vanish, as they vanish locally
  have h₀ (U : X.Etale) (hU : IsAffine U.left)
      (t : (Etale.higherDirectImagePresheaf Λ h q K).obj (op U)) : φ.app (op U) t = 0 := by
    obtain ⟨S, hS, hz⟩ := H U hU t
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 GT.property _ hS).isSeparatedFor.ext
      fun V f hf ↦ ?_
    change G.obj.map f.op (φ.app _ t) = G.obj.map f.op 0
    have hn := ConcreteCategory.congr_hom (φ.naturality f.op) t
    simp only [ConcreteCategory.comp_apply] at hn
    rw [map_zero]
    erw [← hn, hz f hf, map_zero]
  -- hence all of them vanish, the affine étale schemes being cover-dense
  have h₁ (U : X.Etale) (t : (Etale.higherDirectImagePresheaf Λ h q K).obj (op U)) :
      φ.app (op U) t = 0 := by
    refine Functor.IsCoverDense.ext (Scheme.AffineEtale.Spec X) GT U fun Z f ↦ ?_
    change G.obj.map f.op (φ.app _ t) = G.obj.map f.op 0
    have hn := ConcreteCategory.congr_hom (φ.naturality f.op) t
    simp only [ConcreteCategory.comp_apply] at hn
    rw [map_zero]
    erw [← hn]
    exact h₀ _ (by
      dsimp [Scheme.AffineEtale.Spec, MorphismProperty.CostructuredArrow.toOver]
      exact (inferInstance : IsAffine (Spec _))) _
  -- and every section vanishes, being locally such a class
  have h₂ (U : X.Etale) (s : G.obj.obj (op U)) : s = 0 := by
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 GT.property _
      (hφ.imageSieve_mem s)).isSeparatedFor.ext fun V f hf ↦ ?_
    obtain ⟨t, ht⟩ := hf
    change G.obj.map f.op s = G.obj.map f.op 0
    rw [map_zero]
    exact ht.symm.trans (h₁ _ _)
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact h₂ U.unop x

end Vanishing

/-- Precomposing a morphism `X[0] ⟶ Y[0][n]` of the bounded below derived category with the
image of `a : X' ⟶ X` corresponds to composing the `Ext`-class with `a`. -/
lemma _root_.DerivedCategory.Plus.singleFunctorHomEquivExt_singleFunctor_map_comp {C : Type*}
    [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C] {X X' Y : C} (a : X' ⟶ X)
    {n : ℕ} (t : (singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    singleFunctorHomEquivExt X' Y n ((singleFunctor C 0).map a ≫ t) =
      (Ext.mk₀ a).comp (singleFunctorHomEquivExt X Y n t) (zero_add n) := by
  ext
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  simp [singleFunctorHomEquivExt]
  rfl

section Constant

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- On the base change `W ×_X Y` of an étale `W ⟶ X`, every class of the constant sheaf with
value `B` dies on an étale cover of `W`. -/
def Etale.ConstantClassesDieLocally (W : X.Etale) (q : ℕ) (B : AddCommGrpCat.{u + 1}) : Prop :=
  ∀ η : Sheaf.H ((constantSheaf ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
    h).obj W).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B) q,
    ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g →
      Etale.cohomologyMap ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).map
        g).left _ q η = 0

/-- Finitely many properties of morphisms into `W`, each holding on a covering sieve, hold
simultaneously on a covering sieve. -/
lemma Etale.exists_sieve_forall_mem_finset {X : Scheme.{u}} {W : X.Etale} {κ : Type*}
    (s : Finset κ) (P : κ → ∀ ⦃W' : X.Etale⦄, (W' ⟶ W) → Prop)
    (hP : ∀ k, ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W),
      S g → P k g) :
    ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧ ∀ ⦃W' : X.Etale⦄ (g : W' ⟶ W), S g →
      ∀ k ∈ s, P k g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, X.smallEtaleTopology.top_mem W, fun _ _ _ _ hk ↦ by simp at hk⟩
  | insert k s _ ih =>
    obtain ⟨S₁, hS₁, h₁⟩ := hP k
    obtain ⟨S₂, hS₂, h₂⟩ := ih
    refine ⟨S₁ ⊓ S₂, X.smallEtaleTopology.intersection_covering hS₁ hS₂,
      fun W' g hg k' hk' ↦ ?_⟩
    rcases Finset.mem_insert.1 hk' with rfl | hk'
    · exact h₁ g hg.1
    · exact h₂ g hg.2 k' hk'

/-- If the identity of `B` is a finite sum of morphisms factoring through groups `Z k` whose
constant classes die locally, the constant classes with value `B` die locally. -/
lemma Etale.constantClassesDieLocally_of_sum_eq_id {W : X.Etale} {q : ℕ}
    {B : AddCommGrpCat.{u + 1}} {κ : Type} [Fintype κ] (Z : κ → AddCommGrpCat.{u + 1})
    (π : ∀ k, B ⟶ Z k) (ι : ∀ k, Z k ⟶ B) (hsum : ∑ k, π k ≫ ι k = 𝟙 B)
    (hZ : ∀ k, Etale.ConstantClassesDieLocally h W q (Z k)) :
    Etale.ConstantClassesDieLocally h W q B := by
  intro η
  let c := constantSheaf ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
    h).obj W).left.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hη : η = ∑ k, Sheaf.H.map (c.map (ι k)) q (Sheaf.H.map (c.map (π k)) q η) := by
    have hc : ∑ k, c.map (π k) ≫ c.map (ι k) = 𝟙 _ := by
      simp only [← Functor.map_comp, ← Functor.map_sum, hsum, Functor.map_id]
    simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      ← Ext.comp_sum, ← Ext.mk₀_sum, hc, Ext.comp_mk₀_id]
  choose S hS hz using fun k ↦ hZ k (Sheaf.H.map (c.map (π k)) q η)
  obtain ⟨S', hS', hz'⟩ := Etale.exists_sieve_forall_mem_finset Finset.univ
    (fun k W' g ↦ Etale.cohomologyMap ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale
      ⊤ h).map g).left _ q (Sheaf.H.map (c.map (π k)) q η) = 0) (fun k ↦ ⟨S k, hS k, hz k⟩)
  refine ⟨S', hS', fun W' g hg ↦ ?_⟩
  rw [hη, map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [Etale.cohomologyMap_map, hz' g hg k (Finset.mem_univ _), map_zero]

end Constant


section FiniteGeneration

variable {n : ℕ} {ι : Type} [Fintype ι] (p e : ι → ℕ)

/-- The orders of the cyclic factors of `(Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)`, the free factors
having order `0`. -/
def Etale.cyclicFactorOrder : Fin n ⊕ ι → ℕ :=
  Sum.elim (fun _ ↦ 0) (fun i ↦ p i ^ e i)

/-- The projections of `(Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)` to its cyclic factors. -/
noncomputable def Etale.cyclicFactorProj :
    ∀ k : Fin n ⊕ ι, ((Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) →+
      ZMod (Etale.cyclicFactorOrder p e k)
  | .inl j => (Finsupp.applyAddHom j).comp (AddMonoidHom.fst _ _)
  | .inr i => (DFinsupp.evalAddMonoidHom (β := fun i ↦ ZMod (p i ^ e i)) i).comp
      (AddMonoidHom.snd _ _)

/-- The inclusions of the cyclic factors of `(Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)`. -/
noncomputable def Etale.cyclicFactorIncl [DecidableEq ι] :
    ∀ k : Fin n ⊕ ι, ZMod (Etale.cyclicFactorOrder p e k) →+
      ((Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i))
  | .inl j => (AddMonoidHom.inl _ _).comp (Finsupp.singleAddHom j)
  | .inr i => (AddMonoidHom.inr _ _).comp (DirectSum.of (fun i ↦ ZMod (p i ^ e i)) i)

lemma Etale.cyclicFactorProj_cyclicFactorIncl [DecidableEq ι] (k : Fin n ⊕ ι)
    (z : ZMod (Etale.cyclicFactorOrder p e k)) :
    Etale.cyclicFactorProj p e k (Etale.cyclicFactorIncl p e k z) = z := by
  cases k with
  | inl j => simp [Etale.cyclicFactorProj, Etale.cyclicFactorIncl]
  | inr i =>
    simp only [Etale.cyclicFactorProj, Etale.cyclicFactorIncl, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.inr_apply, AddMonoidHom.snd_apply]
    exact DirectSum.of_eq_same i z

lemma Etale.sum_cyclicFactorIncl_cyclicFactorProj [DecidableEq ι]
    (x : (Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) :
    ∑ k, Etale.cyclicFactorIncl p e k (Etale.cyclicFactorProj p e k x) = x := by
  rw [Fintype.sum_sum_type]
  ext1
  · simp only [Prod.fst_add, Prod.fst_sum, Etale.cyclicFactorIncl, Etale.cyclicFactorProj,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
      AddMonoidHom.inr_apply, Finsupp.singleAddHom_apply, Finsupp.applyAddHom_apply,
      AddMonoidHom.fst_apply, Finset.sum_const_zero, add_zero]
    exact Finsupp.univ_sum_single x.1
  · simp only [Prod.snd_add, Prod.snd_sum, Etale.cyclicFactorIncl, Etale.cyclicFactorProj,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
      AddMonoidHom.inr_apply, AddMonoidHom.snd_apply, Finset.sum_const_zero, zero_add]
    exact DirectSum.sum_univ_of x.2

end FiniteGeneration

section Constant

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- If the constant classes with value `ℤ/e` die locally for every `e ∣ d`, so do the constant
classes with value a finitely generated abelian group killed by `d`: such a group is a finite
direct sum of cyclic groups `ℤ/e` with `e ∣ d` (and `e = 0` only if `d = 0`). -/
lemma Etale.constantClassesDieLocally_of_addGroupFG {W : X.Etale} {q d : ℕ}
    (hZ : ∀ e : ℕ, e ∣ d →
      Etale.ConstantClassesDieLocally h W q (AddCommGrpCat.of (ULift.{u + 1} (ZMod e))))
    (M : Type (u + 1)) [AddCommGroup M] [AddGroup.FG M] (hM : ∀ m : M, d • m = 0) :
    Etale.ConstantClassesDieLocally h W q (AddCommGrpCat.of M) := by
  classical
  obtain ⟨n, ι, _, p, -, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  let π (k : Fin n ⊕ ι) : AddCommGrpCat.of M ⟶
      AddCommGrpCat.of (ULift.{u + 1} (ZMod (Etale.cyclicFactorOrder p e k))) :=
    AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((Etale.cyclicFactorProj p e k).comp φ.toAddMonoidHom))
  let ι' (k : Fin n ⊕ ι) :
      AddCommGrpCat.of (ULift.{u + 1} (ZMod (Etale.cyclicFactorOrder p e k))) ⟶
        AddCommGrpCat.of M :=
    AddCommGrpCat.ofHom (φ.symm.toAddMonoidHom.comp
      ((Etale.cyclicFactorIncl p e k).comp AddEquiv.ulift.toAddMonoidHom))
  have hπι (k : Fin n ⊕ ι) (z) : π k (ι' k z) = z := by
    simp [π, ι', Etale.cyclicFactorProj_cyclicFactorIncl]
  refine Etale.constantClassesDieLocally_of_sum_eq_id h _ π ι' ?_ fun k ↦ hZ _ ?_
  · ext m
    simp only [AddCommGrpCat.hom_sum, AddCommGrpCat.hom_comp, AddMonoidHom.finset_sum_apply,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply, AddCommGrpCat.hom_ofHom,
      AddMonoidHom.coe_comp, Function.comp_apply, π, ι']
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply,
      ← map_sum, Etale.sum_cyclicFactorIncl_cyclicFactorProj, AddEquiv.symm_apply_apply]
  · rw [← ZMod.natCast_eq_zero_iff, ← nsmul_one]
    have := congrArg (π k) (hM (ι' k (ULift.up 1)))
    rw [map_nsmul, hπι, map_zero] at this
    exact congrArg ULift.down this

/-- If the constant classes with value every finitely generated subgroup of `A` die locally on
the quasi-compact quasi-separated scheme `W ×_X Y`, so do the constant classes with value `A`:
cohomology commutes with the filtered colimit of these subgroups. -/
lemma Etale.constantClassesDieLocally_of_forall_fg [QuasiCompact h] [QuasiSeparated h]
    {W : X.Etale} [IsAffine W.left] {q : ℕ} (A : AddCommGrpCat.{u + 1})
    (hA : ∀ s : Finset A, Etale.ConstantClassesDieLocally h W q
      (AddCommGrpCat.of (AddSubgroup.closure (s : Set A)))) :
    Etale.ConstantClassesDieLocally h W q A := by
  intro η
  obtain ⟨_, _⟩ := Etale.compactSpace_and_quasiSeparatedSpace_pullback h W
  let D : Finset A ⥤ AddCommGrpCat.{u + 1} :=
    { obj s := AddCommGrpCat.of (AddSubgroup.closure (s : Set A))
      map {s t} f := AddCommGrpCat.ofHom (AddSubgroup.inclusion
        (AddSubgroup.closure_mono (Finset.coe_subset.2 (leOfHom f))))
      map_id _ := rfl
      map_comp _ _ := rfl }
  let c : Cocone D :=
    { pt := A
      ι := { app s := AddCommGrpCat.ofHom (AddSubgroup.closure (s : Set A)).subtype } }
  have hc : IsColimit c := by
    refine isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1})
      (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun s x y hxy ↦ ?_))
    · exact ⟨{x}, ⟨x, AddSubgroup.subset_closure (by simp)⟩, rfl⟩
    · exact ⟨s, 𝟙 s, Subtype.ext hxy⟩
  let C := constantSheaf ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
    h).obj W).left.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfShape (Finset A) C :=
    (constantSheafAdj _ AddCommGrpCat.{u + 1} terminalIsTerminal).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  obtain ⟨s, y, hy⟩ := (Scheme.H_map_isColimit_of_isFiltered_of_large _
    (isColimitOfPreserves C hc) q).1 η
  obtain ⟨S, hS, hz⟩ := hA s y
  refine ⟨S, hS, fun W' g hg ↦ ?_⟩
  rw [← hy, Etale.cohomologyMap_map, hz g hg, map_zero]

end Constant


section Constant

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- The hypothesis of
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`, written
on the base changes `W ×_X Y` of the affine étale `W ⟶ X`: the constant classes with value `ℤ/e`
die locally. The hypothesis is stated on `Y ×_X W`, which is identified with `W ×_X Y` by
`CategoryTheory.Limits.pullbackSymmetry`. -/
lemma Etale.constantClassesDieLocally_zmod {q e : ℕ}
    (H : ∀ ⦃U : Scheme.{u}⦄ (u : U ⟶ X) [AlgebraicGeometry.Etale u] [IsAffine U]
      (ξ : Sheaf.H ((pullback h u).constantZMod e) q),
      ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U),
        (∀ i, AlgebraicGeometry.Etale (v i)) ∧ (∀ x : U, ∃ i y, (v i).base y = x) ∧
        ∀ i, Etale.cohomologyMap (pullback.map h (v i ≫ u) h u (𝟙 Y) (v i) (𝟙 X) (by simp)
          (by simp)) _ q ξ = 0)
    (W : X.Etale) [IsAffine W.left] :
    Etale.ConstantClassesDieLocally h W q (AddCommGrpCat.of (ULift.{u + 1} (ZMod e))) := by
  intro η
  have : AlgebraicGeometry.Etale W.hom := W.prop
  let σ := pullbackSymmetry h W.hom
  obtain ⟨ι, V, v, hv, hsurj, hkill⟩ := H W.hom (Sheaf.H.map
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} σ.hom).hom.app _) q
    (Etale.cohomologyMap σ.hom _ q η))
  have := hv
  refine ⟨Sieve.ofArrows (fun i ↦ (MorphismProperty.Over.mk ⊤ (v i ≫ W.hom)
    (inferInstance : AlgebraicGeometry.Etale (v i ≫ W.hom)) : X.Etale))
    (fun i ↦ MorphismProperty.Over.homMk (v i) rfl), ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := hsurj x
    exact Set.mem_iUnion.2 ⟨i, y, rfl⟩
  · rintro W' g ⟨W'', k, _, ⟨i⟩, rfl⟩
    let F := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h
    change Etale.cohomologyMap (F.map (k ≫ _)).left _ q η = 0
    rw [Functor.map_comp]
    refine Etale.cohomologyMap_comp_eq_zero (F.map k).left _ _ _ _ ?_
    have h₁ := hkill i
    rw [Etale.cohomologyMap_map_eq_zero_iff, Etale.cohomologyMap_cohomologyMap_eq_zero_iff_comp]
      at h₁
    have h₂ := Etale.cohomologyMap_comp_eq_zero (pullbackSymmetry h (v i ≫ W.hom)).inv _ _ _ _ h₁
    convert h₂ using 2
    apply pullback.hom_ext <;> simp [σ, F]

/-- The underlying abelian sheaf of the constant sheaf `Λ/dΛ`, restricted to `W ×_X Y`, is the
constant sheaf with value the abelian group `Λ/dΛ`. -/
noncomputable def Etale.localizationRestrictionForget₂ConstantModSheafIso (d : ℕ)
    (W : X.Etale) :
    (Etale.localizationRestriction AddCommGrpCat.{u + 1} _
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W).prop).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ Y d)) ≅
      (constantSheaf ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
        h).obj W).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)))) :=
  ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} _
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W).prop).app _).symm ≪≫
    (((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj
      W).hom)^*[AddCommGrpCat.{u + 1}].mapIso
      ((constantCommuteCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app _) ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} _).app _

end Constant

/-- Blueprint `sbc-lem-higher-direct-image-presheaf`, in the vanishing form used for constant
coefficients: Higher direct image as a sheafified cohomology presheaf.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated, let `d : ℕ` and `q : ℕ`. Suppose that for
every `e ∣ d`, every affine scheme `U` étale over `X` and every class
`ξ ∈ H^q(Y ×_X U, ℤ/e)` there is an étale covering `{V i ⟶ U}` such that `ξ` dies after
pullback to every `Y ×_X V i`. Then `R^q h_* (Λ/dΛ) = 0`.

By Stacks `03Q8` the sheaf `R^q h_* (Λ/dΛ)` is the sheafification of `U ↦ H^q(U ×_X Y, Λ/dΛ)`
on `X_ét` (`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`), and
the affine `U` form a basis of `X_ét`, so it suffices that every class of
`H^q(U ×_X Y, Λ/dΛ)`, `U` affine, dies locally on `U`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isAffine_exists`). These groups
are computed with sheaves of `Λ`-modules; their classes die locally as soon as those of the
underlying abelian sheaf do (`AlgebraicGeometry.Etale.classesDieLocally_of_classesDieLocallyAb`).
The underlying abelian group of `Λ/dΛ` is the filtered colimit of its finitely generated
subgroups, and cohomology of the quasi-compact quasi-separated scheme `U ×_X Y` commutes with
filtered colimits (`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_of_large`); a
finitely generated subgroup is a finite direct sum of cyclic groups `ℤ/e` with `e ∣ d`, for
which the classes die locally by hypothesis. -/
@[stacks 03Q8]
theorem Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (d q : ℕ)
    (H : ∀ e : ℕ, e ∣ d → ∀ ⦃U : Scheme.{u}⦄ (u : U ⟶ X) [Etale u] [IsAffine U]
      (ξ : Sheaf.H ((pullback h u).constantZMod e) q),
      ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U), (∀ i, Etale (v i)) ∧
        (∀ x : U, ∃ i y, (v i).base y = x) ∧
        ∀ i, Etale.cohomologyMap (pullback.map h (v i ≫ u) h u (𝟙 Y) (v i) (𝟙 X) (by simp)
          (by simp)) _ q ξ = 0) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  -- the classes of the underlying abelian sheaf die locally
  have hAb : Etale.ClassesDieLocallyAb h ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj (Etale.constantModSheaf Λ Y d)) q := by
    intro W hW ξ
    let A := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)))
    have hA : ∀ a : A, d • a = 0 := by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(d : Λ)}) a
      change d • Ideal.Quotient.mk _ x = 0
      rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hZ (e : ℕ) (he : e ∣ d) := Etale.constantClassesDieLocally_zmod h (H e he) W
    obtain ⟨S, hS, hz⟩ := Etale.constantClassesDieLocally_of_forall_fg h A (fun s ↦
      Etale.constantClassesDieLocally_of_addGroupFG h hZ _ (fun m ↦ Subtype.ext (hA m)))
      (Sheaf.H.map (Etale.localizationRestrictionForget₂ConstantModSheafIso Λ h d W).hom q ξ)
    exact ⟨S, hS, fun W' g hg ↦ (Etale.cohomologyMap_map_eq_zero_iff _ _ _ _).1 (hz g hg)⟩
  refine Etale.isZero_higherDirectImage_of_forall_isAffine_exists Λ h q _ fun W hW t ↦ ?_
  obtain ⟨S, hS, hz⟩ := Etale.classesDieLocally_of_classesDieLocallyAb Λ h q _ hAb W hW
    (DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1} _ _ q t)
  refine ⟨S, hS, fun W' g hg ↦ (DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    _ _ q).injective ?_⟩
  have h₀ := DerivedCategory.Plus.singleFunctorHomEquivExt_singleFunctor_map_comp
    ((h)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ X).map g)) t
  have h₁ := DerivedCategory.Plus.singleFunctorHomEquivExt_singleFunctor_map_comp
    (0 : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W') ⟶ _) t
  rw [Functor.map_zero, Limits.zero_comp, Ext.mk₀_zero, Ext.zero_comp] at h₁
  exact h₀.trans ((hz g hg).trans h₁.symm)

end AlgebraicGeometry
