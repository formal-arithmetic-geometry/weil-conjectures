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

end DieLocally

end AlgebraicGeometry
