/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# The Galois category axioms for finite étale schemes

Let `Y` be a scheme. We verify the axioms of a (pre-)Galois category for the category
`FÉt(Y)` of finite étale `Y`-schemes, and, for connected `Y` and a geometric point `s`, the axioms
of a fibre functor for the geometric fibre functor `F_s`
(blueprint `lem-fet-finite-limits`, `lem-fet-galois-category`).

* Finite limits are computed in schemes.
* Finite coproducts are disjoint unions.
* The quotient of a finite étale `Y`-scheme `P` by a finite group `G` is glued from the spectra
  of the rings of invariants over the affine opens of `Y`
  (`AlgebraicGeometry.Scheme.hasColimitsOfShape_singleObj`); it is finite étale by
  `AlgHom.finite_and_etale_fixedPoints`, and its geometric points are the `G`-orbits of the
  geometric points of `P` (`AlgHom.surjective_comap_fixedPoints_val_and_iff`).
* A monomorphism is an open and closed immersion, hence the inclusion of a direct summand.
* The fibre functor is conservative: a morphism inducing a bijection on geometric fibres is a
  surjective monomorphism, by a clopen-image argument over the connected base.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-- The category of affine `Y`-schemes. -/
local instance :
    Category (MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y) :=
  MorphismProperty.Comma.instCategory _ _ _ _ _

local instance : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

local instance : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).HasOfPostcompProperty
    (@IsFinite ⊓ @Etale) := by
  refine ⟨fun {X Y Z} f g hg hfg ↦ ?_⟩
  have := hg.1; have := hg.2; have := hfg.1; have := hfg.2
  exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

variable (Y) in
/-- A finite étale `Y`-scheme as an affine `Y`-scheme. -/
@[simps]
noncomputable def toAffineOver :
    Y.FiniteEtale ⥤ MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y where
  obj P := MorphismProperty.Over.mk ⊤ P.obj.hom
    (by have : IsFinite P.obj.hom := P.property; infer_instance)
  map f := MorphismProperty.Over.homMk f.hom.left (hom_left_comp f) trivial

/-- The functor `FÉt(Y) ⥤ AffOver(Y)` is fully faithful. -/
noncomputable def toAffineOverFullyFaithful : (toAffineOver Y).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := hom_ext rfl

instance : (toAffineOver Y).Full := toAffineOverFullyFaithful.full
instance : (toAffineOver Y).Faithful := toAffineOverFullyFaithful.faithful

/-- Two open immersions with disjoint images covering the target exhibit it as a coproduct. -/
lemma _root_.AlgebraicGeometry.isIso_coprodDesc_of_isOpenImmersion {X X' Z : Scheme.{u}}
    (a : X ⟶ Z) (b : X' ⟶ Z) [IsOpenImmersion a] [IsOpenImmersion b]
    (hdisj : ∀ x x', a x ≠ b x') (hcov : ∀ z, z ∈ Set.range a ∨ z ∈ Set.range b) :
    IsIso (coprod.desc a b) := by
  have hinl (x : X) : coprod.desc a b ((coprod.inl : X ⟶ X ⨿ X') x) = a x := by
    rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
  have hinr (x : X') : coprod.desc a b ((coprod.inr : X' ⟶ X ⨿ X') x) = b x := by
    rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
  have hpt (p : (X ⨿ X' : Scheme.{u})) :
      (∃ x, p = (coprod.inl : X ⟶ X ⨿ X') x) ∨ ∃ x', p = (coprod.inr : X' ⟶ X ⨿ X') x' := by
    obtain ⟨(x | x), rfl⟩ := (coprodMk X X').surjective p
    · exact .inl ⟨x, coprodMk_inl X X' x⟩
    · exact .inr ⟨x, coprodMk_inr X X' x⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨IsOpenImmersion.iff_isIso_stalkMap.mpr ⟨?_, fun p ↦ ?_⟩, ⟨fun z ↦ ?_⟩⟩
  · refine .of_continuous_injective_isOpenMap (coprod.desc a b).continuous ?_ ?_
    · intro p q hpq
      rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases hpt q with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [hinl, hinl] at hpq; rw [a.isOpenEmbedding.injective hpq]
      · rw [hinl, hinr] at hpq; exact (hdisj _ _ hpq).elim
      · rw [hinr, hinl] at hpq; exact (hdisj _ _ hpq.symm).elim
      · rw [hinr, hinr] at hpq; rw [b.isOpenEmbedding.injective hpq]
    · intro U hU
      have : (coprod.desc a b) '' U =
          a '' ((coprod.inl : X ⟶ X ⨿ X') ⁻¹' U) ∪ b '' ((coprod.inr : X' ⟶ X ⨿ X') ⁻¹' U) := by
        ext z
        constructor
        · rintro ⟨p, hp, rfl⟩
          rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩
          · exact .inl ⟨x, hp, (hinl x).symm⟩
          · exact .inr ⟨x, hp, (hinr x).symm⟩
        · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
          · exact ⟨_, hx, hinl x⟩
          · exact ⟨_, hx, hinr x⟩
      rw [this]
      exact (a.isOpenEmbedding.isOpenMap _ (hU.preimage (coprod.inl : X ⟶ X ⨿ X').continuous)).union
        (b.isOpenEmbedding.isOpenMap _ (hU.preimage (coprod.inr : X' ⟶ X ⨿ X').continuous))
  · rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have h := Scheme.Hom.stalkMap_comp (coprod.inl : X ⟶ X ⨿ X') (coprod.desc a b) x
      rw [Scheme.Hom.stalkMap_congr_hom _ _ (coprod.inl_desc a b) x] at h
      have : IsIso ((coprod.desc a b).stalkMap ((coprod.inl : X ⟶ X ⨿ X') x) ≫
          (coprod.inl : X ⟶ X ⨿ X').stalkMap x) := by rw [← h]; infer_instance
      exact IsIso.of_isIso_comp_right _ ((coprod.inl : X ⟶ X ⨿ X').stalkMap x)
    · have h := Scheme.Hom.stalkMap_comp (coprod.inr : X' ⟶ X ⨿ X') (coprod.desc a b) x
      rw [Scheme.Hom.stalkMap_congr_hom _ _ (coprod.inr_desc a b) x] at h
      have : IsIso ((coprod.desc a b).stalkMap ((coprod.inr : X' ⟶ X ⨿ X') x) ≫
          (coprod.inr : X' ⟶ X ⨿ X').stalkMap x) := by rw [← h]; infer_instance
      exact IsIso.of_isIso_comp_right _ ((coprod.inr : X' ⟶ X ⨿ X').stalkMap x)
  · rcases hcov z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨_, hinl x⟩
    · exact ⟨_, hinr x⟩

section Limits

/-- A coproduct of two étale morphisms is étale. -/
lemma _root_.AlgebraicGeometry.Etale.coprodDesc {X X' Z : Scheme.{u}} (f : X ⟶ Z) (g : X' ⟶ Z)
    [Etale f] [Etale g] : Etale (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{_, 0} X X')]
  rintro (⟨⟩ | ⟨⟩)
  · simpa [coprodOpenCover] using ‹Etale f›
  · simpa [coprodOpenCover] using ‹Etale g›

variable (Y) in
/-- `FÉt(Y)` as the category of `Y`-schemes with finite étale structure morphism. -/
@[simps]
noncomputable def toFiniteEtaleOver :
    Y.FiniteEtale ⥤ (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y where
  obj P := MorphismProperty.Over.mk ⊤ P.obj.hom ⟨P.property, P.obj.prop⟩
  map f := MorphismProperty.Over.homMk f.hom.left (hom_left_comp f) trivial

/-- `FÉt(Y) ⥤ (finite ⊓ étale).Over Y` is fully faithful. -/
noncomputable def toFiniteEtaleOverFullyFaithful : (toFiniteEtaleOver Y).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := hom_ext rfl

instance : (toFiniteEtaleOver Y).Full := toFiniteEtaleOverFullyFaithful.full
instance : (toFiniteEtaleOver Y).Faithful := toFiniteEtaleOverFullyFaithful.faithful
instance : (toFiniteEtaleOver Y).EssSurj where
  mem_essImage A := ⟨⟨MorphismProperty.Over.mk ⊤ A.hom A.prop.2, A.prop.1⟩,
    ⟨MorphismProperty.Over.isoMk (Iso.refl _)⟩⟩
instance : (toFiniteEtaleOver Y).IsEquivalence where

instance : HasFiniteLimits Y.FiniteEtale :=
  ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (toFiniteEtaleOver Y)⟩

variable (Y) in
/-- The underlying scheme of a finite étale `Y`-scheme. -/
noncomputable abbrev forgetScheme : Y.FiniteEtale ⥤ Scheme.{u} :=
  toFiniteEtaleOver Y ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y

instance : PreservesLimitsOfShape WalkingCospan (forgetScheme Y) := inferInstance

instance {P Q : Y.FiniteEtale} (i : P ⟶ Q) [Mono i] : Mono i.hom.left :=
  (forgetScheme Y).map_mono i

/-- The initial finite étale `Y`-scheme: the empty scheme. -/
noncomputable def empty : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (Scheme.emptyTo Y) inferInstance,
    show IsFinite (Scheme.emptyTo Y) from inferInstance⟩

/-- The empty scheme is initial in `FÉt(Y)`. -/
noncomputable def isInitialEmpty : IsInitial (empty (Y := Y)) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ ObjectProperty.homMk (MorphismProperty.Over.homMk (Scheme.emptyTo _)
      (_root_.AlgebraicGeometry.emptyIsInitial.hom_ext _ _) trivial))
    (fun _ _ ↦ hom_ext (_root_.AlgebraicGeometry.emptyIsInitial.hom_ext _ _))

/-- The disjoint union of two finite étale `Y`-schemes. -/
noncomputable def coprod (P Q : Y.FiniteEtale) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (Limits.coprod.desc P.obj.hom Q.obj.hom)
    (by have := P.obj.prop; have := Q.obj.prop; exact Etale.coprodDesc _ _),
    by
      have : IsFinite P.obj.hom := P.property
      have : IsFinite Q.obj.hom := Q.property
      exact show IsFinite (Limits.coprod.desc P.obj.hom Q.obj.hom) from inferInstance⟩

/-- The disjoint union is a coproduct in `FÉt(Y)`. -/
noncomputable def coprodCofan (P Q : Y.FiniteEtale) : BinaryCofan P Q :=
  BinaryCofan.mk
    (ObjectProperty.homMk (MorphismProperty.Over.homMk Limits.coprod.inl
      (Limits.coprod.inl_desc _ _)) : P ⟶ coprod P Q)
    (ObjectProperty.homMk (MorphismProperty.Over.homMk Limits.coprod.inr
      (Limits.coprod.inr_desc _ _)) : Q ⟶ coprod P Q)

/-- The disjoint union is a coproduct in `FÉt(Y)`. -/
noncomputable def isColimitCoprodCofan (P Q : Y.FiniteEtale) : IsColimit (coprodCofan P Q) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ObjectProperty.homMk (MorphismProperty.Over.homMk
      (Limits.coprod.desc f.hom.left g.hom.left)
      (by
        apply Limits.coprod.hom_ext
        · exact (Limits.coprod.inl_desc_assoc _ _ _).trans
            ((hom_left_comp f).trans (Limits.coprod.inl_desc _ _).symm)
        · exact (Limits.coprod.inr_desc_assoc _ _ _).trans
            ((hom_left_comp g).trans (Limits.coprod.inr_desc _ _).symm))))
    (fun f g ↦ hom_ext (Limits.coprod.inl_desc _ _))
    (fun f g ↦ hom_ext (Limits.coprod.inr_desc _ _))
    (fun f g m h₁ h₂ ↦ hom_ext (by
      apply Limits.coprod.hom_ext
      · exact congr(($h₁).hom.left).trans (Limits.coprod.inl_desc _ _).symm
      · exact congr(($h₂).hom.left).trans (Limits.coprod.inr_desc _ _).symm))

instance : HasBinaryCoproducts Y.FiniteEtale :=
  @hasBinaryCoproducts_of_hasColimit_pair _ _ (fun {P Q} ↦ ⟨⟨_, isColimitCoprodCofan P Q⟩⟩)

instance : HasInitial Y.FiniteEtale := isInitialEmpty.hasInitial

instance : HasFiniteCoproducts Y.FiniteEtale :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- **Monomorphisms are inclusions of direct summands** in `FÉt(Y)`: a monomorphism of finite
étale `Y`-schemes is an étale monomorphism, hence an open immersion, and it is finite, hence
closed; its image is open and closed, and the complement is the other summand. -/
lemma monoInducesIsoOnDirectSummand {X Z : Y.FiniteEtale} (i : X ⟶ Z) [Mono i] :
    ∃ (Z' : Y.FiniteEtale) (u : Z' ⟶ Z), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  let V : Z.obj.left.Opens := i.hom.left.opensRange
  have hVc : IsClosed (V : Set Z.obj.left) := i.hom.left.isClosedMap.isClosed_range
  let W : Z.obj.left.Opens := ⟨(V : Set Z.obj.left)ᶜ, hVc.isOpen_compl⟩
  have hW : IsClosed (W : Set Z.obj.left) := isClosed_compl_iff.mpr V.isOpen
  let Z' := ofIsClopen Z W hW
  have hiso : IsIso (coprod.desc i.hom.left W.ι) := by
    refine isIso_coprodDesc_of_isOpenImmersion _ _ (fun x w hxw ↦ ?_) (fun z ↦ ?_)
    · have : W.ι w ∈ W := by simp
      exact this ⟨x, hxw⟩
    · by_cases hz : z ∈ V
      · exact .inl hz
      · exact .inr ⟨⟨z, hz⟩, rfl⟩
  let c := BinaryCofan.mk i (ofIsClopenι Z W hW)
  have : IsIso ((forgetScheme Y).map ((isColimitCoprodCofan X Z').desc c)) := by
    change IsIso (coprod.desc i.hom.left W.ι)
    exact hiso
  have : IsIso ((isColimitCoprodCofan X Z').desc c) :=
    isIso_of_reflects_iso _ (forgetScheme Y)
  exact ⟨Z', ofIsClopenι Z W hW, ⟨IsColimit.ofPointIso (isColimitCoprodCofan X Z')⟩⟩

end Limits

section FiberLimits

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The fibre functor followed by the inclusion into types is corepresented by `s` on
`Y`-schemes. -/
noncomputable def fiberCompInclIso : fiber s ⋙ FintypeCat.incl ≅
    toFiniteEtaleOver Y ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ coyoneda.obj (.op (Over.mk s)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance : PreservesFiniteLimits (fiber s ⋙ FintypeCat.incl) :=
  preservesFiniteLimits_of_natIso (fiberCompInclIso s).symm

instance : PreservesFiniteLimits (fiber s) :=
  preservesFiniteLimits_of_reflects_of_preserves (fiber s) FintypeCat.incl

omit [IsSepClosed Ω] in
/-- A geometric point of a disjoint union factors through one of the summands. -/
lemma _root_.AlgebraicGeometry.exists_eq_comp_inl_or_inr {X X' : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X ⨿ X') :
    (∃ y, x = y ≫ (coprod.inl : X ⟶ X ⨿ X')) ∨ ∃ y, x = y ≫ (coprod.inr : X' ⟶ X ⨿ X') := by
  have hpt (p : Spec (.of Ω)) : p = default := Subsingleton.elim _ _
  obtain ⟨(a | a), ha⟩ := (coprodMk X X').surjective (x default)
  · left
    have h : Set.range x ⊆ Set.range (coprod.inl : X ⟶ X ⨿ X') := by
      rintro _ ⟨p, rfl⟩
      exact ⟨a, by rw [hpt p, ← ha, coprodMk_inl]⟩
    exact ⟨IsOpenImmersion.lift _ x h, (IsOpenImmersion.lift_fac _ _ h).symm⟩
  · right
    have h : Set.range x ⊆ Set.range (coprod.inr : X' ⟶ X ⨿ X') := by
      rintro _ ⟨p, rfl⟩
      exact ⟨a, by rw [hpt p, ← ha, coprodMk_inr]⟩
    exact ⟨IsOpenImmersion.lift _ x h, (IsOpenImmersion.lift_fac _ _ h).symm⟩

lemma isColimit_binaryCofan_fiber (P Q : Y.FiniteEtale) :
    Nonempty (IsColimit (BinaryCofan.mk ((fiber s ⋙ FintypeCat.incl).map (coprodCofan P Q).inl)
      ((fiber s ⋙ FintypeCat.incl).map (coprodCofan P Q).inr))) := by
  rw [Types.binaryCofan_isColimit_iff]
  have hinl (y y' : (fiber s).obj P) (h : (fiber s).map (coprodCofan P Q).inl y =
      (fiber s).map (coprodCofan P Q).inl y') : y = y' := by
    apply fiber_ext
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) h
    simp only [fiber_map_left] at this
    exact (cancel_mono (coprod.inl : P.obj.left ⟶ P.obj.left ⨿ Q.obj.left)).mp this
  have hinr (y y' : (fiber s).obj Q) (h : (fiber s).map (coprodCofan P Q).inr y =
      (fiber s).map (coprodCofan P Q).inr y') : y = y' := by
    apply fiber_ext
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) h
    simp only [fiber_map_left] at this
    exact (cancel_mono (coprod.inr : Q.obj.left ⟶ P.obj.left ⨿ Q.obj.left)).mp this
  refine ⟨hinl, hinr, ⟨?_, ?_⟩⟩
  · rw [Set.disjoint_iff]
    rintro _ ⟨⟨y, rfl⟩, ⟨y', hy'⟩⟩
    change (fiber s).obj P at y
    change (fiber s).obj Q at y'
    change (fiber s).map (coprodCofan P Q).inr y' = (fiber s).map (coprodCofan P Q).inl y at hy'
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) hy'
    simp only [fiber_map_left] at this
    have := congr_arg (fun g : Spec (.of Ω) ⟶ P.obj.left ⨿ Q.obj.left ↦ g (default : Spec (.of Ω)))
      this
    simp only [Scheme.Hom.comp_apply] at this
    exact inr_ne_inl _ _ _ _ this
  · refine codisjoint_iff.mpr (Set.eq_univ_of_forall fun x ↦ ?_)
    change (fiber s).obj (coprod P Q) at x
    rcases exists_eq_comp_inl_or_inr x.left with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine .inl ⟨Over.homMk y ?_, fiber_ext s ?_⟩
      · change y ≫ P.obj.hom = s
        rw [← fiber_left_comp s x, hy, Category.assoc]
        exact congr_arg (y ≫ ·) (coprod.inl_desc _ _).symm
      · exact hy.symm
    · refine .inr ⟨Over.homMk y ?_, fiber_ext s ?_⟩
      · change y ≫ Q.obj.hom = s
        rw [← fiber_left_comp s x, hy, Category.assoc]
        exact congr_arg (y ≫ ·) (coprod.inr_desc _ _).symm
      · exact hy.symm

instance (P Q : Y.FiniteEtale) : PreservesColimit (pair P Q) (fiber s) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoprodCofan P Q)
    (isColimitOfReflects FintypeCat.incl
      ((isColimitMapCoconeBinaryCofanEquiv (fiber s ⋙ FintypeCat.incl) _ _).symm
        (isColimit_binaryCofan_fiber s P Q).some))

lemma isEmpty_fiber_empty : IsEmpty ((fiber s).obj (empty (Y := Y))) :=
  ⟨fun x ↦ (inferInstance : IsEmpty (∅ : Scheme.{u})).false (x.left (default : Spec (.of Ω)))⟩

instance : PreservesColimit (Functor.empty.{0} Y.FiniteEtale) (fiber s) := by
  have := isEmpty_fiber_empty s
  obtain ⟨h⟩ := (Types.initial_iff_empty ((fiber s ⋙ FintypeCat.incl).obj empty)).mpr this
  exact preservesColimit_of_preserves_colimit_cocone isInitialEmpty
    ((isColimitMapCoconeEmptyCoconeEquiv _ _).symm (IsInitial.isInitialOfObj FintypeCat.incl _ h))

instance : PreservesColimitsOfShape (Discrete WalkingPair) (fiber s) :=
  ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm⟩

instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) (fiber s) :=
  preservesColimitsOfShape_pempty_of_preservesInitial (fiber s)

instance : PreservesFiniteCoproducts (fiber s) :=
  ⟨fun n ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial (fiber s) (Fin n)⟩

end FiberLimits

section Quotient

variable {G : Type u} [Monoid G] [Finite G] (D : SingleObj G ⥤ Y.FiniteEtale)

lemma isAffineHom_of_isAffineHom {X Z : Scheme.{u}} (f : X ⟶ Z) (hf : IsAffineHom f) :
    IsAffineHom f :=
  hf

lemma isAffineHom_of_isAffine {X Z : Scheme.{u}} (f : X ⟶ Z) (_ : IsAffine X) (_ : IsAffine Z) :
    IsAffineHom f :=
  inferInstance

/-- The gluing data for the quotient of a finite étale `Y`-scheme by a finite monoid action. -/
noncomputable abbrev quotientGluingData :
    Y.directedAffineCover.ColimitGluingData (D ⋙ toAffineOver Y) :=
  Scheme.quotientGluingData isAffineHom_of_isAffineHom isAffineHom_of_isAffine _

instance preservesColimitsOfShape_pullback_trans {U V : Y.directedAffineCover.I₀} (hUV : U ⟶ V) :
    PreservesColimitsOfShape (SingleObj G)
      (MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
        (Y.directedAffineCover.trans hUV)) :=
  preservesColimitsOfShape_pullback isAffineHom_of_isAffineHom isAffineHom_of_isAffine _

/-- The quotient cocone in affine `Y`-schemes is a colimit. -/
noncomputable def isColimitGluedCocone : IsColimit (quotientGluingData D).gluedCocone :=
  (quotientGluingData D).isColimitGluedCocone

lemma isFinite_and_etale_gluedCocone :
    IsFinite (quotientGluingData D).gluedCocone.pt.hom ∧
      Etale (quotientGluingData D).gluedCocone.pt.hom := by
  have : IsFinite ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).property
  have : Etale ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).obj.prop
  exact isFinite_and_etale_of_isColimit isAffineHom_of_isAffineHom isAffineHom_of_isAffine _
    (isColimitGluedCocone D)

/-- The quotient of a finite étale `Y`-scheme by a finite monoid action, as a cocone in
`FÉt(Y)`. -/
noncomputable def quotientCocone : Cocone D where
  pt := ⟨MorphismProperty.Over.mk ⊤ (quotientGluingData D).gluedCocone.pt.hom
    (isFinite_and_etale_gluedCocone D).2, (isFinite_and_etale_gluedCocone D).1⟩
  ι :=
    { app j := ObjectProperty.homMk (MorphismProperty.Over.homMk
        ((quotientGluingData D).gluedCocone.ι.app j).left
        (MorphismProperty.Over.w ((quotientGluingData D).gluedCocone.ι.app j)))
      naturality j j' g := hom_ext
        congr(($((quotientGluingData D).gluedCocone.ι.naturality g)).left) }

/-- The quotient cocone is a colimit in `FÉt(Y)`. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone D) :=
  isColimitOfReflects (toAffineOver Y)
    (IsColimit.ofIsoColimit (isColimitGluedCocone D)
      (Cocone.ext (MorphismProperty.Over.isoMk (Iso.refl _)) fun _ ↦
        MorphismProperty.Over.Hom.ext (by simp [quotientCocone])))

variable (Y G) in
/-- **`FÉt(Y)` has quotients by finite monoids.** -/
theorem hasColimitsOfShape_singleObj : HasColimitsOfShape (SingleObj G) Y.FiniteEtale :=
  ⟨fun D ↦ ⟨_, isColimitQuotientCocone D⟩⟩

end Quotient

end AlgebraicGeometry.Scheme.FiniteEtale
