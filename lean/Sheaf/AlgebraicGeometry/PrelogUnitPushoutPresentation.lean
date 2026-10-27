/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Unit-pushout presentations of prelog presheaves

Source: ILO, Exposé VI 1.1, printed p. 69; Stacks, Tag 00YR.
(blueprint: def-trf-prelog-unit-pushout-presentation).

The existing divisorial chart quotient applies to every ring-valued monoid map
by range restriction. Here the monoid itself varies contravariantly. Q28’s existing bundled
`PrelogPushoutPresentation` is reused, and the normalized comparison below
identifies its natural pair-map encoding with the explicit quotient functor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual quotient congruence at an étale test object. Source: ILO VI 1.1
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentationCon {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) (W : X.Etale) :
    Con (M.obj (op W) × Γ(W.left, ⊤)ˣ) :=
  divisorialChartCongruence (γ.app (op W)).hom.mrangeRestrict

/-- Pullback on pairs restricts both the monoid element and the ring unit.
Source: ILO VI 1.1 (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPairRestriction {X : Scheme.{u}} (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    {V W : X.Etale} (f : V ⟶ W) :
    M.obj (op W) × Γ(W.left, ⊤)ˣ →* M.obj (op V) × Γ(V.left, ⊤)ˣ :=
  (M.map f.op).hom.prodMap (Units.map f.left.appTop.hom.toMonoidHom)

/-- Pullback respects the quotient relations. Source: ILO VI 1.1.
Proof: naturality of γ sends each relation identifying a monoid element with its
unit image to the identical relation after pullback; close under congruence.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogPairRestriction_wellDefined {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    {V W : X.Etale} (f : V ⟶ W) :
    prelogPresentationCon γ W ≤
      Con.ker ((prelogPresentationCon γ V).mk'.comp (prelogPairRestriction M f)) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨m, a, h, rfl, rfl⟩
  change (prelogPresentationCon γ V).mk' (prelogPairRestriction M f (m, 1)) =
    (prelogPresentationCon γ V).mk' (prelogPairRestriction M f (1, a))
  change (prelogPresentationCon γ V).mk'
      (M.map f.op m, Units.map f.left.appTop.hom.toMonoidHom 1) =
    (prelogPresentationCon γ V).mk'
      (M.map f.op 1, Units.map f.left.appTop.hom.toMonoidHom a)
  rw [map_one, map_one]
  apply (prelogPresentationCon γ V).eq.mpr
  apply Con.le_conGen
  refine ⟨M.map f.op m, Units.map f.left.appTop.hom.toMonoidHom a, ?_, rfl, rfl⟩
  have hn := congrArg (fun k ↦ k m) (γ.naturality f.op)
  change γ.app (op V) (M.map f.op m) = f.left.appTop (γ.app (op W) m) at hn
  change γ.app (op V) (M.map f.op m) = f.left.appTop a.val
  exact hn.trans (congrArg (fun z ↦ f.left.appTop z) h)

/-- The canonical restriction on the actual quotient monoids. Source: ILO VI 1.1
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentationMap {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    {V W : X.Etale} (f : V ⟶ W) :
    CommMonCat.of (prelogPresentationCon γ W).Quotient ⟶
      CommMonCat.of (prelogPresentationCon γ V).Quotient :=
  CommMonCat.ofHom ((prelogPresentationCon γ W).lift
    ((prelogPresentationCon γ V).mk'.comp (prelogPairRestriction M f))
      (prelogPairRestriction_wellDefined γ f))

/-- Identity acts identically on every pair representative. Source: ILO VI 1.1.
Proof: pullback along the identity fixes each component of the pair, and quotient
classes are exhausted by pairs. (blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogPresentationMap_id {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) (W : X.Etale) :
    prelogPresentationMap γ (𝟙 W) = 𝟙 _ := by
  apply CommMonCat.hom_ext
  apply MonoidHom.ext
  intro z
  refine Con.induction_on z ?_
  rintro ⟨m, a⟩
  change (prelogPresentationCon γ W).mk' (prelogPairRestriction M (𝟙 W) (m, a)) =
    (prelogPresentationCon γ W).mk' (m, a)
  congr 1
  apply Prod.ext
  · change M.map (𝟙 (op W)) m = m
    simp
  · apply Units.ext
    change (𝟙 W.left : W.left ⟶ W.left).appTop a.val = a.val
    simp

/-- Successive restrictions agree with the restriction along the composite.
Source: ILO VI 1.1. Proof: check on pairs using functoriality of M and pullback of
functions, then use surjectivity of the quotient map.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogPresentationMap_comp {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W) :
    prelogPresentationMap γ (f ≫ g) =
      prelogPresentationMap γ g ≫ prelogPresentationMap γ f := by
  apply CommMonCat.hom_ext
  apply MonoidHom.ext
  intro z
  refine Con.induction_on z ?_
  rintro ⟨m, a⟩
  change (prelogPresentationCon γ U).mk' (prelogPairRestriction M (f ≫ g) (m, a)) =
    (prelogPresentationCon γ U).mk'
      (prelogPairRestriction M f (prelogPairRestriction M g (m, a)))
  congr 1
  apply Prod.ext
  · change M.map (g.op ≫ f.op) m = M.map f.op (M.map g.op m)
    simp
  · apply Units.ext
    change (f.left ≫ g.left).appTop a.val = f.left.appTop (g.left.appTop a.val)
    simp

/-- The quotient-of-pairs presheaf of the given prelog presheaf, with real data.
Source: ILO VI 1.1 (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentation {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :
    X.Etaleᵒᵖ ⥤ CommMonCat.{u} where
  obj W := CommMonCat.of (prelogPresentationCon γ W.unop).Quotient
  map f := prelogPresentationMap γ f.unop
  map_id W := prelogPresentationMap_id γ W.unop
  map_comp f g := prelogPresentationMap_comp γ g.unop f.unop

/-- The quotient class of a pair. Source: ILO VI 1.1
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentationPair {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) (W : X.Etale) :
    M.obj (op W) × Γ(W.left, ⊤)ˣ →* (prelogPresentation γ).obj (op W) :=
  (prelogPresentationCon γ W).mk'

/-- The monoid-sheafification universal property with its specified unit.
Source: Stacks Tag 00YR (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def IsPrelogPresentationSheafification {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (η : prelogPresentation γ ⟶ L.obj) : Prop :=
  ∀ H : Sheaf X.smallEtaleTopology CommMonCat.{u},
    Function.Bijective (fun f : L ⟶ H ↦ η ≫ f.hom)

/-- The inclusion of the monoid into the sheafified quotient is natural.
Source: ILO VI 1.1. Proof: both composites send m to the restriction of [m,1],
because the quotient restriction restricts both entries.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogPresentationIota_naturality {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (η : prelogPresentation γ ⟶ L.obj) {V W : X.Etaleᵒᵖ} (f : V ⟶ W) :
    M.map f ≫ CommMonCat.ofHom
        ((η.app W).hom.comp ((prelogPresentationPair γ W.unop).comp
          (MonoidHom.inl (M.obj W) Γ(W.unop.left, ⊤)ˣ))) =
      CommMonCat.ofHom ((η.app V).hom.comp ((prelogPresentationPair γ V.unop).comp
        (MonoidHom.inl (M.obj V) Γ(V.unop.left, ⊤)ˣ))) ≫ L.obj.map f := by
  ext m
  have hn := congrArg (fun k ↦ k (prelogPresentationPair γ V.unop (m, 1)))
    (η.naturality f)
  simpa [prelogPresentation, prelogPresentationMap, prelogPresentationPair,
    prelogPairRestriction] using hn

/-- The natural map m ↦ η([m,1]). Source: ILO VI 1.1
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentationIota {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (η : prelogPresentation γ ⟶ L.obj) : M ⟶ L.obj where
  app W := CommMonCat.ofHom ((η.app W).hom.comp
    ((prelogPresentationPair γ W.unop).comp (MonoidHom.inl (M.obj W) Γ(W.unop.left, ⊤)ˣ)))
  naturality _ _ f := prelogPresentationIota_naturality γ L η f

/-- The unit map a ↦ η([1,a]). Source: ILO VI 1.1
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogPresentationUnits {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (η : prelogPresentation γ ⟶ L.obj) (W : X.Etale) :
    Γ(W.left, ⊤)ˣ →* L.obj.obj (op W) :=
  (η.app (op W)).hom.comp ((prelogPresentationPair γ W).comp
    (MonoidHom.inr (M.obj (op W)) Γ(W.left, ⊤)ˣ))

/-- The stalk diagram also makes sense for an arbitrary monoid presheaf.
Source: Stacks Tag 040R (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogStalkDiagram {X : Scheme.{u}} (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ ⥤ CommMonCat.{u} :=
  (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙ M

/-- The actual filtered monoid colimit exists on pointed neighbourhoods. This is
constructed from Mathlib's filtered colimit on a small final model, exactly as in
`pointedEtaleCommMonStalkHasColimit`, now before imposing the sheaf condition.
Source: Stacks Tags 03PQ, 040R
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
instance prelogStalkColimits {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    HasColimitsOfShape (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ CommMonCat.{u} :=
  have : HasColimitsOfShape
      (FinallySmall.FilteredFinalModel.{u} (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ)
      CommMonCat.{u} :=
    ⟨fun D ↦ ⟨⟨_, CommMonCat.FilteredColimits.colimitCoconeIsColimit D⟩⟩⟩
  Functor.Final.hasColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u} (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ)

/-- The stalk of the presheaf M, using precisely the pointed-neighbourhood colimit.
Source: Stacks Tag 040R (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogStalk {X : Scheme.{u}} (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) : CommMonCat.{u} :=
  colimit (prelogStalkDiagram M t)

/-- The induced stalk map is the canonical map of these colimits. Its target is
the already recorded geometric stalk, not a separately chosen monoid.
Source: Stacks Tag 040R (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogStalkMap {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (N : Sheaf X.smallEtaleTopology CommMonCat.{u}) (i : M ⟶ N.obj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    prelogStalk M t ⟶ pointedEtaleStalk N t :=
  colim.map (Functor.whiskerLeft
    (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op i)

/-- The inverse units identification on sections. This is the inverse function of
the units map induced by α, followed by the inclusion of monoid units. The
logarithmic compatibility axiom makes this map bijective, so this is its unique
inverse, as for `unitsIn`.
Source: ILO VI 1.1 (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogSectionUnit {X : Scheme.{u}} (K : EtaleLogStructure X) (W : X.Etale)
    (a : Γ(W.left, ⊤)ˣ) : K.monoidSheaf.obj.obj (op W) :=
  (Function.invFun (Units.map (K.alpha.app (op W)).hom) a).val

/-- The universal mapping bijection, expressed as injectivity and precisely the
compatible range, avoiding any chosen inverse or hidden proof in the signature.
Source: ILO VI 1.1 (blueprint: def-trf-prelog-unit-pushout-presentation). -/
def HasPrelogUniversalMapping {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : EtaleLogStructure X) (i : M ⟶ L.monoidSheaf.obj) : Prop :=
  ∀ N : EtaleLogStructure X,
    Function.Injective (fun f : {f : L.monoidSheaf ⟶ N.monoidSheaf //
      f.hom ≫ N.alpha = L.alpha} ↦ i ≫ f.val.hom) ∧
    Set.range (fun f : {f : L.monoidSheaf ⟶ N.monoidSheaf //
      f.hom ≫ N.alpha = L.alpha} ↦ i ≫ f.val.hom) =
      {v : M ⟶ N.monoidSheaf.obj | v ≫ N.alpha = γ}

/-- Q28's natural pair-map unit is natural for the explicit quotient functor.
Source: ILO VI 1.1; Stacks Tag 00YR.
Proof: on a representative [m,a], the quotient restriction restricts both entries.
The required equation is exactly `q.naturality`. Every class has a pair
representative, so this proves the equation on the whole quotient.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogBundledUnit_naturality {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    {γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat}
    {L : Sheaf X.smallEtaleTopology CommMonCat.{u}}
    {α : L.obj ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat}
    (q : PrelogPushoutPresentation X.smallEtaleTopology M
      X.etaleStructurePresheaf γ L α) {V W : X.Etaleᵒᵖ} (f : V ⟶ W) :
    (prelogPresentation γ).map f ≫ CommMonCat.ofHom (q.pairMap W) =
      CommMonCat.ofHom (q.pairMap V) ≫ L.obj.map f := by
  apply CommMonCat.hom_ext
  apply MonoidHom.ext
  intro z
  refine Con.induction_on z ?_
  rintro ⟨m, a⟩
  exact (q.naturality V W f m a).symm

/-- The unit from Q28's existing bundled presentation, as a natural transformation
from the explicit quotient presheaf. The pair maps are reused verbatim.
Source: ILO VI 1.1; Stacks Tag 00YR
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
def prelogBundledUnit {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    {γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat}
    {L : Sheaf X.smallEtaleTopology CommMonCat.{u}}
    {α : L.obj ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat}
    (q : PrelogPushoutPresentation X.smallEtaleTopology M
      X.etaleStructurePresheaf γ L α) : prelogPresentation γ ⟶ L.obj where
  app W := CommMonCat.ofHom (q.pairMap W)
  naturality _ _ f := prelogBundledUnit_naturality q f

private theorem prelogPairNatural_iff {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (H : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (r : ∀ W, (prelogPresentation γ).obj W →* H.obj W) :
    PrelogPairNatural M X.etaleStructurePresheaf γ H r ↔
      ∀ (V W : X.Etaleᵒᵖ) (f : V ⟶ W),
        (prelogPresentation γ).map f ≫ CommMonCat.ofHom (r W) =
          CommMonCat.ofHom (r V) ≫ H.map f := by
  constructor
  · intro hn V W f
    apply CommMonCat.hom_ext
    apply MonoidHom.ext
    intro z
    refine Con.induction_on z ?_
    rintro ⟨m, a⟩
    exact (hn V W f m a).symm
  · intro hn V W f m a
    exact (congrArg (fun k ↦ k (prelogPairClass
      (X.etaleStructurePresheaf.obj V) (γ.app V).hom m a)) (hn V W f)).symm

/-- The explicit unit with its sheafification property is exactly Q28's existing
bundled presentation, with the same structural map and prelog inclusion.
Source: ILO VI 1.1; Stacks Tag 00YR.
Proof: a natural transformation out of the explicit quotient presheaf is the
same as a family of quotient homomorphisms satisfying `PrelogPairNatural`:
check naturality on exhaustive pair representatives in both directions. Under
this identification, the hom-set bijection is precisely `q.universal`.
The structural equation is the given pair formula, and `q.iota_pair` identifies
the inclusions. Conversely use the supplied unit as `pairMap`; its naturality,
structural formula, and inclusion give the corresponding fields of q, and its
hom-set bijection gives the universal field. Thus no second notion of a
sheafified prelog presentation is introduced by the explicit quotient functor.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogPresentation_bundled_comparison {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : EtalePrelogStructure X) (η : prelogPresentation γ ⟶ L.monoidSheaf.obj)
    (hα : ∀ (W : X.Etale) (m : M.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
      L.alpha.app (op W) (η.app (op W) (prelogPresentationPair γ W (m, a))) =
        @id Γ(W.left, ⊤) (γ.app (op W) m) * a.val) :
    IsPrelogPresentationSheafification γ L.monoidSheaf η ↔
      ∃ q : PrelogPushoutPresentation X.smallEtaleTopology M
        X.etaleStructurePresheaf γ L.monoidSheaf L.alpha,
        prelogBundledUnit q = η ∧
        q.iota = prelogPresentationIota γ L.monoidSheaf η := by
  constructor
  · intro h
    let q : PrelogPushoutPresentation X.smallEtaleTopology M
        X.etaleStructurePresheaf γ L.monoidSheaf L.alpha :=
      { pairMap := fun W ↦ (η.app W).hom
        naturality := (prelogPairNatural_iff γ L.monoidSheaf.obj _).mpr
          (fun _ _ f ↦ η.naturality f)
        structural := fun W m a ↦ hα W.unop m a
        iota := prelogPresentationIota γ L.monoidSheaf η
        iota_pair := fun _ _ ↦ rfl
        universal := by
          intro H r hr
          let τ : prelogPresentation γ ⟶ H.obj :=
            { app := fun W ↦ CommMonCat.ofHom (r W)
              naturality := (prelogPairNatural_iff γ H.obj r).mp hr }
          obtain ⟨f, hf, hu⟩ := (h H).existsUnique τ
          refine ⟨f, ?_, ?_⟩
          · intro W z
            exact congrArg (fun k ↦ k.app W z) hf
          · intro g hg
            apply hu
            ext W z
            exact hg W z }
    exact ⟨q, by ext W z; rfl, rfl⟩
  · rintro ⟨q, hq, _⟩ H
    apply (Function.bijective_iff_existsUnique _).mpr
    intro τ
    have hr : PrelogPairNatural M X.etaleStructurePresheaf γ H.obj
        (fun W ↦ (τ.app W).hom) :=
      (prelogPairNatural_iff γ H.obj _).mpr (fun _ _ f ↦ τ.naturality f)
    obtain ⟨f, hf, hu⟩ := q.universal H (fun W ↦ (τ.app W).hom) hr
    have hpair (W : X.Etaleᵒᵖ) (z : (prelogPresentation γ).obj W) :
        q.pairMap W z = η.app W z := congrArg (fun k ↦ k.app W z) hq
    refine ⟨f, ?_, ?_⟩
    · ext W z
      change f.hom.app W (η.app W z) = τ.app W z
      rw [← hpair]
      exact hf W z
    · intro g hg
      apply hu
      intro W z
      rw [hpair]
      exact congrArg (fun k ↦ k.app W z) hg

/-- The general presheaf mapping predicate specializes to Q28's existing
`EtaleUniversal` predicate on a prelog sheaf; neither tests a smaller class of maps.
Source: ILO VI 1.1; Stacks Tag 00YR.
Proof: `q.iota_pair` and `q.structural`, with a=1, make q.iota compatible with
P.alpha. Hence composition with q.iota always lands among compatible maps.
Injectivity and equality of that range are exactly unique existence of a lift
for every compatible map, which is the definition of `EtaleUniversal`.
(blueprint: def-trf-prelog-unit-pushout-presentation). -/
theorem prelogUniversalMapping_bundled_iff {X : Scheme.{u}}
    (P : EtalePrelogStructure X) (L : EtaleLogStructure X)
    (q : PrelogPushoutPresentation X.smallEtaleTopology
      P.monoidSheaf.obj X.etaleStructurePresheaf P.alpha L.monoidSheaf L.alpha) :
    HasPrelogUniversalMapping P.alpha L q.iota ↔ q.EtaleUniversal P L := by
  have hi : q.iota ≫ L.alpha = P.alpha := by
    ext W m
    change L.alpha.app W (q.iota.app W m) = P.alpha.app W m
    rw [q.iota_pair]
    simpa using q.structural W m 1
  constructor
  · intro h K f hf
    have hr : f ∈ Set.range (fun g : {g : L.monoidSheaf ⟶ K.monoidSheaf //
        g.hom ≫ K.alpha = L.alpha} ↦ q.iota ≫ g.val.hom) := by
      rw [(h K).2]
      exact hf
    obtain ⟨g, hg⟩ := hr
    refine ⟨g, hg, ?_⟩
    intro k hk
    exact (h K).1 (hk.trans hg.symm)
  · intro h K
    refine ⟨?_, ?_⟩
    · intro f g hfg
      have hc : (q.iota ≫ f.val.hom) ≫ K.alpha = P.alpha := by
        rw [Category.assoc, f.property, hi]
      obtain ⟨k, _, hk⟩ := h K (q.iota ≫ f.val.hom) hc
      exact (hk f rfl).trans (hk g hfg.symm).symm
    · ext v
      constructor
      · rintro ⟨f, rfl⟩
        change (q.iota ≫ f.val.hom) ≫ K.alpha = P.alpha
        rw [Category.assoc, f.property, hi]
      · intro hv
        obtain ⟨f, hf, _⟩ := h K v hv
        exact ⟨f, hf⟩

end AlgebraicGeometry
