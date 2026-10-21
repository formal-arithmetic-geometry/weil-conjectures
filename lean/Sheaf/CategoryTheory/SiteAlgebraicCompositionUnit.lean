/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Algebraic transport of unit-normalized site composition and identity

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (blueprint: lem-pur-site-algebraic-composition-unit).

The composite inverse image is the specified comma-colimit/sheafification construction.
Its comparison is obtained from the specified adjunctions, without choosing another unit.
The predicates below spell out the algebraic clauses using the recorded presentations;
they do not choose new ring or module structures.
-/

@[expose] public section

universe uC vC uD vD uE vE w s

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The specified inverse image for the composite site functor. The continuity proof is
Mathlib's composition lemma; the functor is exactly left Kan extension then sheafification.
Source: Stacks Project, Sites, Tags 03CB and 00WX
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositePullback
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :=
  letI := Functor.isContinuous_comp v u J K L
  sheafPullback (v ⋙ u) (Type (max uC vC uD vD uE vE w)) J L

/-- The specified composite-site adjunction, with right adjoint written as successive
precomposition. These precomposition functors are definitionally identical.
Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX and 00WH
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositeAdjunction
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :
    siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ⊣
      u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L ⋙
        v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K :=
  letI := Functor.isContinuous_comp v u J K L
  sheafAdjunctionContinuous (v ⋙ u) (Type (max uC vC uD vD uE vE w)) J L

/-- The comparison determined by the specified units, directed from composite to iterated
inverse image. No existence choice or arbitrary natural isomorphism is used.
Source: Stacks Project, Sites, Tag 03CB, with the unit normalization of Tags 00VE and 00WX
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositionIso
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :
    siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
      sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
        sheafPullback u (Type (max uC vC uD vD uE vE w)) K L :=
  (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).leftAdjointUniq
    ((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).comp
      (sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L))

/-- The ring and module clauses for a comparison of algebraic inverse-image presentations.
The ring isomorphism and additive natural isomorphism have precisely the prescribed
underlying maps; semilinearity is required on every section. Isomorphisms of ring sheaves
preserve zero, one, addition and multiplication; additive sheaf isomorphisms preserve zero
and addition. The natural-isomorphism type includes naturality on all module morphisms.
Source: Stacks Project, Sites, Tag 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-site-algebraic-composition-unit). -/
def SiteAlgebraicComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    {L₀ L₁ : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : L₀ ⟶ L₁) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{s}) (R₀ R₁ : Sheaf K CommRingCat.{s})
    (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses L₀ R R₀)
    (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses L₁ R R₁),
    ∃ eR : R₀ ≅ R₁,
      (sheafCompose K (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
          eR.hom =
        A₀.ringUnderlying.inv ≫ γ.app _ ≫ A₁.ringUnderlying.hom ∧
      ∃ eM : A₀.modules ⋙ SheafOfModules.toSheaf _ ≅
          A₁.modules ⋙ SheafOfModules.toSheaf _,
        (∀ M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R),
          (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{s} ⋙
              uliftFunctor.{s, s})).map (eM.hom.app M) =
            A₀.moduleUnderlying.hom.app M ≫ γ.app _ ≫ A₁.moduleUnderlying.inv.app M) ∧
        (∀ (M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R))
          (V : Dᵒᵖ) (a : R₀.obj.obj V) (x : (A₀.modules.obj M).val.obj V),
          (eM.hom.app M).hom.app V (a • x) =
            (@id (R₁.obj.obj V) (eR.hom.hom.app V a)) •
              (@id ((A₁.modules.obj M).val.obj V) ((eM.hom.app M).hom.app V x)))

/-- The algebraic identity-unit clauses, with their underlying maps fixed by the set unit.
Both the ring and module source are the original sheaves, so this also includes the
literal identity case rather than only a comparison between two chosen lifts.
Source: Stacks Project, Sites, Tags 00WX and 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-site-algebraic-composition-unit). -/
def SiteAlgebraicIdentityUnit
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    {I : Sheaf J (Type s) ⥤ Sheaf J (Type s)} (η : 𝟭 _ ⟶ I) : Prop :=
  ∀ (R RI : Sheaf J CommRingCat.{s})
    (A : SheafOfModules.AlgebraicInverseImageOfUniverses I R RI),
    ∃ eR : R ≅ RI,
      (sheafCompose J (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
          eR.hom = η.app _ ≫ A.ringUnderlying.hom ∧
      ∃ eM : SheafOfModules.toSheaf ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R) ≅
          A.modules ⋙ SheafOfModules.toSheaf _,
        (∀ M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R),
          (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{s} ⋙
              uliftFunctor.{s, s})).map (eM.hom.app M) =
            η.app _ ≫ A.moduleUnderlying.inv.app M) ∧
        (∀ (M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R))
          (V : Cᵒᵖ) (a : R.obj.obj V) (x : M.val.obj V),
          (eM.hom.app M).hom.app V (a • x) =
            (@id (RI.obj.obj V) (eR.hom.hom.app V a)) •
              (@id ((A.modules.obj M).val.obj V) ((eM.hom.app M).hom.app V x)))

noncomputable section Transport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private theorem pair_sections (F : Sheaf J (Type s) ⥤ Sheaf K (Type s))
    [PreservesFiniteLimits F] (X Y : Sheaf J (Type s)) (V : Dᵒᵖ)
    (x : (F.obj X).obj.obj V) (y : (F.obj Y).obj.obj V) :
    ∃ z : (F.obj (X ⨯ Y)).obj.obj V,
      (F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z = x ∧
        (F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z = y := by
  let E := F ⋙ sheafToPresheaf K (Type s) ⋙ (evaluation Dᵒᵖ (Type s)).obj V
  let h := isLimitOfHasBinaryProductOfPreservesLimit E X Y
  let c : BinaryFan (E.obj X) (E.obj Y) :=
    BinaryFan.mk (↾fun _ : PUnit.{s + 1} ↦ x) (↾fun _ : PUnit.{s + 1} ↦ y)
  let z := h.lift c
  refine ⟨z PUnit.unit, ?_, ?_⟩
  · exact congrArg (fun k : PUnit.{s + 1} ⟶ E.obj X ↦ k PUnit.unit)
      (h.fac c ⟨WalkingPair.left⟩)
  · exact congrArg (fun k : PUnit.{s + 1} ⟶ E.obj Y ↦ k PUnit.unit)
      (h.fac c ⟨WalkingPair.right⟩)

private def sectionMap {X Y : Sheaf J (Type s)}
    (f : ∀ V, X.obj.obj V → Y.obj.obj V)
    (hf : ∀ {V W} (i : V ⟶ W) (x : X.obj.obj V),
      Y.obj.map i (f V x) = f W (X.obj.map i x)) : X ⟶ Y :=
  ⟨{ app V := ↾(f V)
     naturality := by
       intro V W i
       ext x
       exact (hf i x).symm }⟩

private theorem nat_section
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X Y : Sheaf J (Type s)} (f : X ⟶ Y) (V : Dᵒᵖ) (x : (F.obj X).obj.obj V) :
    (γ.app Y).hom.app V ((F.map f).hom.app V x) =
      (G.map f).hom.app V ((γ.app X).hom.app V x) :=
  congrArg (fun k ↦ k.hom.app V x) (γ.naturality f)

private def compareMap
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁) : X₀ ⟶ X₁ :=
  e₀.inv ≫ γ.app X ≫ e₁.hom

private theorem compareMap_image
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁)
    (V : Dᵒᵖ) (x : (F.obj X).obj.obj V) :
    (compareMap γ e₀ e₁).hom.app V (e₀.hom.hom.app V x) =
      e₁.hom.hom.app V ((γ.app X).hom.app V x) := by
  change e₁.hom.hom.app V ((γ.app X).hom.app V
    (e₀.inv.hom.app V (e₀.hom.hom.app V x))) = _
  have h := congrArg (fun k ↦ k.hom.app V x) e₀.hom_inv_id
  change e₀.inv.hom.app V (e₀.hom.hom.app V x) = x at h
  rw [h]

private theorem compare_binary
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
    (γ : F ⟶ G) {X Y Z : Sheaf J (Type s)}
    {X₀ Y₀ Z₀ X₁ Y₁ Z₁ : Sheaf K (Type s)}
    (ex₀ : F.obj X ≅ X₀) (ey₀ : F.obj Y ≅ Y₀) (ez₀ : F.obj Z ≅ Z₀)
    (ex₁ : G.obj X ≅ X₁) (ey₁ : G.obj Y ≅ Y₁) (ez₁ : G.obj Z ≅ Z₁)
    (t : X ⨯ Y ⟶ Z)
    (o₀ : ∀ V, X₀.obj.obj V → Y₀.obj.obj V → Z₀.obj.obj V)
    (o₁ : ∀ V, X₁.obj.obj V → Y₁.obj.obj V → Z₁.obj.obj V)
    (h₀ : ∀ V (z : (F.obj (X ⨯ Y)).obj.obj V),
      ez₀.hom.hom.app V ((F.map t).hom.app V z) =
        o₀ V (ex₀.hom.hom.app V ((F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z))
          (ey₀.hom.hom.app V ((F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z)))
    (h₁ : ∀ V (z : (G.obj (X ⨯ Y)).obj.obj V),
      ez₁.hom.hom.app V ((G.map t).hom.app V z) =
        o₁ V (ex₁.hom.hom.app V ((G.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z))
          (ey₁.hom.hom.app V ((G.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z)))
    (V : Dᵒᵖ) (x : X₀.obj.obj V) (y : Y₀.obj.obj V) :
    (compareMap γ ez₀ ez₁).hom.app V (o₀ V x y) =
      o₁ V ((compareMap γ ex₀ ex₁).hom.app V x)
        ((compareMap γ ey₀ ey₁).hom.app V y) := by
  obtain ⟨z, hx, hy⟩ := pair_sections F X Y V (ex₀.inv.hom.app V x)
    (ey₀.inv.hom.app V y)
  have hx' : ex₀.hom.hom.app V ((F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z) = x := by
    rw [hx]
    exact congrArg (fun k ↦ k.hom.app V x) ex₀.inv_hom_id
  have hy' : ey₀.hom.hom.app V ((F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z) = y := by
    rw [hy]
    exact congrArg (fun k ↦ k.hom.app V y) ey₀.inv_hom_id
  rw [← hx', ← hy', ← h₀ V z, compareMap_image, nat_section, h₁]
  rw [compareMap_image, compareMap_image, nat_section, nat_section]

private theorem compare_constant
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁) (t : X ⟶ X)
    (n₀ : ∀ V, X₀.obj.obj V) (n₁ : ∀ V, X₁.obj.obj V)
    (h₀ : ∀ V (z : (F.obj X).obj.obj V),
      e₀.hom.hom.app V ((F.map t).hom.app V z) = n₀ V)
    (h₁ : ∀ V (z : (G.obj X).obj.obj V),
      e₁.hom.hom.app V ((G.map t).hom.app V z) = n₁ V) (V : Dᵒᵖ) :
    (compareMap γ e₀ e₁).hom.app V (n₀ V) = n₁ V := by
  rw [← h₀ V (e₀.inv.hom.app V (n₀ V)), compareMap_image, nat_section, h₁]

end Transport

noncomputable section AlgebraicTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]

private abbrev ringSets (R : Sheaf J CommRingCat.{s}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).obj R

private abbrev moduleSets {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
    (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).obj M)

private def binaryMap {X Y Z : Sheaf J (Type s)}
    (o : ∀ V, X.obj.obj V → Y.obj.obj V → Z.obj.obj V)
    (ho : ∀ {V W} (i : V ⟶ W) (x : X.obj.obj V) (y : Y.obj.obj V),
      Z.obj.map i (o V x y) = o W (X.obj.map i x) (Y.obj.map i y)) : X ⨯ Y ⟶ Z :=
  sectionMap (fun V z ↦ o V ((prod.fst : X ⨯ Y ⟶ X).hom.app V z)
    ((prod.snd : X ⨯ Y ⟶ Y).hom.app V z))
    (by
      intro V W i z
      rw [ho]
      congr 1
      · exact (congrArg (fun k ↦ k z) ((prod.fst : X ⨯ Y ⟶ X).hom.naturality i)).symm
      · exact (congrArg (fun k ↦ k z) ((prod.snd : X ⨯ Y ⟶ Y).hom.naturality i)).symm)

private def ringAddMap (R : Sheaf J CommRingCat.{s}) :
    ringSets R ⨯ ringSets R ⟶ ringSets R :=
  binaryMap (fun _ a b ↦ ULift.up (a.down + b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_add (R.obj.map i).hom a.down b.down)

private def ringMulMap (R : Sheaf J CommRingCat.{s}) :
    ringSets R ⨯ ringSets R ⟶ ringSets R :=
  binaryMap (fun _ a b ↦ ULift.up (a.down * b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_mul (R.obj.map i).hom a.down b.down)

private def ringConstMap (R : Sheaf J CommRingCat.{s}) (n : ℕ) :
    ringSets R ⟶ ringSets R :=
  sectionMap (fun V _ ↦ ULift.up (n : R.obj.obj V)) (by
    intro V W i x
    apply ULift.ext
    exact map_natCast (R.obj.map i).hom n)

private def moduleAddMap {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    moduleSets M ⨯ moduleSets M ⟶ moduleSets M :=
  binaryMap (fun _ a b ↦ ULift.up (a.down + b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_add (M.val.map i).hom a.down b.down)

private def moduleSMulMap {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringSets R ⨯ moduleSets M ⟶ moduleSets M :=
  binaryMap (fun V a b ↦ ULift.up
    ((@id (R.obj.obj V) a.down) • (@id (M.val.obj V) b.down))) (by
    intro V W i a b
    apply ULift.ext
    exact M.val.map_smul i a.down b.down)


end AlgebraicTransport

noncomputable section Lift

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ⟶ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

private theorem ring_compare_add (V : Dᵒᵖ) (a b : R₀.obj.obj V) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up (a + b))).down =
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down +
        ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying A₀.ringUnderlying A₀.ringUnderlying
      A₁.ringUnderlying A₁.ringUnderlying A₁.ringUnderlying (ringAddMap R)
      (fun _ a b ↦ ULift.up (a.down + b.down))
      (fun _ a b ↦ ULift.up (a.down + b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.ringAdd _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringAdd _ _ _ _ (fun _ _ ↦ rfl) V z

private theorem ring_compare_mul (V : Dᵒᵖ) (a b : R₀.obj.obj V) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up (a * b))).down =
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down *
        ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying A₀.ringUnderlying A₀.ringUnderlying
      A₁.ringUnderlying A₁.ringUnderlying A₁.ringUnderlying (ringMulMap R)
      (fun _ a b ↦ ULift.up (a.down * b.down))
      (fun _ a b ↦ ULift.up (a.down * b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.ringMul _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringMul _ _ _ _ (fun _ _ ↦ rfl) V z

omit [PreservesFiniteLimits F] in
private theorem ring_compare_zero (V : Dᵒᵖ) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up 0)).down = 0 := by
  apply congrArg ULift.down
    (compare_constant γ A₀.ringUnderlying A₁.ringUnderlying (ringConstMap R 0)
      (fun _ ↦ ULift.up 0) (fun _ ↦ ULift.up 0) ?_ ?_ V)
  · intro V z
    apply ULift.ext
    exact A₀.ringZero _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringZero _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z

omit [PreservesFiniteLimits F] in
private theorem ring_compare_one (V : Dᵒᵖ) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up 1)).down = 1 := by
  apply congrArg ULift.down
    (compare_constant γ A₀.ringUnderlying A₁.ringUnderlying (ringConstMap R 1)
      (fun _ ↦ ULift.up 1) (fun _ ↦ ULift.up 1) ?_ ?_ V)
  · intro V z
    apply ULift.ext
    exact A₀.ringOne _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringOne _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z

private def ringComparisonMap : R₀ ⟶ R₁ :=
  ⟨{ app V := CommRingCat.ofHom
       { toFun a := ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V
           (ULift.up a)).down
         map_one' := ring_compare_one γ A₀ A₁ V
         map_mul' := ring_compare_mul γ A₀ A₁ V
         map_zero' := ring_compare_zero γ A₀ A₁ V
         map_add' := ring_compare_add γ A₀ A₁ V }
     naturality := by
       intro V W i
       ext a
       exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up a))
         ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.naturality i)) }⟩

private theorem ringComparisonMap_underlying :
    (sheafCompose K (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
      (ringComparisonMap γ A₀ A₁) = compareMap γ A₀.ringUnderlying A₁.ringUnderlying := by
  ext V a
  rfl

private theorem module_compare_add
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Dᵒᵖ) (a b : (A₀.modules.obj M).val.obj V) :
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up (a + b))).down =
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up a)).down +
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ (A₀.moduleUnderlying.app M).symm (A₀.moduleUnderlying.app M).symm
      (A₀.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm (moduleAddMap M)
      (fun _ a b ↦ ULift.up (a.down + b.down))
      (fun _ a b ↦ ULift.up (a.down + b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.moduleAdd M _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.moduleAdd M _ _ _ _ (fun _ _ ↦ rfl) V z

private theorem module_compare_smul
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Dᵒᵖ) (a : R₀.obj.obj V) (b : (A₀.modules.obj M).val.obj V) :
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up (a • b))).down =
    (@id (R₁.obj.obj V)
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down) •
      (@id ((A₁.modules.obj M).val.obj V)
        ((compareMap γ (A₀.moduleUnderlying.app M).symm
          (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up b)).down) := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying (A₀.moduleUnderlying.app M).symm
      (A₀.moduleUnderlying.app M).symm A₁.ringUnderlying
      (A₁.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm (moduleSMulMap M)
      (fun V a b ↦ ULift.up
        ((@id (R₀.obj.obj V) a.down) • (@id ((A₀.modules.obj M).val.obj V) b.down)))
      (fun V a b ↦ ULift.up
        ((@id (R₁.obj.obj V) a.down) • (@id ((A₁.modules.obj M).val.obj V) b.down)))
      ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.moduleSMul M _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.moduleSMul M _ _ _ _ (fun _ _ ↦ rfl) V z

end Lift

noncomputable section FinishTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ≅ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

private def moduleComparisonApp
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (SheafOfModules.toSheaf _).obj (A₀.modules.obj M) ⟶
      (SheafOfModules.toSheaf _).obj (A₁.modules.obj M) :=
  ⟨{ app V := AddCommGrpCat.ofHom (AddMonoidHom.mk'
       (fun a ↦ ((compareMap γ.hom (A₀.moduleUnderlying.app M).symm
         (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up a)).down)
       (module_compare_add γ.hom A₀ A₁ M V))
     naturality := by
       intro V W i
       ext a
       exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up a))
         ((compareMap γ.hom (A₀.moduleUnderlying.app M).symm
           (A₁.moduleUnderlying.app M).symm).hom.naturality i)) }⟩

private theorem moduleComparisonApp_underlying
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map
      (moduleComparisonApp γ A₀ A₁ M) =
    compareMap γ.hom (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm := by
  ext V a
  rfl

private theorem algebraicComparison : SiteAlgebraicComparison γ.hom := by
  intro R R₀ R₁ A₀ A₁
  let er := A₀.ringUnderlying.symm ≪≫ γ.app _ ≪≫ A₁.ringUnderlying
  have : IsIso ((sheafCompose K
      (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
        (ringComparisonMap γ.hom A₀ A₁)) := by
    rw [ringComparisonMap_underlying]
    change IsIso er.hom
    infer_instance
  have : IsIso (ringComparisonMap γ.hom A₀ A₁) :=
    isIso_of_reflects_iso _ (sheafCompose K
      (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s}))
  refine ⟨asIso (ringComparisonMap γ.hom A₀ A₁),
    ringComparisonMap_underlying γ.hom A₀ A₁, ?_⟩
  let em := A₀.moduleUnderlying ≪≫ Functor.isoWhiskerLeft
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})) γ ≪≫
        A₁.moduleUnderlying.symm
  let τ : A₀.modules ⋙ SheafOfModules.toSheaf _ ⟶
      A₁.modules ⋙ SheafOfModules.toSheaf _ :=
    { app := moduleComparisonApp γ A₀ A₁
      naturality := by
        intro M N f
        apply (sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map_injective
        simp only [Functor.map_comp, moduleComparisonApp_underlying]
        simpa only [em, compareMap, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app,
          Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.app_hom,
          Iso.app_inv, Functor.comp_map, Category.assoc] using em.hom.naturality f }
  have (M : ringedSiteModules.{s}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : IsIso (τ.app M) := by
    have : IsIso ((sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map (τ.app M)) := by
      change IsIso ((sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map
          (moduleComparisonApp γ A₀ A₁ M))
      rw [moduleComparisonApp_underlying]
      change IsIso (em.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (sheafCompose K
      (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s}))
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, ?_, ?_⟩
  · intro M
    exact moduleComparisonApp_underlying γ A₀ A₁ M
  · intro M V a x
    exact module_compare_smul γ.hom A₀ A₁ M V a x

private def identityPresentation (R : Sheaf J CommRingCat.{s}) :
    SheafOfModules.AlgebraicInverseImageOfUniverses (𝟭 (Sheaf J (Type s))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private theorem algebraicIdentity
    {I : Sheaf J (Type s) ⥤ Sheaf J (Type s)} (η : 𝟭 _ ≅ I) :
    SiteAlgebraicIdentityUnit η.hom := by
  intro R RI A
  exact algebraicComparison η R R RI (identityPresentation R) A

end FinishTransport

/-- The specified compositor is uniquely unit normalized, including on individual sections;
it respects canonical products, terminal objects and the ring/module operation transports.
The identity inverse-image unit is invertible and has the same algebraic compatibilities.

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (blueprint: lem-pur-site-algebraic-composition-unit).

Proof:
1. Precomposition by v then u is literally precomposition by their composite. The specified
   adjunctions therefore have the same right adjoint. Compose the individual adjunctions
   using def-weil-pbc-composite-adjunction; its unit is eta_v followed by P_v(eta_u).
2. Apply lem-weil-pbc-conjugate-iso-unit-equation to the identity right-adjoint comparison.
   It gives the invertible compositor and uniqueness with the displayed unit normalization.
3. Evaluate that equation at W and s. Conversely, equality at every W and s is equality
   of sheaf morphisms, so the section equation alone gives the same uniqueness.
4. Compose the product equation with each projection and use naturality. The terminal
   equation follows from the unique map to a terminal object. Finite-limit preservation
   makes these canonical comparisons invertible. For the composite functor, successive
   product comparisons have exactly the images of the original projections as components.
5. A transported binary operation o is L(o) after the inverse product comparison, and a
   transported constant is L(e) after the inverse terminal comparison. The previous step
   shows that composite and iterated transports coincide. Naturality of gamma then proves
   preservation of ring addition, multiplication, zero and one. Bijectivity makes this a
   ring-sheaf isomorphism, with precisely the underlying-sheaf comparison recorded here.
6. Apply the same calculation to module addition, zero and scalar action. It gives the
   natural additive comparison and sectionwise semilinearity through the ring comparison.
   Naturality on module morphisms follows from gamma and the presentation identifications
   of def-weil-pbc-algebraic-inverse-image. The modules are exactly those of
   def-weil-sheaf-of-modules-category.
7. Compare the specified identity adjunction with the identity adjunction using the same
   conjugate-unit lemma. Its compositor c satisfies c eta_id = id, so eta_id is c inverse.
   Its product and terminal comparisons are consequently invertible without a further
   finite-limit hypothesis on the identity inverse image.
8. Naturality of eta_id with projections and operation maps gives preservation of the
   ring and module operations, including constants and scalar action. Its already proved
   invertibility yields the asserted ring and natural additive semilinear isomorphisms.
-/
theorem siteAlgebraicCompositionUnit
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L]
    [PreservesFiniteLimits (sheafPullback v
      (Type (max uC vC uD vD uE vE w)) J K)]
    [PreservesFiniteLimits (sheafPullback u
      (Type (max uC vC uD vD uE vE w)) K L)]
    [PreservesFiniteLimits
      (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)] :
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L).map
              ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H)) =
        (sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H))) ∧
    (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C) (x : H.obj.obj (op W)),
      ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H).hom.app
          (op (u.obj (v.obj W)))
          (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
        ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
            ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
          (op (v.obj W))
          (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
            H).hom.app (op W) x)) ∧
    (∀ δ : siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
        sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L,
      (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C)
          (x : H.obj.obj (op W)),
        (δ.hom.app H).hom.app (op (u.obj (v.obj W)))
            (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
          ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
            (op (v.obj W))
            (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
              H).hom.app (op W) x)) →
        δ = siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u) ∧
    (∀ A B : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (A ⨯ B) ≫
          prodComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
            sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) A B =
        prodComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u) A B ≫
          prod.map ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app A)
            ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app B)) ∧
    ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (⊤_ _) ≫
        terminalComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) =
      terminalComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)) ∧
    SiteAlgebraicComparison
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom ∧
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit.app H)) ∧
    SiteAlgebraicIdentityUnit
      (sheafAdjunctionContinuous (𝟭 C) (Type (max uC vC uD vD uE vE w)) J J).unit := by
  let adj₀ := siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u
  let adj₁ := (sheafAdjunctionContinuous v
    (Type (max uC vC uD vD uE vE w)) J K).comp
      (sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L)
  have hu (H : Sheaf J (Type (max uC vC uD vD uE vE w))) :=
    adj₀.unit_leftAdjointUniq_hom_app adj₁ H
  have hid : ∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit.app H) := by
    intro H
    let adj := sheafAdjunctionContinuous (𝟭 C)
      (Type (max uC vC uD vD uE vE w)) J J
    have h := adj.unit_leftAdjointUniq_hom_app (Adjunction.id) H
    change adj.unit.app H ≫ (adj.leftAdjointUniq (Adjunction.id)).hom.app H = 𝟙 H at h
    have he : adj.unit.app H = (adj.leftAdjointUniq (Adjunction.id)).inv.app H := by
      apply (cancel_mono ((adj.leftAdjointUniq (Adjunction.id)).hom.app H)).mp
      simpa using h
    rw [he]
    infer_instance
  refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H W x
    exact congrArg (fun f ↦ f.hom.app (op W) x) (hu H)
  · intro δ hδ
    apply Iso.ext
    apply NatTrans.ext
    funext H
    apply (adj₀.homEquiv _ _).injective
    change (adj₀.homEquiv _ _) (δ.hom.app H) =
      (adj₀.homEquiv _ _) ((adj₀.leftAdjointUniq adj₁).hom.app H)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    ext W x
    exact hδ H W.unop x
  · intro A B
    apply prod.hom_ext <;> simp only [Category.assoc, prodComparison_fst,
      prodComparison_snd, prod.map_fst, prod.map_snd,
      prodComparison_fst_assoc, prodComparison_snd_assoc]
    · exact ((siteAlgebraicCompositionIso J K L v u).hom.naturality (prod.fst : A ⨯ B ⟶ A)).symm
    · exact ((siteAlgebraicCompositionIso J K L v u).hom.naturality (prod.snd : A ⨯ B ⟶ B)).symm
  · apply terminal.hom_ext
  · exact algebraicComparison
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u)
  · exact hid
  · have : IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit) :=
      NatIso.isIso_of_isIso_app _
    exact algebraicIdentity (asIso ((sheafAdjunctionContinuous (𝟭 C)
      (Type (max uC vC uD vD uE vE w)) J J).unit))

end CategoryTheory
