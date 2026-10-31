/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionInflation
public import WeilConjectures.CategoryTheory.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Normalized fixed-subsheaf adjunctions for a product of group sheaves

Source: main-20261015, direct-image stability paragraph (3), agent-formulated
fixed-subsheaf input; Stacks Tags 03CV, 00VH, 00VM, 0037, 0DV0
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).

The action categories and their sectionwise additive structures are the existing
`InternalActionSite.EquivariantSheaf` categories, recorded by the definition node
`def-sfb-equivariant-module-sheaves`. The specifications below identify
invariants by their injective inclusions and exact fixed-section images. No invariant
object or comparison is chosen from an unspecified existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

/-- The pair-valued group restriction maps obey the functor laws.
Source: product of group sheaves in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).
Proof: evaluate each equation on a pair. In each coordinate the identity equation
is the corresponding group presheaf's map-identity law, and the composition equation
is its map-composition law. Extensionality of group homomorphisms concludes. -/
theorem productGroup_laws (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    (∀ X : Cᵒᵖ, GrpCat.ofHom ((K.map (𝟙 X)).hom.prodMap (L.map (𝟙 X)).hom) =
      𝟙 (GrpCat.of (K.obj X × L.obj X))) ∧
    (∀ (X Y Z : Cᵒᵖ) (f : X ⟶ Y) (g : Y ⟶ Z),
      GrpCat.ofHom ((K.map (f ≫ g)).hom.prodMap (L.map (f ≫ g)).hom) =
        GrpCat.ofHom ((K.map f).hom.prodMap (L.map f).hom) ≫
          GrpCat.ofHom ((K.map g).hom.prodMap (L.map g).hom)) := by
  constructor
  · intro X
    simp only [Functor.map_id]
    rfl
  · intro X Y Z f g
    simp only [Functor.map_comp]
    rfl

/-- Sectionwise product, retaining actual pairs of group sections.
Source: product-action calculation in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
def productGroup (K L : Cᵒᵖ ⥤ GrpCat.{u}) : Cᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (K.obj X × L.obj X)
  map f := GrpCat.ofHom ((K.map f).hom.prodMap (L.map f).hom)
  map_id := (productGroup_laws K L).1
  map_comp := (productGroup_laws K L).2 _ _ _

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Inflation along the first projection precomposes the action with `(k,l) ↦ k`.
It leaves every section module and every map unchanged.
Source: projection inflation in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
def inflateFirst (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    EquivariantSheaf (K := K) J R ⥤
      EquivariantSheaf (K := productGroup K L) J R where
  obj M :=
    ⟨⟨M.obj.val,
      { act := fun X ↦ (M.obj.action.act X).comp (MonoidHom.fst _ _)
        naturality := fun f a m ↦ M.obj.action.naturality f a.1 m }⟩, M.property⟩
  map f := ObjectProperty.homMk ⟨f.hom.val, fun X a m ↦ f.hom.property X a.1 m⟩

/-- Fixedness is tested after every base change, including the identity restriction.
Source: invariant-section formula in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
def FixedSection {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) (m : M.obj.val.obj X) : Prop :=
  ∀ (Y : Cᵒᵖ) (f : X ⟶ Y) (p : P.obj Y),
    M.obj.action.act Y p (M.obj.val.map f m) = M.obj.val.map f m

/-- A fixed-subsheaf functor with its normalized additive adjunction. Injectivity and
image specify the displayed subsheaf; the transpose equations retain every section map.
Source: fixed-subsheaf construction and Stacks 0037
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
structure SheafFixedAdjunction (P : Cᵒᵖ ⥤ GrpCat.{u}) where
  /-- Restriction of equivariant maps to invariant sections. -/
  functor : EquivariantSheaf (K := P) J R ⥤ ringedSiteModules.{u} R
  /-- Sectionwise addition is preserved. -/
  additive : functor.Additive
  /-- The natural invariant inclusion. -/
  inclusion : functor ⟶ forgetSheaf (K := P) J R
  /-- Trivial action is additive. -/
  trivial_additive : (trivialSheafAction R P).Additive
  /-- The adjunction with trivial action. -/
  adjunction : trivialSheafAction R P ⊣ functor
  /-- Each component inclusion is injective on sections. -/
  injective (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) :
    Function.Injective ((inclusion.app M).val.app X)
  /-- Its sectionwise image is exactly the displayed invariant subset. -/
  image (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) (m : M.obj.val.obj X) :
    (∃ x : (functor.obj M).val.obj X, (inclusion.app M).val.app X x = m) ↔
      FixedSection R M X m
  /-- Forward transposition restricts the codomain and keeps the map. -/
  transpose (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f : (trivialSheafAction R P).obj A ⟶ M) :
    adjunction.homEquiv A M f ≫ inclusion.app M = ⟨f.hom.val⟩
  /-- Inverse transposition composes with the invariant inclusion. -/
  untranspose (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f : A ⟶ functor.obj M) :
    ((adjunction.homEquiv A M).symm f).hom.val = (f ≫ inclusion.app M).val
  /-- The normalized Hom bijection preserves sums. -/
  transpose_add (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f g : (trivialSheafAction R P).obj A ⟶ M) :
    adjunction.homEquiv A M (f + g) =
      adjunction.homEquiv A M f + adjunction.homEquiv A M g

/-- Second-factor invariants with their residual first-factor action and normalized
adjunction. All section formulas refer to the existing equivariant module categories.
Source: commuting-factor calculation and Stacks 0037
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
structure SheafProductFixedAdjunction (K L : Cᵒᵖ ⥤ GrpCat.{u}) where
  /-- Invariants under the second factor retain the first-factor action. -/
  functor : EquivariantSheaf (K := productGroup K L) J R ⥤
    EquivariantSheaf (K := K) J R
  /-- Restriction of sums is addition of restricted maps. -/
  additive : functor.Additive
  /-- The natural second-factor invariant inclusion. -/
  inclusion : functor ⋙ forgetSheaf (K := K) J R ⟶
    forgetSheaf (K := productGroup K L) J R
  /-- First-projection inflation is additive. -/
  inflation_additive : (inflateFirst R K L).Additive
  /-- Inflation is left adjoint to second-factor invariants. -/
  adjunction : inflateFirst R K L ⊣ functor
  /-- The invariant inclusion is sectionwise injective. -/
  injective (M : EquivariantSheaf (K := productGroup K L) J R) (X : Cᵒᵖ) :
    Function.Injective ((inclusion.app M).val.app X)
  /-- Its image consists of the sections fixed by `(1,l)` after every restriction. -/
  image (M : EquivariantSheaf (K := productGroup K L) J R) (X : Cᵒᵖ)
      (m : M.obj.val.obj X) :
    (∃ x : (functor.obj M).obj.val.obj X, (inclusion.app M).val.app X x = m) ↔
      ∀ (Y : Cᵒᵖ) (f : X ⟶ Y) (l : L.obj Y),
        M.obj.action.act Y (1, l) (M.obj.val.map f m) = M.obj.val.map f m
  /-- The residual action is exactly the action of `(k,1)` under the inclusion. -/
  residual (M : EquivariantSheaf (K := productGroup K L) J R) (X : Cᵒᵖ)
      (k : K.obj X) (x : (functor.obj M).obj.val.obj X) :
    (inclusion.app M).val.app X ((functor.obj M).obj.action.act X k x) =
      M.obj.action.act X (k, 1) ((inclusion.app M).val.app X x)
  /-- The equivariant forward transpose keeps the section map. -/
  transpose (A : EquivariantSheaf (K := K) J R)
      (M : EquivariantSheaf (K := productGroup K L) J R)
      (f : (inflateFirst R K L).obj A ⟶ M) :
    ((adjunction.homEquiv A M f).hom.val) ≫ (inclusion.app M).val = f.hom.val
  /-- The inverse transpose composes with the inclusion. -/
  untranspose (A : EquivariantSheaf (K := K) J R)
      (M : EquivariantSheaf (K := productGroup K L) J R)
      (f : A ⟶ functor.obj M) :
    ((adjunction.homEquiv A M).symm f).hom.val = f.hom.val ≫ (inclusion.app M).val
  /-- The equivariant Hom bijection is additive. -/
  transpose_add (A : EquivariantSheaf (K := K) J R)
      (M : EquivariantSheaf (K := productGroup K L) J R)
      (f g : (inflateFirst R K L).obj A ⟶ M) :
    adjunction.homEquiv A M (f + g) =
      adjunction.homEquiv A M f + adjunction.homEquiv A M g

private def fixedSubmodule {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) : M.obj.val.Submodule where
  obj X :=
    { carrier := {m | FixedSection R M X m}
      zero_mem' := by intro Y f p; simp
      add_mem' := by
        intro m n hm hn Y f p
        simp only [map_add, hm Y f p, hn Y f p]
      smul_mem' := by
        intro a m hm Y f p
        rw [M.obj.val.map_smul, map_smul, hm Y f p] }
  map {X Y} f := by
    intro m hm Z g p
    simpa only [PresheafOfModules.restrictₛₗ_apply,
      ← PresheafOfModules.map_comp_apply] using hm Z (f ≫ g) p

private def fixedSubfunctor {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) :
    Subfunctor (M.obj.val.presheaf ⋙ forget AddCommGrpCat.{u}) where
  obj X := {m | FixedSection R M X m}
  map f := (fixedSubmodule R M).map f

private theorem fixed_isSheaf {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) :
    Presheaf.IsSheaf J (fixedSubmodule R M).toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have hM : Presieve.IsSheaf J (M.obj.val.presheaf ⋙ forget AddCommGrpCat.{u}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u})]
    exact M.property
  change Presieve.IsSheaf J (fixedSubfunctor R M).toFunctor
  -- Membership in the fixed submodule is local; separatedness detects the action equation.
  apply (Subfunctor.isSheaf_iff _ hM).2
  intro X m hm Y f p
  apply (hM _ (J.pullback_stable f.unop hm)).isSeparatedFor.ext
  intro Z g hg
  change M.obj.val.map g.op (M.obj.action.act Y p (M.obj.val.map f m)) =
    M.obj.val.map g.op (M.obj.val.map f m)
  rw [M.obj.action.naturality]
  have hfix : FixedSection R M (op Z) (M.obj.val.map (g ≫ f.unop).op m) := hg
  have he := hfix (op Z) (𝟙 _) (P.map g.op p)
  simpa [PresheafOfModules.map_comp_apply] using he

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedSheaf {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) : ringedSiteModules.{u} R :=
  ⟨(fixedSubmodule R M).toPresheafOfModules, fixed_isSheaf R M⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedMap {P : Cᵒᵖ ⥤ GrpCat.{u}}
    {M N : EquivariantSheaf (K := P) J R} (a : M ⟶ N) :
    fixedSheaf R M ⟶ fixedSheaf R N where
  val :=
    { app X := ModuleCat.ofHom
        { toFun := fun x ↦ ⟨a.hom.val.app X x.val, by
            intro Y f p
            rw [← PresheafOfModules.naturality_apply]
            rw [← a.hom.property, x.property Y f p]⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      naturality := by
        intro X Y f
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply a.hom.val f x.val }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedFunctor (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    EquivariantSheaf (K := P) J R ⥤ ringedSiteModules.{u} R where
  obj M := fixedSheaf R M
  map a := fixedMap R a
  map_id M := by ext X x; rfl
  map_comp a b := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedInclusion (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    fixedFunctor R P ⟶ forgetSheaf (K := P) J R where
  app M := ⟨(fixedSubmodule R M).ι⟩
  naturality {M N} a := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedHomEquiv (P : Cᵒᵖ ⥤ GrpCat.{u})
    (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R) :
    ((trivialSheafAction R P).obj A ⟶ M) ≃ (A ⟶ (fixedFunctor R P).obj M) where
  toFun a :=
    ⟨{ app X := ModuleCat.ofHom
        { toFun := fun x ↦ ⟨a.hom.val.app X x, by
            intro Y f p
            rw [← PresheafOfModules.naturality_apply]
            exact (a.hom.property Y p (A.val.map f x)).symm⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
       naturality := by
         intro X Y f
         ext x
         apply Subtype.ext
         exact PresheafOfModules.naturality_apply a.hom.val f x }⟩
  invFun a := ObjectProperty.homMk
    ⟨a.val ≫ (fixedSubmodule R M).ι, by
      intro X p x
      have h := (a.val.app X x).property X (𝟙 X) p
      change (a.val.app X x).val = M.obj.action.act X p (a.val.app X x).val
      simpa using h.symm⟩
  left_inv a := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl
  right_inv a := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedAdjunction (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    SheafFixedAdjunction R P where
  functor := fixedFunctor R P
  additive := { map_add := by intros; ext X x; rfl }
  inclusion := fixedInclusion R P
  trivial_additive :=
    { map_add := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        rfl }
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := fixedHomEquiv R P
      homEquiv_naturality_left_symm := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        ext X x
        rfl
      homEquiv_naturality_right := by intros; ext X x; rfl }
  injective M X := Subtype.val_injective
  image M X m := ⟨fun ⟨x,h⟩ ↦ h ▸ x.property, fun h ↦ ⟨⟨m,h⟩,rfl⟩⟩
  transpose A M a := by ext X x; rfl
  untranspose A M a := rfl
  transpose_add A M a b := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private def secondAction (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (M : EquivariantSheaf (K := productGroup K L) J R) :
    EquivariantSheaf (K := L) J R :=
  ⟨⟨M.obj.val,
    { act := fun X ↦ (M.obj.action.act X).comp (MonoidHom.inr _ _)
      naturality := by
        intro X Y f l m
        simpa [productGroup] using M.obj.action.naturality f (1, l) m }⟩, M.property⟩

set_option backward.isDefEq.respectTransparency false in
private theorem factors_commute (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (M : EquivariantSheaf (K := productGroup K L) J R)
    (X : Cᵒᵖ) (k : K.obj X) (l : L.obj X) (m : M.obj.val.obj X) :
    M.obj.action.act X (1,l) (M.obj.action.act X (k,1) m) =
      M.obj.action.act X (k,1) (M.obj.action.act X (1,l) m) := by
  have hp : (1,l) * (k,1) = (k,1) * (1,l) := by ext <;> simp
  have he := congrArg (fun p ↦ M.obj.action.act X p m) hp
  simpa only [map_mul, Module.End.mul_apply] using he

set_option backward.isDefEq.respectTransparency false in
private noncomputable def residualAction (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (M : EquivariantSheaf (K := productGroup K L) J R) :
    LinearAction K (fixedSheaf R (secondAction R K L M)).val where
  act X :=
    { toFun := fun k ↦
        { toFun := fun x ↦ ⟨M.obj.action.act X (k,1) x.val, by
            intro Y f l
            change M.obj.action.act Y (1,l)
              (M.obj.val.map f (M.obj.action.act X (k,1) x.val)) =
                M.obj.val.map f (M.obj.action.act X (k,1) x.val)
            rw [M.obj.action.naturality]
            have hp : (productGroup K L).map f (k,1) = (K.map f k,1) := by
              change (K.map f k, L.map f 1) = (K.map f k,1)
              rw [map_one]
            rw [hp, factors_commute R K L M]
            exact congrArg (M.obj.action.act Y (K.map f k,1)) (x.property Y f l)⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      map_one' := by
        ext x
        apply Subtype.ext
        change M.obj.action.act X (1 : (productGroup K L).obj X) x.val = x.val
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        ext x
        apply Subtype.ext
        change M.obj.action.act X (a*b,1) x.val =
          M.obj.action.act X (a,1) (M.obj.action.act X (b,1) x.val)
        have hp : ((a,1) : (productGroup K L).obj X) * (b,1) = (a*b,1) := by
          ext <;> simp
        rw [← hp, map_mul]
        rfl }
  naturality := by
    intro X Y f k x
    apply Subtype.ext
    change M.obj.val.map f (M.obj.action.act X (k,1) x.val) =
      M.obj.action.act Y (K.map f k,1) (M.obj.val.map f x.val)
    have hp : (productGroup K L).map f (k,1) = (K.map f k,1) := by
      change (K.map f k, L.map f 1) = (K.map f k,1)
      rw [map_one]
    exact (M.obj.action.naturality f (k,1) x.val).trans
      (congrArg (fun p ↦ M.obj.action.act Y p (M.obj.val.map f x.val)) hp)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def secondFixed (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (M : EquivariantSheaf (K := productGroup K L) J R) :
    EquivariantSheaf (K := K) J R :=
  ⟨⟨(fixedSheaf R (secondAction R K L M)).val, residualAction R K L M⟩,
    (fixedSheaf R (secondAction R K L M)).isSheaf⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def secondFixedMap (K L : Cᵒᵖ ⥤ GrpCat.{u})
    {M N : EquivariantSheaf (K := productGroup K L) J R} (a : M ⟶ N) :
    secondFixed R K L M ⟶ secondFixed R K L N :=
  ObjectProperty.homMk
    ⟨(fixedMap R (ObjectProperty.homMk ⟨a.hom.val, fun X l m ↦
      a.hom.property X (1,l) m⟩ : secondAction R K L M ⟶ secondAction R K L N)).val,
      by
        intro X k x
        apply Subtype.ext
        exact a.hom.property X (k,1) x.val⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def secondFixedFunctor (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    EquivariantSheaf (K := productGroup K L) J R ⥤ EquivariantSheaf (K := K) J R where
  obj M := secondFixed R K L M
  map a := secondFixedMap R K L a
  map_id M := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def secondFixedInclusion (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    secondFixedFunctor R K L ⋙ forgetSheaf (K := K) J R ⟶
      forgetSheaf (K := productGroup K L) J R where
  app M := ⟨(fixedSubmodule R (secondAction R K L M)).ι⟩
  naturality {M N} a := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def secondFixedHomEquiv (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (A : EquivariantSheaf (K := K) J R)
    (M : EquivariantSheaf (K := productGroup K L) J R) :
    ((inflateFirst R K L).obj A ⟶ M) ≃ (A ⟶ (secondFixedFunctor R K L).obj M) where
  toFun a := ObjectProperty.homMk
    ⟨{ app X := ModuleCat.ofHom
        { toFun := fun x ↦ ⟨a.hom.val.app X x, by
            intro Y f l
            change M.obj.action.act Y (1,l) (M.obj.val.map f (a.hom.val.app X x)) =
              M.obj.val.map f (a.hom.val.app X x)
            rw [← PresheafOfModules.naturality_apply]
            have he := a.hom.property Y (1,l) (A.obj.val.map f x)
            change a.hom.val.app Y (A.obj.action.act Y 1 (A.obj.val.map f x)) = _ at he
            rw [map_one] at he
            exact he.symm⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
       naturality := by
         intro X Y f
         ext x
         apply Subtype.ext
         exact PresheafOfModules.naturality_apply a.hom.val f x }, by
      intro X k x
      apply Subtype.ext
      exact a.hom.property X (k,1) x⟩
  invFun a := ObjectProperty.homMk
    ⟨a.hom.val ≫ (fixedSubmodule R (secondAction R K L M)).ι, by
      intro X p x
      change (a.hom.val.app X (A.obj.action.act X p.1 x)).val =
        M.obj.action.act X p (a.hom.val.app X x).val
      have he := congrArg Subtype.val (a.hom.property X p.1 x)
      change _ = M.obj.action.act X (p.1,1) (a.hom.val.app X x).val at he
      rw [he]
      have hf := (a.hom.val.app X x).property X (𝟙 X) p.2
      have hf' : M.obj.action.act X (1,p.2) (a.hom.val.app X x).val =
          (a.hom.val.app X x).val := by
        change M.obj.action.act X (1,p.2)
          (M.obj.val.map (𝟙 X) (a.hom.val.app X x).val) =
            M.obj.val.map (𝟙 X) (a.hom.val.app X x).val at hf
        simpa using hf
      calc
        M.obj.action.act X (p.1,1) (a.hom.val.app X x).val =
            M.obj.action.act X (p.1,1)
              (M.obj.action.act X (1,p.2) (a.hom.val.app X x).val) :=
          congrArg (M.obj.action.act X (p.1,1)) hf'.symm
        _ = M.obj.action.act X p (a.hom.val.app X x).val := by
          rw [← Module.End.mul_apply, ← map_mul]
          have hp : ((p.1,1) : (productGroup K L).obj X) * (1,p.2) = p := by
            exact Prod.ext (mul_one p.1) (one_mul p.2)
          rw [hp]⟩
  left_inv a := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl
  right_inv a := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def productFixedAdjunction (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    SheafProductFixedAdjunction R K L where
  functor := secondFixedFunctor R K L
  additive :=
    { map_add := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        ext X x
        rfl }
  inclusion := secondFixedInclusion R K L
  inflation_additive :=
    { map_add := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        rfl }
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := secondFixedHomEquiv R K L
      homEquiv_naturality_left_symm := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        ext X x
        rfl
      homEquiv_naturality_right := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        ext X x
        rfl }
  injective M X := Subtype.val_injective
  image M X m := ⟨fun ⟨x,h⟩ ↦ h ▸ x.property, fun h ↦ ⟨⟨m,h⟩,rfl⟩⟩
  residual M X k x := rfl
  transpose A M a := by ext X x; rfl
  untranspose A M a := rfl
  transpose_add A M a b := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl

private theorem trivial_product (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    trivialSheafAction R (productGroup K L) =
      trivialSheafAction R K ⋙ inflateFirst R K L := by
  rfl

set_option linter.unusedVariables false in
/-- Fixed subsheaves, normalized adjunctions and the normalized product conjugate.
Source: main-20261015, direct-image stability paragraph (3), agent-formulated
categorical input; Stacks 03CV, 00VH, 00VM, 0037, 0DV0
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).

Proof:
1. The fixed-section condition is closed under zero, sums, negatives and scalars by
   linearity. Quantification over all restrictions gives restriction stability, using
   `def-weil-sheaf-of-modules-category`.
2. Glue matching fixed sections in the underlying module sheaf. Pull the covering back
   along each test restriction. Naturality of the action and fixedness on that pulled-back
   cover identify the two tested sections locally, hence globally by sheaf uniqueness.
   This uses `def-weil-pbc-sites-and-cohomology`, including empty covers.
3. The commuting factors preserve second-factor invariants and induce the residual
   `(k,1)` action. Restrict equivariant maps; identities, composites and sums restrict
   sectionwise. This constructs all additive functors and natural injective inclusions.
4. For trivial-action inflation restrict an equivariant map's codomain to invariants.
   Conversely compose with the inclusion. These operations are inverse, natural and
   additive on every section. Apply `lem-weil-pbc-adjunction-of-natural-bijection`.
5. For first-projection inflation the same codomain restriction is K-equivariant for
   the specified residual action. Conversely `(k,l)=(k,1)(1,l)` proves equivariance
   after inclusion. The inverse natural additive bijections give the second adjunction.
6. Direct and successive trivial actions agree. Fixedness under all pairs is equivalent
   after every restriction to fixedness under both factors. The identity on section
   values gives inverse linear natural maps between direct and successive invariants.
7. Compose the normalized adjunctions by `def-weil-pbc-composite-adjunction`.
   Its counit is the composite of the two inclusions. Evaluate the formula from
   `def-weil-pbc-adjunction-conjugate`: the composite unit keeps the fixed section,
   and the image of the direct counit includes the same section. Thus the conjugate is
   precisely the preceding identity on section values. Unit laws include trivial factors;
   a zero coefficient ring forces every module section to be zero and all formulas persist.
-/
theorem sheaf_product_fixed_adjunction [HasFiniteLimits C] (J₀ : Precoverage C)
    (hJ : J₀.IsSiteForCoverings) (S : Sheaf J₀.toGrothendieck CommRingCat.{u})
    (K L : Sheaf J₀.toGrothendieck GrpCat.{u}) :
    ∃ (dK : SheafFixedAdjunction (baseRing J₀.toGrothendieck S) K.obj)
      (dL : SheafFixedAdjunction (baseRing J₀.toGrothendieck S) L.obj)
      (dKL : SheafFixedAdjunction (baseRing J₀.toGrothendieck S) (productGroup K.obj L.obj))
      (dLK : SheafProductFixedAdjunction (baseRing J₀.toGrothendieck S) K.obj L.obj)
      (h : trivialSheafAction (baseRing J₀.toGrothendieck S) (productGroup K.obj L.obj) =
        trivialSheafAction (baseRing J₀.toGrothendieck S) K.obj ⋙
          inflateFirst (baseRing J₀.toGrothendieck S) K.obj L.obj),
      ∀ (M : EquivariantSheaf (K := productGroup K.obj L.obj) J₀.toGrothendieck
        (baseRing J₀.toGrothendieck S)) (X : Cᵒᵖ) (x : (dKL.functor.obj M).val.obj X),
        ((dK.inclusion.app (dLK.functor.obj M) ≫ dLK.inclusion.app M).val.app X)
          (((((conjugateIsoEquiv dKL.adjunction (dK.adjunction.comp dLK.adjunction))
            (eqToIso h.symm)).hom.app M).val.app X) x) =
          (dKL.inclusion.app M).val.app X x := by
  let R₀ := baseRing J₀.toGrothendieck S
  let dK := fixedAdjunction R₀ K.obj
  let dKL := fixedAdjunction R₀ (productGroup K.obj L.obj)
  let dLK := productFixedAdjunction R₀ K.obj L.obj
  let h := trivial_product R₀ K.obj L.obj
  refine ⟨dK, fixedAdjunction R₀ L.obj, dKL, dLK, h, ?_⟩
  intro M X x
  -- The normalized counits are the displayed inclusions, also for the composite.
  have he := conjugateEquiv_counit dKL.adjunction (dK.adjunction.comp dLK.adjunction)
    (eqToIso h.symm).hom M
  have hs := congrArg (fun a ↦ a.hom.val.app X x) he
  exact hs

end CategoryTheory.InternalActionSite
