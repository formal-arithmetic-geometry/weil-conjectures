/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteInverseImageTensor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Sheaf.CategoryTheory.Sites.NormalizedSliceInverseImage
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Inverse image of a compatible free inverse tower

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, integral twist paragraph;
Stacks Project, Sites, Tag 03CF (blueprint: lem-pur-inverse-image-compatible-free-tower).

The comparisons are `limit.post` for the actual Kan-extension/sheafification inverse image.
We use underlying set sheaves to express varying-coefficient scalar actions by morphisms
out of binary products. All scalar actions and local identifications are normalized by
explicit projection equations. The natural-number index `n` represents level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- A commutative-ring tower with its module sheaves and additive semilinear transitions.
Source: the integral twist paragraph of `sk-prop-sfb-cartesian-coefficients-twists.proof.md`
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
structure PurCompatibleFreeTowerData (J : GrothendieckTopology C) where
  R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u + 1}
  M : ∀ n : ℕ, ringedSiteModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.obj (op n)))
  t : ∀ n : ℕ,
    (SheafOfModules.toSheaf _).obj (M (n + 1)) ⟶ (SheafOfModules.toSheaf _).obj (M n)
  semilinear : ∀ (n : ℕ) (W : Cᵒᵖ)
    (a : (R.obj (op (n + 1))).obj.obj W) (x : (M (n + 1)).val.obj W),
    (t n).hom.app W (a • x) =
      @SMul.smul _ ((M n).val.obj W) inferInstance
        ((R.map (homOfLE (Nat.le_succ n)).op).hom.app W a) ((t n).hom.app W x)

namespace PurCompatibleFreeTowerData

variable (T : PurCompatibleFreeTowerData J)

/-- The coefficient ring at level `n + 1`, forgetting only commutativity.
Source: the integral twist paragraph (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
abbrev ring (n : ℕ) : Sheaf J RingCat.{u + 1} :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (T.R.obj (op n))

/-- The underlying set-sheaf ring tower; limits retain their sectionwise operations.
Source: def-pur-sheaf-inverse-limit
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def rings : ℕᵒᵖ ⥤ Sheaf J (Type (u + 1)) :=
  T.R ⋙ sheafCompose J (forget CommRingCat.{u + 1})

/-- The actual additive tower, with all transition composites supplied by Mathlib.
Source: the integral twist paragraph (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def abelian : ℕᵒᵖ ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    (SheafOfModules.toSheaf (T.ring n)).obj (T.M n)) T.t

/-- The underlying set-sheaf module tower.
Source: def-pur-sheaf-inverse-limit
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def modules : ℕᵒᵖ ⥤ Sheaf J (Type (u + 1)) :=
  T.abelian ⋙ sheafCompose J (forget AddCommGrpCat.{u + 1})

/-- Scalar multiplication at one level, as a morphism of set sheaves.
Source: def-weil-sheaf-of-modules-category
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def scalar (n : ℕ) : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶
    T.modules.obj (op n) where
  hom.app W := ↾(fun x ↦ @SMul.smul ((T.ring n).obj.obj W) ((T.M n).val.obj W)
    inferInstance ((prod.fst : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W x)
      ((prod.snd : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W x))
  hom.naturality W Z f := by
    ext x
    symm
    change (T.M n).val.map f
      (@SMul.smul ((T.ring n).obj.obj W) ((T.M n).val.obj W) inferInstance
        ((prod.fst : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W x)
        ((prod.snd : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W x)) = _
    refine (PresheafOfModules.map_smul (T.M n).val f _ _).trans ?_
    congr 1
    · exact (ConcreteCategory.congr_hom (NatTrans.naturality
        (prod.fst : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom f) x).symm
    · exact (ConcreteCategory.congr_hom (NatTrans.naturality
        (prod.snd : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom f) x).symm

/-- The underlying local basis isomorphism, using the existing localization of modules.
Source: def-pur-localized-ringed-site and the integral twist paragraph
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def basisIso (V : C) (n : ℕ)
    (b : (SheafOfModules.unit (T.ring n)).over V ≅ (T.M n).over V) :
    (T.rings.obj (op n)).over V ≅ (T.modules.obj (op n)).over V :=
  (sheafCompose (J.over V) (forget AddCommGrpCat.{u + 1})).mapIso
    ((SheafOfModules.toSheaf ((T.ring n).over V)).mapIso b)

/-- Compatibility of the chosen linear bases with the semilinear transitions.
Source: the integral twist paragraph (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def CompatibleBases (V : C)
    (b : ∀ n : ℕ, (SheafOfModules.unit (T.ring n)).over V ≅ (T.M n).over V) : Prop :=
  ∀ n : ℕ,
    (T.basisIso V (n + 1) (b (n + 1))).hom ≫
        (J.overPullback (Type (u + 1)) V).map
          (T.modules.map (homOfLE (Nat.le_succ n)).op) =
      (J.overPullback (Type (u + 1)) V).map
          (T.rings.map (homOfLE (Nat.le_succ n)).op) ≫ (T.basisIso V n (b n)).hom

end PurCompatibleFreeTowerData

/-- The geometric inverse image, literally left Kan extension followed by sheafification.
Source: lem-weil-pbc-left-exact-site-inverse-image-tensor
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def purTowerInverseImage {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) :
    Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K

/-- The Kan-extension/sheafification unit, on sections, without a chosen adjunction.
Source: the inverse-image construction and Stacks 03CF
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def purTowerInverseImageUnit {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) (F : Sheaf J (Type (u + 1))) :
    F.obj ⟶ U.op ⋙ ((purTowerInverseImage K U).obj F).obj :=
  (U.op.lanAdjunction (Type (u + 1))).unit.app F.obj ≫
    Functor.whiskerLeft U.op (toSheafify K (U.op.lan.obj F.obj))

/-- Characterization of the inverse image of a local isomorphism by the actual unit.
The equation is imposed on every object over `V` and every section; it determines the
localized map of inverse images, including after base change to arbitrary slice objects.
Source: Stacks 03CF (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def PurTowerLocalInverseImage {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) {F G : Sheaf J (Type (u + 1))}
    (V : C) (b : F.over V ≅ G.over V)
    (b' : ((purTowerInverseImage K U).obj F).over (U.obj V) ≅
      ((purTowerInverseImage K U).obj G).over (U.obj V)) : Prop :=
  ∀ (W : C) (q : W ⟶ V) (x : F.obj.obj (op W)),
    b'.hom.hom.app (op (Over.mk (U.map q)))
        ((purTowerInverseImageUnit K U F).app (op W) x) =
      (purTowerInverseImageUnit K U G).app (op W)
        (b.hom.hom.app (op (Over.mk q)) x)

namespace PurCompatibleFreeTowerData

variable (T : PurCompatibleFreeTowerData J)

/-- The scalar-action and linearity clauses, with every operation uniquely specified.
`a` is the coordinatewise action on the source limit. `a'` and `s n` are its inverse
image and the inverse images of the level actions, specified using product comparisons.
`c` is the coordinatewise action of the limit of the inverse-image rings. The last
identity is precisely linearity of the module comparison over the ring comparison.
Source: the integral twist paragraph (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def ScalarComparison {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))) : Prop :=
  ∃ (a : limit T.rings ⨯ limit T.modules ⟶ limit T.modules)
    (a' : L.obj (limit T.rings) ⨯ L.obj (limit T.modules) ⟶ L.obj (limit T.modules))
    (s : ∀ n : ℕ, L.obj (T.rings.obj (op n)) ⨯ L.obj (T.modules.obj (op n)) ⟶
      L.obj (T.modules.obj (op n)))
    (c : limit (T.rings ⋙ L) ⨯ limit (T.modules ⋙ L) ⟶ limit (T.modules ⋙ L)),
    (∀ n : ℕ, a ≫ limit.π T.modules (op n) =
      prod.map (limit.π T.rings (op n)) (limit.π T.modules (op n)) ≫ T.scalar n) ∧
    prodComparison L (limit T.rings) (limit T.modules) ≫ a' = L.map a ∧
    (∀ n : ℕ, prodComparison L (T.rings.obj (op n)) (T.modules.obj (op n)) ≫ s n =
      L.map (T.scalar n)) ∧
    (∀ n : ℕ, c ≫ limit.π (T.modules ⋙ L) (op n) =
      prod.map (limit.π (T.rings ⋙ L) (op n)) (limit.π (T.modules ⋙ L) (op n)) ≫ s n) ∧
    a' ≫ limit.post T.modules L =
      prod.map (limit.post T.rings L) (limit.post T.modules L) ≫ c

/-- The local-basis clauses: bases induce limit isomorphisms; their inverse images and
levelwise inverse images identify the module comparison with the ring comparison.
Every intermediate isomorphism is fixed by projection equations or the actual unit,
so this does not ask for arbitrary identifications of unrelated objects.
Source: the integral twist paragraph and Stacks 03CF
(blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def LocalComparison {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) (V : C)
    (b : ∀ n : ℕ, (SheafOfModules.unit (T.ring n)).over V ≅ (T.M n).over V) : Prop :=
  ∃ B : (limit T.rings).over V ≅ (limit T.modules).over V,
    (∀ n : ℕ, B.hom ≫ (J.overPullback (Type (u + 1)) V).map (limit.π T.modules (op n)) =
      (J.overPullback (Type (u + 1)) V).map (limit.π T.rings (op n)) ≫
        (T.basisIso V n (b n)).hom) ∧
    ∃ B' : ((purTowerInverseImage K U).obj (limit T.rings)).over (U.obj V) ≅
        ((purTowerInverseImage K U).obj (limit T.modules)).over (U.obj V),
      PurTowerLocalInverseImage K U V B B' ∧
      ∃ b' : ∀ n : ℕ,
          ((purTowerInverseImage K U).obj (T.rings.obj (op n))).over (U.obj V) ≅
            ((purTowerInverseImage K U).obj (T.modules.obj (op n))).over (U.obj V),
        (∀ n : ℕ, PurTowerLocalInverseImage K U V (T.basisIso V n (b n)) (b' n)) ∧
        ∃ B'' : (limit (T.rings ⋙ purTowerInverseImage K U)).over (U.obj V) ≅
            (limit (T.modules ⋙ purTowerInverseImage K U)).over (U.obj V),
          (∀ n : ℕ, B''.hom ≫ (K.overPullback (Type (u + 1)) (U.obj V)).map
                (limit.π (T.modules ⋙ purTowerInverseImage K U) (op n)) =
            (K.overPullback (Type (u + 1)) (U.obj V)).map
                (limit.π (T.rings ⋙ purTowerInverseImage K U) (op n)) ≫ (b' n).hom) ∧
          B'.hom ≫ (K.overPullback (Type (u + 1)) (U.obj V)).map
              (limit.post T.modules (purTowerInverseImage K U)) =
            (K.overPullback (Type (u + 1)) (U.obj V)).map
                (limit.post T.rings (purTowerInverseImage K U)) ≫ B''.hom

/-- Naturality for homomorphisms of ring towers and compatible semilinear module maps.
The ring map is a natural transformation in commutative-ring sheaves, the module map
one in abelian sheaves; the displayed sectionwise condition is semilinearity.
Source: the integral twist paragraph (blueprint: lem-pur-inverse-image-compatible-free-tower). -/
def NaturalComparison {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))) : Prop :=
  ∀ (T' : PurCompatibleFreeTowerData J) (r : T.R ⟶ T'.R) (m : T.abelian ⟶ T'.abelian),
    (∀ (n : ℕ) (W : Cᵒᵖ) (a : (T.R.obj (op n)).obj.obj W) (x : (T.M n).val.obj W),
      (m.app (op n)).hom.app W (a • x) =
        @SMul.smul ((T'.ring n).obj.obj W) ((T'.M n).val.obj W) inferInstance
          ((r.app (op n)).hom.app W a) ((m.app (op n)).hom.app W x)) →
    L.map (lim.map (Functor.whiskerRight m
        (sheafCompose J (forget AddCommGrpCat.{u + 1})))) ≫ limit.post T'.modules L =
      limit.post T.modules L ≫ lim.map (Functor.whiskerRight
        (Functor.whiskerRight m (sheafCompose J (forget AddCommGrpCat.{u + 1}))) L)

end PurCompatibleFreeTowerData

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_natural_comparison
    (T : PurCompatibleFreeTowerData J)
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))) :
    T.NaturalComparison L := by
  intro T' r m hm
  exact limit.map_post (Functor.whiskerRight m
    (sheafCompose J (forget AddCommGrpCat.{u + 1}))) L

set_option backward.isDefEq.respectTransparency.types false in
private abbrev towerProduct
    {A : Type*} [Category A] [HasBinaryProducts A] (F G : ℕᵒᵖ ⥤ A) : ℕᵒᵖ ⥤ A where
  obj j := F.obj j ⨯ G.obj j
  map f := prod.map (F.map f) (G.map f)
  map_id j := by simp
  map_comp f g := by simp [prod.map_map]

set_option backward.isDefEq.respectTransparency.types false in
private def towerScalar (T : PurCompatibleFreeTowerData J) :
    towerProduct T.rings T.modules ⟶ T.modules :=
  NatTrans.ofOpSequence (T.scalar) (by
    intro n
    dsimp only [towerProduct]
    ext W x
    change @SMul.smul ((T.ring n).obj.obj W) ((T.M n).val.obj W) _
      ((prod.fst : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W
        ((prod.map (T.rings.map (homOfLE (Nat.le_succ n)).op)
          (T.modules.map (homOfLE (Nat.le_succ n)).op)).hom.app W x))
      ((prod.snd : T.rings.obj (op n) ⨯ T.modules.obj (op n) ⟶ _).hom.app W
        ((prod.map (T.rings.map (homOfLE (Nat.le_succ n)).op)
          (T.modules.map (homOfLE (Nat.le_succ n)).op)).hom.app W x)) =
      (T.modules.map (homOfLE (Nat.le_succ n)).op).hom.app W
        (@SMul.smul ((T.ring (n + 1)).obj.obj W) ((T.M (n + 1)).val.obj W) _
          ((prod.fst : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶ _).hom.app W x)
          ((prod.snd : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶ _).hom.app W x))
    have hfst := ConcreteCategory.congr_hom
      (congrArg (fun f : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶
          T.rings.obj (op n) ↦ f.hom.app W) (prod.map_fst
        (T.rings.map (homOfLE (Nat.le_succ n)).op)
        (T.modules.map (homOfLE (Nat.le_succ n)).op))) x
    have hsnd := ConcreteCategory.congr_hom
      (congrArg (fun f : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶
          T.modules.obj (op n) ↦ f.hom.app W) (prod.map_snd
        (T.rings.map (homOfLE (Nat.le_succ n)).op)
        (T.modules.map (homOfLE (Nat.le_succ n)).op))) x
    dsimp at hfst hsnd
    rw [hfst, hsnd]
    simp only [PurCompatibleFreeTowerData.modules, PurCompatibleFreeTowerData.abelian,
      Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact (T.semilinear n W
        ((prod.fst : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶ _).hom.app W x)
        ((prod.snd : T.rings.obj (op (n + 1)) ⨯ T.modules.obj (op (n + 1)) ⟶ _).hom.app W x)).symm)

set_option backward.isDefEq.respectTransparency.types false in
private abbrev towerAction
    {A : Type*} [Category A] [HasBinaryProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (F G : ℕᵒᵖ ⥤ A) (s : towerProduct F G ⟶ G) :
    limit F ⨯ limit G ⟶ limit G :=
  limit.lift G
    { pt := limit F ⨯ limit G
      π :=
        { app := fun j ↦ prod.map (limit.π F j) (limit.π G j) ≫ s.app j
          naturality := by
            intro i j f
            change 𝟙 _ ≫ _ = _
            simp only [Category.id_comp, Category.assoc]
            rw [← s.naturality f]
            change _ = prod.map (limit.π F i) (limit.π G i) ≫
              prod.map (F.map f) (G.map f) ≫ s.app j
            rw [← Category.assoc, prod.map_map, limit.w, limit.w] } }

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem towerAction_π
    {A : Type*} [Category A] [HasBinaryProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (F G : ℕᵒᵖ ⥤ A) (s : towerProduct F G ⟶ G) (j : ℕᵒᵖ) :
    towerAction F G s ≫ limit.π G j =
      prod.map (limit.π F j) (limit.π G j) ≫ s.app j :=
  limit.lift_π _ _


set_option backward.isDefEq.respectTransparency.types false in
private def transportedScalar
    {A B : Type*} [Category A] [Category B] [HasBinaryProducts A] [HasBinaryProducts B]
    (F G : ℕᵒᵖ ⥤ A) (s : towerProduct F G ⟶ G) (L : A ⥤ B)
    [PreservesLimitsOfShape (Discrete WalkingPair) L] :
    towerProduct (F ⋙ L) (G ⋙ L) ⟶ G ⋙ L where
  app j := inv (prodComparison L (F.obj j) (G.obj j)) ≫ L.map (s.app j)
  naturality i j f := by
    dsimp only [towerProduct, Functor.comp_obj, Functor.comp_map]
    rw [← Category.assoc, ← prodComparison_inv_natural L (F.map f) (G.map f),
      Category.assoc, ← L.map_comp, s.naturality f, L.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_scalar_comparison
    (T : PurCompatibleFreeTowerData J)
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    [PreservesLimitsOfShape (Discrete WalkingPair) L] :
    T.ScalarComparison L := by
  let a := towerAction T.rings T.modules (towerScalar T)
  let a' := inv (prodComparison L (limit T.rings) (limit T.modules)) ≫ L.map a
  let s := transportedScalar T.rings T.modules (towerScalar T) L
  let c := towerAction (T.rings ⋙ L) (T.modules ⋙ L) s
  refine ⟨a, a', fun n ↦ s.app (op n), c, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact towerAction_π _ _ _ (op n)
  · dsimp only [a']
    simp only [IsIso.hom_inv_id_assoc]
  · intro n
    dsimp only [s, transportedScalar]
    simp only [IsIso.hom_inv_id_assoc]
    rfl
  · intro n
    exact towerAction_π _ _ _ (op n)
  · apply limit.hom_ext
    intro j
    dsimp only [a', c]
    simp only [Category.assoc, limit.post_π, towerAction_π]
    rw [← L.map_comp, towerAction_π]
    change inv (prodComparison L (limit T.rings) (limit T.modules)) ≫
      L.map (prod.map (limit.π T.rings j) (limit.π T.modules j) ≫
        (towerScalar T).app j) = _
    rw [L.map_comp, ← Category.assoc, prodComparison_inv_natural]
    dsimp only [s, transportedScalar]
    rw [Category.assoc, ← Category.assoc
      (prod.map (limit.post T.rings L) (limit.post T.modules L)), prod.map_map]
    simp only [limit.post_π]

set_option backward.isDefEq.respectTransparency.types false in
private theorem over_preserves_tower_limits (V : C) :
    PreservesLimitsOfShape ℕᵒᵖ (J.overPullback (Type (u + 1)) V) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (J.overPullback (Type (u + 1)) V ⋙
        sheafToPresheaf (J.over V) (Type (u + 1))) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf J (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_local_basis
    (T : PurCompatibleFreeTowerData J) (V : C)
    (b : ∀ n : ℕ, (SheafOfModules.unit (T.ring n)).over V ≅ (T.M n).over V)
    (hb : T.CompatibleBases V b) :
    ∃ B : (limit T.rings).over V ≅ (limit T.modules).over V,
      ∀ n : ℕ, B.hom ≫ (J.overPullback (Type (u + 1)) V).map
          (limit.π T.modules (op n)) =
        (J.overPullback (Type (u + 1)) V).map (limit.π T.rings (op n)) ≫
          (T.basisIso V n (b n)).hom := by
  let Q := J.overPullback (Type (u + 1)) V
  have : PreservesLimitsOfShape ℕᵒᵖ Q := over_preserves_tower_limits V
  let β : T.rings ⋙ Q ⟶ T.modules ⋙ Q :=
    NatTrans.ofOpSequence (fun n ↦ (T.basisIso V n (b n)).hom) (fun n ↦ (hb n).symm)
  have : ∀ j, IsIso (β.app j) := fun j ↦ inferInstanceAs
    (IsIso (T.basisIso V j.unop (b j.unop)).hom)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let B := preservesLimitIso Q T.rings ≪≫ HasLimit.isoOfNatIso (asIso β) ≪≫
    (preservesLimitIso Q T.modules).symm
  refine ⟨B, ?_⟩
  intro n
  change (preservesLimitIso Q T.rings).hom ≫
    (HasLimit.isoOfNatIso (asIso β)).hom ≫
      (preservesLimitIso Q T.modules).inv ≫ Q.map (limit.π T.modules (op n)) = _
  rw [preservesLimitIso_inv_π, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, preservesLimitIso_hom_π]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_continuous
    {D : Type u} [SmallCategory D] [HasFiniteLimits C]
    (J₀ : Precoverage C) (K₀ : Precoverage D) (hJ : J₀.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (hU : ∀ (X : C) (S : Presieve X), S ∈ J₀ X → S.map U ∈ K₀ (U.obj X)) :
    U.IsContinuous J₀.toGrothendieck K₀.toGrothendieck := by
  refine ⟨fun G ↦ ?_⟩
  rw [J₀.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  obtain ⟨I, V, a, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨P, p, q, hpb, hp⟩ := hJ.2.2 I X V a hR Y f
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hpb,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (Presieve.ofArrows P p).HasPairwisePullbacks :=
    J₀.hasPairwisePullbacks_of_mem hp
  let : U.PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun A B a b ha hb ↦ inferInstance⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks U G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    (hU _ _ hp)

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_isIso_of_cover
    {F G : Sheaf J (Type (u + 1))} (φ : F ⟶ G)
    {X : C} (hX : IsTerminal X) {I : Type (u + 1)} (V : I → C)
    (a : ∀ i, V i ⟶ X)
    (hc : Sieve.generate (Presieve.ofArrows V a) ∈ J X)
    (hφ : ∀ i, IsIso ((J.overPullback (Type (u + 1)) (V i)).map φ)) : IsIso φ := by
  have hb (i : I) (W : C) (q : W ⟶ V i) : Function.Bijective (φ.hom.app (op W)) := by
    have := hφ i
    have : IsIso (((J.overPullback (Type (u + 1)) (V i)).map φ).hom.app
      (op (Over.mk q))) := inferInstance
    exact (isIso_iff_bijective _).1 this
  apply (Sheaf.isLocallyBijective_iff_isIso φ).1
  constructor
  · constructor
    intro W x y h
    apply J.superset_covering _ (J.pullback_stable (hX.from W.unop) hc)
    intro Z f hf
    obtain ⟨Y, g, t, ⟨i⟩, he⟩ := hf
    apply (hb i Z g).injective
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  · constructor
    intro W y
    apply J.superset_covering _ (J.pullback_stable (hX.from W) hc)
    intro Z f hf
    obtain ⟨Y, g, t, ⟨i⟩, he⟩ := hf
    exact (hb i Z g).surjective (G.obj.map f.op y)

set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_local_comparison
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
    (T : PurCompatibleFreeTowerData J) (V : C)
    (b : ∀ n : ℕ, (SheafOfModules.unit (T.ring n)).over V ≅ (T.M n).over V)
    (hb : T.CompatibleBases V b) : T.LocalComparison K U V b := by
  let L := purTowerInverseImage (J := J) K U
  let Q := J.overPullback (Type (u + 1)) V
  let Q' := K.overPullback (Type (u + 1)) (U.obj V)
  have : PreservesLimitsOfShape ℕᵒᵖ Q' := over_preserves_tower_limits (U.obj V)
  obtain ⟨H, η, e, hη, he⟩ := unit_normalized_slice_inverse_image J K U V
  change Q ⋙ H ≅ L ⋙ Q' at e
  have en {F G : Sheaf J (Type (u + 1))} (f : F ⟶ G) :
      H.map (Q.map f) ≫ e.hom.app G = e.hom.app F ≫ Q'.map (L.map f) :=
    e.hom.naturality f
  have eni {F G : Sheaf J (Type (u + 1))} (f : F ⟶ G) :
      Q'.map (L.map f) ≫ e.inv.app G = e.inv.app F ≫ H.map (Q.map f) :=
    e.inv.naturality f
  let transport {F G : Sheaf J (Type (u + 1))} (b : F.over V ≅ G.over V) :
      (L.obj F).over (U.obj V) ≅ (L.obj G).over (U.obj V) :=
    (e.app F).symm ≪≫ H.mapIso b ≪≫ e.app G
  have ht {F G : Sheaf J (Type (u + 1))} (b : F.over V ≅ G.over V) :
      PurTowerLocalInverseImage K U V b (transport b) := by
    intro W q x
    have hn := ConcreteCategory.congr_hom (congrArg
      (fun f : (F.over V).obj ⟶ (Over.post U).op ⋙ (H.obj (G.over V)).obj ↦
        f.app (op (Over.mk q))) (hη b.hom)) x
    dsimp only [transport, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change (e.hom.app G).hom.app _
      ((H.map b.hom).hom.app _ ((e.inv.app F).hom.app (op (Over.mk (U.map q)))
        ((purTowerInverseImageUnit K U F).app (op W) x))) = _
    have heF := he F W q x
    change (e.hom.app F).hom.app (op (Over.mk (U.map q)))
      ((η (F.over V)).app (op (Over.mk q)) x) =
        (purTowerInverseImageUnit K U F).app (op W) x at heF
    rw [← heF]
    have hi' := ConcreteCategory.congr_hom (congrArg
      (fun f : H.obj (F.over V) ⟶ H.obj (F.over V) ↦
        f.hom.app (op (Over.mk (U.map q)))) (e.app F).hom_inv_id)
      ((η (F.over V)).app (op (Over.mk q)) x)
    dsimp at hi'
    have hc : (e.inv.app F).hom.app (op (Over.mk (U.map q)))
        ((e.hom.app F).hom.app (op (Over.mk (U.map q)))
          ((η (F.over V)).app (op (Over.mk q)) x)) =
          (η (F.over V)).app (op (Over.mk q)) x := hi'
    have hn' : (H.map b.hom).hom.app (op (Over.mk (U.map q)))
        ((η (F.over V)).app (op (Over.mk q)) x) =
      (η (G.over V)).app (op (Over.mk q))
        (b.hom.hom.app (op (Over.mk q)) x) := hn.symm
    exact (congrArg (fun z ↦ (e.hom.app G).hom.app (op (Over.mk (U.map q)))
      ((H.map b.hom).hom.app (op (Over.mk (U.map q))) z)) hc).trans
        ((congrArg (fun z ↦ (e.hom.app G).hom.app (op (Over.mk (U.map q))) z) hn').trans
          (he G W q (b.hom.hom.app (op (Over.mk q)) x)))
  obtain ⟨B, hB⟩ := tower_local_basis T V b hb
  let b' := fun n ↦ transport (T.basisIso V n (b n))
  let β : T.rings ⋙ Q ⟶ T.modules ⋙ Q :=
    NatTrans.ofOpSequence (fun n ↦ (T.basisIso V n (b n)).hom) (fun n ↦ (hb n).symm)
  let β' : (T.rings ⋙ L) ⋙ Q' ⟶ (T.modules ⋙ L) ⋙ Q' := {
    app j := (b' j.unop).hom
    naturality i j f := by
      change Q'.map (L.map (T.rings.map f)) ≫ _ = _ ≫ Q'.map (L.map (T.modules.map f))
      change Q'.map (L.map (T.rings.map f)) ≫ e.inv.app (T.rings.obj j) ≫
        H.map (β.app j) ≫ e.hom.app (T.modules.obj j) =
          (e.inv.app (T.rings.obj i) ≫ H.map (β.app i) ≫
            e.hom.app (T.modules.obj i)) ≫ Q'.map (L.map (T.modules.map f))
      rw [← Category.assoc, eni]
      simp only [Category.assoc]
      rw [← H.map_comp_assoc]
      have hn := β.naturality f
      change Q.map (T.rings.map f) ≫ _ = _ at hn
      rw [hn, H.map_comp]
      simp only [Category.assoc]
      simp only [Functor.comp_map]
      rw [en] }
  have : ∀ j, IsIso (β'.app j) := fun j ↦ inferInstanceAs (IsIso (b' j.unop).hom)
  have : IsIso β' := NatIso.isIso_of_isIso_app β'
  let B'' := preservesLimitIso Q' (T.rings ⋙ L) ≪≫
    HasLimit.isoOfNatIso (asIso β') ≪≫ (preservesLimitIso Q' (T.modules ⋙ L)).symm
  refine ⟨B, hB, transport B, ht B, b', fun n ↦ ht _, B'', ?_, ?_⟩
  · intro n
    change (preservesLimitIso Q' (T.rings ⋙ L)).hom ≫
      (HasLimit.isoOfNatIso (asIso β')).hom ≫
        (preservesLimitIso Q' (T.modules ⋙ L)).inv ≫
          Q'.map (limit.π (T.modules ⋙ L) (op n)) = _
    rw [preservesLimitIso_inv_π, HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc, preservesLimitIso_hom_π]
    rfl
  · apply (isLimitOfPreserves Q' (limit.isLimit (T.modules ⋙ L))).hom_ext
    intro j
    change (transport B).hom ≫ Q'.map (limit.post T.modules L) ≫
      Q'.map (limit.π (T.modules ⋙ L) j) =
        (Q'.map (limit.post T.rings L) ≫ B''.hom) ≫
          Q'.map (limit.π (T.modules ⋙ L) j)
    rw [← Q'.map_comp, limit.post_π]
    dsimp only [B'', Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, preservesLimitIso_inv_π,
      HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc]
    rw [← Q'.map_comp_assoc, limit.post_π]
    dsimp only [transport, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    erw [← en (limit.π T.modules j)]
    rw [← H.map_comp_assoc, hB j.unop, H.map_comp]
    simp only [Category.assoc]
    change e.inv.app (limit T.rings) ≫ H.map (Q.map (limit.π T.rings j)) ≫
      H.map (β.app j) ≫ e.hom.app (T.modules.obj j) =
        Q'.map (L.map (limit.π T.rings j)) ≫
          (e.inv.app (T.rings.obj j) ≫ H.map (β.app j) ≫ e.hom.app (T.modules.obj j))
    rw [← Category.assoc, ← eni]
    simp only [Category.assoc]


-- The site-axiom witness hK is retained in the original public signature.
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Inverse image of the inverse limit of a locally compatibly free module tower.

The scalar and local comparison predicates above expand all the stated equations.
The comparison itself is `limit.post`, without a cover or basis parameter. Its
uniqueness among maps with the same projections also gives independence of its inverse.

Source: the integral twist paragraph of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, localized by Stacks 03CF
(blueprint: lem-pur-inverse-image-compatible-free-tower).

Proof:
1. On each slice C/V_i the compatible linear bases give an isomorphism of towers.
   Sectionwise limits (def-pur-sheaf-inverse-limit) give B, linear for the
   coordinatewise action, and uniquely specified by its projections.
2. Cover and finite-limit preservation make U continuous and its Kan-extension
   inverse image left exact (lem-weil-pbc-left-exact-site-inverse-image-tensor).
   The unit-normalized slice comparison
   (lem-pur-unit-normalized-slice-inverse-image, Stacks 03CF) gives B' and the b'_n
   and their required unit equations.
3. Restriction to slices is sectionwise (def-pur-localized-ringed-site), hence
   commutes with inverse limits. Taking limits of b'_n gives B''. Projection
   squares identify the local module comparison with the local ring comparison.
   The latter is invertible by hκ. The same squares prove the scalar-action identity.
4. U carries the covering to a covering; pull it back over every object of D.
   The sheaf local-isomorphism criterion
   (lem-galois-set-sheaf-local-bijection-isomorphism) gives the global isomorphism.
5. Canonical projections commute with every compatible semilinear tower morphism,
   which gives naturality by joint monicity. They determine the comparison uniquely,
   independently of the covering and bases; uniqueness of inverses gives the same
   independence for the inverse.
-/
theorem pur_inverse_image_compatible_free_tower
    {D : Type u} [SmallCategory D] [HasFiniteLimits C] [HasFiniteLimits D]
    (J₀ : Precoverage C) (K₀ : Precoverage D)
    (hJ : J₀.IsSiteForCoverings) (hK : K₀.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (hUcover : ∀ (X : C) (S : Presieve X), S ∈ J₀ X → S.map U ∈ K₀ (U.obj X))
    (T : PurCompatibleFreeTowerData J₀.toGrothendieck)
    (hκ : IsIso (limit.post T.rings (purTowerInverseImage K₀.toGrothendieck U)))
    (I : Type (u + 1)) (V : I → C) (a : ∀ i : I, V i ⟶ ⊤_ C)
    (hcover : Presieve.ofArrows V a ∈ J₀ (⊤_ C))
    (b : ∀ (i : I) (n : ℕ),
      (SheafOfModules.unit (T.ring n)).over (V i) ≅ (T.M n).over (V i))
    (hb : ∀ i : I, T.CompatibleBases (V i) (b i)) :
    IsIso (limit.post T.modules (purTowerInverseImage K₀.toGrothendieck U)) ∧
      T.ScalarComparison (purTowerInverseImage K₀.toGrothendieck U) ∧
      (∀ i : I, T.LocalComparison K₀.toGrothendieck U (V i) (b i)) ∧
      T.NaturalComparison (purTowerInverseImage K₀.toGrothendieck U) ∧
      ∀ θ : (purTowerInverseImage K₀.toGrothendieck U).obj (limit T.modules) ⟶
          limit (T.modules ⋙ purTowerInverseImage K₀.toGrothendieck U),
        (∀ n : ℕ, θ ≫ limit.π (T.modules ⋙ purTowerInverseImage K₀.toGrothendieck U) (op n) =
          (purTowerInverseImage K₀.toGrothendieck U).map (limit.π T.modules (op n))) →
        θ = limit.post T.modules (purTowerInverseImage K₀.toGrothendieck U) := by
  have : U.IsContinuous J₀.toGrothendieck K₀.toGrothendieck :=
    tower_continuous J₀ K₀ hJ U hUcover
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : AB5OfSize.{u, u} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : PreservesFiniteLimits
      (purTowerInverseImage (J := J₀.toGrothendieck) K₀.toGrothendieck U) := by
    dsimp only [purTowerInverseImage]
    infer_instance
  refine ⟨?_, tower_scalar_comparison T _, ?_, tower_natural_comparison T _, ?_⟩
  · let L := purTowerInverseImage (J := J₀.toGrothendieck) K₀.toGrothendieck U
    have hi (i : I) : IsIso ((K₀.toGrothendieck.overPullback (Type (u + 1))
        (U.obj (V i))).map (limit.post T.modules L)) := by
      obtain ⟨B, hB, B', hB', b', hb', B'', hB'', hsq⟩ :=
        tower_local_comparison K₀.toGrothendieck U T (V i) (b i) (hb i)
      let Q := K₀.toGrothendieck.overPullback (Type (u + 1)) (U.obj (V i))
      have := hκ
      have : IsIso (Q.map (limit.post T.rings L)) := inferInstance
      have he : Q.map (limit.post T.modules L) =
          B'.inv ≫ Q.map (limit.post T.rings L) ≫ B''.hom := by
        rw [← hsq, Iso.inv_hom_id_assoc]
      rw [he]
      infer_instance
    apply tower_isIso_of_cover (limit.post T.modules L)
      (IsTerminal.isTerminalObj U (⊤_ C) terminalIsTerminal) (fun i ↦ U.obj (V i))
      (fun i ↦ U.map (a i)) _ hi
    have hc := hUcover (⊤_ C) (Presieve.ofArrows V a) hcover
    rw [Presieve.map_ofArrows] at hc
    exact Precoverage.Saturate.of _ _ hc
  · intro i
    exact tower_local_comparison _ U T (V i) (b i) (hb i)
  · intro θ hθ
    apply limit.hom_ext
    intro n
    exact (hθ n.unop).trans (limit.post_π _ _ n).symm

end CategoryTheory
