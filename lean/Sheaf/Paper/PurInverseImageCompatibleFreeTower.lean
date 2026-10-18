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
import Sheaf.Paper.SliceSiteLocalization
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
   The slice comparison (lem-weil-pbc-slice-site-localization, Stacks 03CF)
   gives B' and the b'_n; its adjunction compatibility gives the unit equations.
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
  sorry

end CategoryTheory
