/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Elements
import Sheaf.CategoryTheory.SitePointFibre
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-! # Affine neighbourhoods of an oriented geometric point

Source: Illusie, Around the Thom--Sebastiani theorem, §1.3, before (1.3.1), printed p. 7;
ILO Exposé XI §§1.1, 1.6, 1.8 (blueprint: lem-trf-oriented-affine-neighbourhood-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The actual etale triple category, with its original homomorphism universe.
Source: ILO XI §1.1(i) (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
abbrev OrientedEtaleTriples {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  OrientedProduct.largeTriples f.Etale g.Etale

/-- The three prescribed generating covering types on the etale triple category.
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedEtaleTopology {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  OrientedProduct.largeTopology X.smallEtalePretopology Y.smallEtalePretopology f.Etale g.Etale

/-- Sheafified representables, viewed in the containing universe of sets: the oriented-product
dependency's `largeAssociated` on the etale triple site.
Source: ILO XI §§1.2, 1.6 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedEtaleAssociated {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    OrientedEtaleTriples f g ⥤ Sheaf (orientedEtaleTopology f g) (Type (u + 1)) :=
  OrientedProduct.largeAssociated (orientedEtaleTopology f g)

/-- The canonical projection from a strict localization to a pointed etale neighbourhood.
Source: Stacks 04HX (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedStrictLeg {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (n : PointedEtaleNeighborhood s) :
    strictLocalization s ⟶ n.1.left :=
  eqToHom (by rfl) ≫ (strictLocalizationConeAll s).π.app n

/-- The canonical cone to base-change neighbourhoods followed by their first projection.
Source: strict-local functoriality, Stacks 04HX
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedStrictMapCone {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Cone (neighborhoodDiagram (x ≫ f)) where
  pt := strictLocalization x
  π :=
    { app := fun n ↦ orientedStrictLeg x
        ((pointSmallEtaleElementsBaseChange f x).obj n) ≫ pullback.fst n.1.hom f
      naturality := by
        intro n n' h
        have hh := (strictLocalizationConeAll x).w
          ((pointSmallEtaleElementsBaseChange f x).map h)
        change orientedStrictLeg x ((pointSmallEtaleElementsBaseChange f x).obj n') ≫
            pullback.fst n'.1.hom f =
          (orientedStrictLeg x ((pointSmallEtaleElementsBaseChange f x).obj n) ≫
            pullback.fst n.1.hom f) ≫ h.1.left
        have hm : (neighborhoodDiagram x).map
            ((pointSmallEtaleElementsBaseChange f x).map h) ≫
              pullback.fst n'.1.hom f = pullback.fst n.1.hom f ≫ h.1.left :=
          Hom.etale_map_left_comp_fst f h.1
        dsimp only [orientedStrictLeg]
        simp only [eqToHom_refl, Category.id_comp]
        rw [← hh, Category.assoc, hm, Category.assoc] }

/-- The canonical map of strict localizations induced by a scheme morphism.
Source: Stacks 04HX, universal property of strict-local neighbourhood limits
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedStrictMap {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    strictLocalization x ⟶ strictLocalization (x ≫ f) :=
  (isLimitStrictLocalizationConeAll (x ≫ f)).lift (orientedStrictMapCone f x) ≫
    eqToHom (by rfl)

/-- The cone of the chosen geometric lifts over all pointed neighbourhoods.
Source: Stacks 04HX (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedStrictPointCone {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cone (neighborhoodDiagram s) where
  pt := Spec (.of Ω)
  π :=
    { app := fun n ↦ n.2.left
      naturality := by
        intro n n' h
        have hh := congrArg Over.Hom.left h.2
        change n'.2.left = n.2.left ≫ h.1.left
        exact hh.symm }

/-- The canonical geometric point of its strict localization, by its limit universal property.
Source: Stacks 04HX (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedStrictPoint {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Spec (.of Ω) ⟶ strictLocalization s :=
  (isLimitStrictLocalizationConeAll s).lift (orientedStrictPointCone s)

/-- The first structural map of a triple, as an ordinary map to its middle scheme.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedTripleLeft {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : OrientedEtaleTriples f g) : T.left.1.left ⟶ T.right.left :=
  T.hom.1.left ≫ pullback.fst T.right.hom f

/-- The second structural map of a triple.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedTripleRight {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : OrientedEtaleTriples f g) : T.left.2.left ⟶ T.right.left :=
  T.hom.2.left ≫ pullback.fst T.right.hom g

/-- The middle geometric lift determined by the left geometric lift.
Source: ILO XI §1.6 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedMiddleLift {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (T : OrientedEtaleTriples f g) (a : (pointSmallEtale x).fiber.obj T.left.1) :
    (pointSmallEtale (x ≫ f)).fiber.obj T.right :=
  Over.homMk (a.left ≫ orientedTripleLeft T) (by
    have ha : a.left ≫ T.left.1.hom = x := Over.w a
    have ht : T.hom.1.left ≫ pullback.snd T.right.hom f = T.left.1.hom :=
      MorphismProperty.Over.w T.hom.1
    change (a.left ≫ (T.hom.1.left ≫ pullback.fst T.right.hom f)) ≫ T.right.hom = _
    calc
      (a.left ≫ (T.hom.1.left ≫ pullback.fst T.right.hom f)) ≫ T.right.hom =
          a.left ≫ (T.hom.1.left ≫ pullback.snd T.right.hom f) ≫ f := by
            simp only [Category.assoc, pullback.condition]
      _ = x ≫ f := by rw [ht, ← Category.assoc, ha])

/-- Compatible pairs of lifts, with the actual specialization equation through `c`.
The middle lift is determined by the first lift and the triple structure map.
Source: ILO XI §1.6 formula (1.a), §1.8; Illusie §1.3
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def OrientedCompatibleLifts {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
    (c : strictLocalization (y ≫ g) ⟶ strictLocalization (x ≫ f))
    (T : OrientedEtaleTriples f g) :=
  {a : (pointSmallEtale x).fiber.obj T.left.1 ×
      (pointSmallEtale y).fiber.obj T.left.2 //
    a.2.left ≫ orientedTripleRight T = orientedStrictPoint (y ≫ g) ≫ c ≫
      orientedStrictLeg (x ≫ f) ⟨T.right, orientedMiddleLift x T a.1⟩}

/-- The inverse-image sections `L_z(T)` of the associated representable.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedEtaleSections {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (z : GeometricMorphism (Type (u + 1))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1)))) :
    OrientedEtaleTriples f g ⥤ Type (u + 1) := orientedEtaleAssociated f g ⋙ z.inverse

/-- That `z` corresponds to `(x,y,c)`, in the natural inverse-image formula for triples.
Only the enlargement of the lift sets to the containing universe uses `ULift`.
Source: ILO XI §§1.6, 1.8 (blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
structure OrientedPointCorrespondence {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
    (c : strictLocalization (y ≫ g) ⟶ strictLocalization (x ≫ f))
    (z : GeometricMorphism (Type (u + 1))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1)))) where
  equiv : ∀ T, (orientedEtaleSections z).obj T ≃ ULift.{u + 1} (OrientedCompatibleLifts x y c T)
  natural_left : ∀ {T T'} (h : T ⟶ T') (a : (orientedEtaleSections z).obj T),
    ((equiv T' ((orientedEtaleSections z).map h a)).down.val.1).left =
      ((equiv T a).down.val.1).left ≫ h.left.1.left
  natural_right : ∀ {T T'} (h : T ⟶ T') (a : (orientedEtaleSections z).obj T),
    ((equiv T' ((orientedEtaleSections z).map h a)).down.val.2).left =
      ((equiv T a).down.val.2).left ≫ h.left.2.left

/-- The fibre-product scheme diagram, on the actual triple category and its actual arrows.
Source: Illusie §1.3 before (1.3.1)
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedFibreProductDiagram {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    OrientedEtaleTriples f g ⥤ Scheme.{u} where
  obj T := pullback (orientedTripleLeft T) (orientedTripleRight T)
  map {T T'} h := pullback.map _ _ _ _ h.left.1.left h.left.2.left h.right.left
    (by
      have hh := congrArg (fun a ↦ a.1.left) h.w
      change h.left.1.left ≫ T'.hom.1.left = T.hom.1.left ≫ (f.Etale.map h.right).left at hh
      dsimp only [orientedTripleLeft]
      rw [Category.assoc, ← Hom.etale_map_left_comp_fst f h.right,
        ← Category.assoc, ← hh, Category.assoc])
    (by
      have hh := congrArg (fun a ↦ a.2.left) h.w
      change h.left.2.left ≫ T'.hom.2.left = T.hom.2.left ≫ (g.Etale.map h.right).left at hh
      dsimp only [orientedTripleRight]
      rw [Category.assoc, ← Hom.etale_map_left_comp_fst g h.right,
        ← Category.assoc, ← hh, Category.assoc])
  map_id T := by
    apply pullback.hom_ext <;>
      simp only [Comma.id_left, prod_id_fst, prod_id_snd, Comma.id_right, limit.lift_π,
        PullbackCone.mk_π_app, Category.id_comp]
    all_goals change _ ≫ 𝟙 _ = _
    all_goals simp
  map_comp h k := by
    apply pullback.hom_ext <;>
      simp only [Comma.comp_left, prod_comp, Comma.comp_right, limit.lift_π,
        PullbackCone.mk_π_app, Category.assoc, limit.lift_π_assoc, cospan_left, cospan_right]
    all_goals change _ ≫ (_ ≫ _) = _ ≫ _ ≫ _
    all_goals rfl

/-- Pointed triples with all three coordinates affine; this is a full subcategory of `L_z`'s
category of elements. Source: Illusie §1.3 before (1.3.1)
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedAffineProperty {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (z : GeometricMorphism (Type (u + 1))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1)))) :
    ObjectProperty (orientedEtaleSections z).Elements :=
  fun n ↦ IsAffine n.1.left.1.left ∧ IsAffine n.1.right.left ∧ IsAffine n.1.left.2.left

/-- Forget the chosen section and restrict the fibre-product diagram to affine triples.
Source: Illusie §1.3 before (1.3.1)
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedAffineDiagram {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (z : GeometricMorphism (Type (u + 1))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1)))) :
    (orientedAffineProperty z).FullSubcategory ⥤ Scheme.{u} :=
  (orientedAffineProperty z).ι ⋙ CategoryOfElements.π _ ⋙ orientedFibreProductDiagram f g

/-- The canonical map of the strict-local fibre product to the ordinary fibre product.
Source: Illusie §1.3 before (1.3.1)
(blueprint: lem-trf-oriented-affine-neighbourhood-limit). -/
def orientedMilnorTube {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
    (c : strictLocalization (y ≫ g) ⟶ strictLocalization (x ≫ f)) : Scheme.{u} :=
  pullback (orientedStrictMap f x) (orientedStrictMap g y ≫ c)

/-- Affine pointed triples are initial and cofiltered, with a small skeleton. Their
fibre-product diagram consists of affine schemes etale over `X ×_S Y`, with affine transition
maps, and its limit is the strict-local fibre product with its prescribed projections.

Source: Illusie, Around the Thom--Sebastiani theorem, §1.3 before (1.3.1), printed p. 7;
ILO XI §§1.1, 1.6, 1.8 (blueprint: lem-trf-oriented-affine-neighbourhood-limit).

Proof plan, following all ten steps of the DAG node:
1. Use the oriented-product inverse-image formula and the representable-stalk lemma to
identify sections with the compatible geometric lifts specified in `e`.
2. Finite limits of triples are componentwise. The site-point fibre lemma makes all pointed
triples cofiltered; work in the containing size universe.
3. First shrink the middle coordinate affinely around its chosen lift. Naturality of the
specialization retains the right lift; then shrink the two outside coordinates affinely.
4. The affine subcategory is full and every pointed triple has an affine refinement. The
full-subcategory initiality criterion gives initiality and cofilteredness, and the size
convention gives a small skeleton.
5. Fibre products of affine schemes over affine schemes are affine. Morphisms between them
are affine. Base change and cancellation of etale morphisms make the canonical maps etale.
6. Each projected affine pointed neighbourhood has a triple refinement: use the prototypes
(U,S,Y), (X,S,W), and (X ×_S V,V,Y ×_S V), then affinely refine.
7. Equalize parallel pointed maps in each coordinate and affinely refine the resulting
triple; in the middle coordinate base change both outside coordinates by the equalizer.
8. The cofiltered initiality criterion makes the three coordinate functors initial. Thus
their limits are the three strict localizations, with their canonical neighbourhood maps.
9. The two maps into the middle limit are `orientedStrictMap f x` and the composite
`orientedStrictMap g y ≫ c`, as checked on every pointed base neighbourhood.
10. The pullback universal property gives the cone below and makes it limiting. The two
projection equations identify every cone leg and its map over `X ×_S Y`. Nothing in this
argument asserts that a stage or the limiting fibre product is nonempty.
-/
theorem orientedAffineNeighbourhoodLimit
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
    (c : strictLocalization (y ≫ g) ⟶ strictLocalization (x ≫ f))
    (hc : c ≫ strictLocalizationToBase (x ≫ f) = strictLocalizationToBase (y ≫ g))
    (z : GeometricMorphism (Type (u + 1))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1))))
    (e : OrientedPointCorrespondence x y c z) :
    (orientedAffineProperty z).ι.Initial ∧
    IsCofiltered (orientedAffineProperty z).FullSubcategory ∧
    EssentiallySmall.{u + 1} (orientedAffineProperty z).FullSubcategory ∧
    (∀ n : (orientedAffineProperty z).FullSubcategory,
      IsAffine ((orientedAffineDiagram z).obj n)) ∧
    (∀ {n n' : (orientedAffineProperty z).FullSubcategory} (h : n ⟶ n'),
      IsAffineHom ((orientedAffineDiagram z).map h)) ∧
    ∃ (q : orientedAffineDiagram z ⟶
        (Functor.const (orientedAffineProperty z).FullSubcategory).obj (pullback f g)),
      (∀ n, Etale (q.app n)) ∧
      (∀ n, q.app n ≫ pullback.fst f g =
        pullback.fst (orientedTripleLeft n.obj.1) (orientedTripleRight n.obj.1) ≫
          n.obj.1.left.1.hom) ∧
      (∀ n, q.app n ≫ pullback.snd f g =
        pullback.snd (orientedTripleLeft n.obj.1) (orientedTripleRight n.obj.1) ≫
          n.obj.1.left.2.hom) ∧
      ∃ (l : Cone (orientedAffineDiagram z))
        (i : l.pt ≅ orientedMilnorTube f g x y c),
        Nonempty (IsLimit l) ∧
        (∀ n, l.π.app n ≫
            pullback.fst (orientedTripleLeft n.obj.1) (orientedTripleRight n.obj.1) =
          i.hom ≫ pullback.fst (orientedStrictMap f x) (orientedStrictMap g y ≫ c) ≫
            orientedStrictLeg x ⟨n.obj.1.left.1, (e.equiv n.obj.1 n.obj.2).down.val.1⟩) ∧
        (∀ n, l.π.app n ≫
            pullback.snd (orientedTripleLeft n.obj.1) (orientedTripleRight n.obj.1) =
          i.hom ≫ pullback.snd (orientedStrictMap f x) (orientedStrictMap g y ≫ c) ≫
            orientedStrictLeg y ⟨n.obj.1.left.2, (e.equiv n.obj.1 n.obj.2).down.val.2⟩) ∧
        (∀ n, l.π.app n ≫ q.app n ≫ pullback.fst f g =
          i.hom ≫ pullback.fst (orientedStrictMap f x) (orientedStrictMap g y ≫ c) ≫
            strictLocalizationToBase x) ∧
        (∀ n, l.π.app n ≫ q.app n ≫ pullback.snd f g =
          i.hom ≫ pullback.snd (orientedStrictMap f x) (orientedStrictMap g y ≫ c) ≫
            strictLocalizationToBase y) := by
  sorry

end AlgebraicGeometry.Scheme
