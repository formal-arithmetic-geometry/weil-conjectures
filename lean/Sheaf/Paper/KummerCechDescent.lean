/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-!
# Canonical coherent Kummer-nerve totalization

Source: direct-image proof paragraph (3), augmented Cech descent, and Stacks Tag 03OU
(blueprint: def-sfb-kummer-cech-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped Simplicial
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual coefficient module category on a scheme.
Source: direct-image proof paragraph (3), Cartesian coefficients
(blueprint: def-sfb-kummer-cech-descent). -/
abbrev KummerModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The unit-induced restriction between the sections over two schemes over W.
Both composition identifications are the published Cartesian coefficient identifications.
Source: direct-image proof paragraph (3), the actual covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSectionsMap {W : Scheme.{u}} {V T : Over W} (f : V ⟶ T) :
    upperStar Λ T.hom ⋙ lowerStar Λ T.hom ⟶
      upperStar Λ V.hom ⋙ lowerStar Λ V.hom :=
  Functor.whiskerLeft (upperStar Λ T.hom)
    (Functor.whiskerRight (upperStarLowerStarAdjunction Λ f.left).unit
      (lowerStar Λ T.hom)) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight
      ((upperStarComp Λ f.left T.hom).symm ≪≫ upperStarCongr Λ f.w)
      (lowerStar Λ f.left ⋙ lowerStar Λ T.hom)).hom ≫
    (Functor.isoWhiskerLeft (upperStar Λ V.hom)
      (lowerStarComp Λ f.left T.hom ≪≫ lowerStarCongr Λ f.w)).hom

/-- Restriction of sections is contravariantly functorial on schemes over W.
Source: direct-image proof paragraph (3), augmented nerve
(blueprint: def-sfb-kummer-cech-descent).

Proof: for the identity use the identity upper/lower-star comparisons and the
identity adjunction. For a composite, the composite adjunction unit is the first
unit followed by the push-pull of the second. Apply the published composition
coherence of upper and lower stars. The two composites are equal by the unit
composition equation, with the same coefficient identifications throughout. -/
theorem overSectionsMap_laws (W : Scheme.{u}) :
    (∀ V : Over W, overSectionsMap Λ (𝟙 V) = 𝟙 _) ∧
    (∀ {V T U : Over W} (f : V ⟶ T) (g : T ⟶ U),
      overSectionsMap Λ (f ≫ g) = overSectionsMap Λ g ≫ overSectionsMap Λ f) := by
  sorry

/-- Sections over schemes over W, using the actual inverse/direct image adjunctions.
Source: direct-image proof paragraph (3), augmented nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSections (W : Scheme.{u}) :
    (Over W)ᵒᵖ ⥤ (KummerModules Λ W ⥤ KummerModules Λ W) where
  obj V := upperStar Λ V.unop.hom ⋙ lowerStar Λ V.unop.hom
  map f := overSectionsMap Λ f.unop
  map_id V := (overSectionsMap_laws Λ W).1 V.unop
  map_comp f g := (overSectionsMap_laws Λ W).2 g.unop f.unop

/-- The actual augmented Cech nerve, regarded as schemes over the open W.
Source: direct-image proof paragraph (3), punctured Kummer cover
(blueprint: def-sfb-kummer-cech-descent). -/
def cechOver {T W : Scheme.{u}} (v : T ⟶ W) : SimplicialObject (Over W) where
  obj n := Over.mk ((Arrow.mk v).augmentedCechNerve.hom.app n)
  map f := Over.homMk ((Arrow.mk v).cechNerve.map f)
    ((Arrow.mk v).augmentedCechNerve.hom.naturality f)
  map_id n := by ext; exact (Arrow.mk v).cechNerve.map_id n
  map_comp f g := by ext; exact (Arrow.mk v).cechNerve.map_comp f g

/-- The actual augmentation projection in nerve degree n.
Source: direct-image proof paragraph (3), the actual punctured covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def cechProjection {T W : Scheme.{u}} (v : T ⟶ W) (n : SimplexCategory) :
    (Arrow.mk v).cechNerve.obj (op n) ⟶ W :=
  WidePullback.base (fun _ : Fin (n.len + 1) ↦ v)


/-- One term of the actual Cech image, written without nested functor flips.
Source: direct-image proof paragraph (3), compatible resolutions
(blueprint: def-sfb-kummer-cech-descent). -/
def cechImageTerm {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (L : KummerModules Λ W) (n : SimplexCategory) : KummerModules Λ S :=
  (upperStar Λ s).obj ((lowerStar Λ a).obj
    ((lowerStar Λ ((cechOver v).obj (op n)).hom).obj
      ((upperStar Λ ((cechOver v).obj (op n)).hom).obj L)))

/-- The coherent cosimplicial module functor is formed before localization.
Source: direct-image proof paragraph (3), normalized Cech descent
(blueprint: def-sfb-kummer-cech-descent). -/
def cechImage {T W Y S : Scheme.{u}} (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    KummerModules Λ W ⥤ (SimplexCategory ⥤ KummerModules Λ S) :=
  (((cechOver v).rightOp ⋙ overSections Λ W) ⋙
    (Functor.whiskeringRight _ _ _).obj (lowerStar Λ a ⋙ upperStar Λ s)).flip

/-- The Cech image functor is additive.
Source: direct-image proof paragraph (3), compatible first-quadrant resolutions
(blueprint: def-sfb-kummer-cech-descent).

Proof: evaluate at every simplex. Its functor is a composite of the additive
Cartesian pullbacks and direct images. Addition of natural transformations is
componentwise, so these componentwise equalities prove additivity. -/
theorem cechImage_additive {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W) :
    (cechImage Λ a s v).Additive := by
  sorry
attribute [instance] cechImage_additive

/-- Resolve the actual coherent Cech diagram, with its type fixed once.
Source: direct-image proof (3), compatible resolutions
(blueprint: def-sfb-kummer-cech-descent). -/
def kummerCechResolution {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) :
    CochainComplex (SimplexCategory ⥤ KummerModules Λ S) ℕ :=
  ((cechImage Λ a s v).mapHomologicalComplex (.up ℕ)).obj I

/-- Cosimplicial module diagrams have their canonical Grothendieck structure.
Source: modules on sites and small functor categories, Tag 03DA
(blueprint: def-sfb-kummer-cech-descent).

Proof: kernels, cokernels and filtered colimits are computed componentwise.
Filtered colimits are exact. A generator is the sum over simplices of the left
Kan extensions of a generator in the module category along each object inclusion.
Smallness of the simplex category and existence of these sums give a generator. -/
theorem cosimplicialGrothendieck (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} ((SimplexCategory ⥤ KummerModules Λ S)) := by
  sorry
attribute [instance] cosimplicialGrothendieck

/-- Derived totalization means the ordinary right-derived limit of the coherent
cosimplicial module diagram. On bounded-below objects it is the compatible
first-quadrant total, with the usual alternating-face sign convention.
Source: direct-image proof paragraph (3), coherent derived totalization
(blueprint: def-sfb-kummer-cech-descent). -/
def cechTotal (S : Scheme.{u}) :
    DerivedCategory (SimplexCategory ⥤ KummerModules Λ S) ⥤
      DerivedCategory (KummerModules Λ S) := by
  let L := (lim : (SimplexCategory ⥤ KummerModules Λ S) ⥤ KummerModules Λ S)
  haveI : L.Additive := Functor.additive_of_preserves_binary_products L
  exact L.rightDerivedFunctor



/-- The actual adjunction unit, with the section functor kept opaque to elaboration.
Source: direct-image proof paragraph (3), augmented covering nerve
(blueprint: def-sfb-kummer-cech-descent). -/
def overSectionUnit {W : Scheme.{u}} (V : Over W) :
    𝟭 (KummerModules Λ W) ⟶ (overSections Λ W).obj (op V) :=
  (upperStarLowerStarAdjunction Λ V.hom).unit


/-- Restrict sections by the actual unit in every nerve term.
Source: direct-image proof (3), augmented descent
(blueprint: def-sfb-kummer-cech-descent). -/
def cechAugmentationComponent {T W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y) (v : T ⟶ W)
    (L : KummerModules Λ W) (n : SimplexCategory) :
    (upperStar Λ s).obj ((lowerStar Λ a).obj L) ⟶ cechImageTerm Λ a s v L n :=
  (upperStar Λ s).map ((lowerStar Λ a).map
    ((upperStarLowerStarAdjunction Λ ((cechOver v).obj (op n)).hom).unit.app L))

end AlgebraicGeometry.ProEtale.CondensedRing
