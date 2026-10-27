module

public import Sheaf.AlgebraicGeometry.FlatSpaceDerivedExternalCupMaps
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange
public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Derived external cup products for flat algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 08IN, 08IR and 071Q;
sites-cohomology.tex, Tags 0FPL, 0FPM and 0H9A.
(blueprint: lem-sfb-flat-space-derived-external-cup).

## Main definitions
- `sections`, `mul`, `unit`, `rho`, `external`, `baseChange`: the actual canonical maps.
- `AlgebraLaws`, `ExternalCoherence`, `BaseChangeLaws`: their algebra and comparison equations.
- `ZariskiComparison`: comparison with the ordinary Zariski ringed-site cup.

## Main statements
- `flat_space_derived_external_cup`: all clauses for flat qcqs spaces over an affine base.

The witness records below specify canonical maps by their section and derived-unit
normalizations. No choice from the existence of an unnormalized map is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry.AlgebraicSpace
namespace FlatExternalCup

variable {S : Scheme.{u}}
  [∀ X : AlgebraicSpace S, HasDerivedCategory.{u} X.SmallModules]

/-- The algebra, pullback and Kunneth clauses, written as equalities of derived morphisms.
The final scalar and topology clauses are recorded separately below.
Source: Stacks 08IN, 08IR, 0FPL, 0FPM and 0FPN
(blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure AlgebraLaws (c : Comparisons (S := S)) (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) where
  associative : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y), admissible f →
    (mul A Y e X f ▷ sections A Y e X f) ≫ mul A Y e X f =
      (α_ _ _ _).hom ≫ (sections A Y e X f ◁ mul A Y e X f) ≫ mul A Y e X f
  left_unit : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y), admissible f →
    (unit A Y e X f ▷ sections A Y e X f) ≫ mul A Y e X f = (λ_ _).hom
  right_unit : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y), admissible f →
    (sections A Y e X f ◁ unit A Y e X f) ≫ mul A Y e X f = (ρ_ _).hom
  commutative : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y), admissible f →
    (symmetry A _ _).hom ≫ mul A Y e X f = mul A Y e X f
  pull_mul : ∀ {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y) (sq : h ≫ f = f'),
    admissible f → admissible f' →
    mul A Y e X f ≫ rho c A Y e f h f' sq =
      (rho c A Y e f h f' sq ⊗ₘ rho c A Y e f h f' sq) ≫ mul A Y e X' f'
  pull_unit : ∀ {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y) (sq : h ≫ f = f'),
    admissible f → admissible f' →
    unit A Y e X f ≫ rho c A Y e f h f' sq = unit A Y e X' f'
  pull_id : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (sq : (𝟙 X) ≫ f = f), admissible f → rho c A Y e f (𝟙 X) f sq = 𝟙 _
  pull_comp : ∀ {X X' X'' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y) (f'' : X'' ⟶ schemeSpace Y)
    (h : X' ⟶ X) (h' : X'' ⟶ X') (sq : h ≫ f = f') (sq' : h' ≫ f' = f'')
    (sq'' : (h' ≫ h) ≫ f = f''),
    admissible f → admissible f' → admissible f'' →
    rho c A Y e f h f' sq ≫ rho c A Y e f' h' f'' sq' =
      rho c A Y e f (h' ≫ h) f'' sq''
  kunneth : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k),
    admissible f → admissible g → IsPullback p.hom q.hom f.hom g.hom →
      IsIso (external c A Y e f g k p q hp hq)
  external_mul : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k),
    admissible f → admissible g → IsPullback p.hom q.hom f.hom g.hom →
    (external c A Y e f g k p q hp hq ⊗ₘ external c A Y e f g k p q hp hq) ≫
        mul A Y e W k =
      @MonoidalCategory.tensorμ _ _ _
        (DerivedCategory.symmetricCategory (ModuleCat.{u} A)).toBraidedCategory
        (sections A Y e X f) (sections A Y e Z g)
        (sections A Y e X f) (sections A Y e Z g) ≫
      (mul A Y e X f ⊗ₘ mul A Y e Z g) ≫ external c A Y e f g k p q hp hq
  external_unit : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k),
    admissible f → admissible g → IsPullback p.hom q.hom f.hom g.hom →
    (λ_ (𝟙_ (DerivedCategory (ModuleCat.{u} A)))).inv ≫
        (unit A Y e X f ⊗ₘ unit A Y e Z g) ≫ external c A Y e f g k p q hp hq =
      unit A Y e W k
  affine_unit : IsIso (unit A Y e (schemeSpace Y) (𝟙 _))
  first_projection : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k), admissible f → admissible g →
    IsPullback p.hom q.hom f.hom g.hom →
    (ρ_ _).inv ≫ (sections A Y e X f ◁ unit A Y e Z g) ≫
      external c A Y e f g k p q hp hq = rho c A Y e f p k hp
  second_projection : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k), admissible f → admissible g →
    IsPullback p.hom q.hom f.hom g.hom →
    (λ_ _).inv ≫ (unit A Y e X f ▷ sections A Y e Z g) ≫
      external c A Y e f g k p q hp hq = rho c A Y e g q k hq

/-- Naturality, permutation, reassociation and affine-unit coherence for external cup.
These are equations for the actual iterated projection pullbacks.
Source: Stacks 0FPL, 0FPM, 0FPN (blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure ExternalCoherence (c : Comparisons (S := S)) (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) where
  naturality : ∀ {X Z W X' Z' W' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y) (g' : Z' ⟶ schemeSpace Y) (k' : W' ⟶ schemeSpace Y)
    (p : W ⟶ X) (q : W ⟶ Z) (p' : W' ⟶ X') (q' : W' ⟶ Z')
    (a : X' ⟶ X) (b : Z' ⟶ Z) (d : W' ⟶ W)
    (hp : p ≫ f = k) (hq : q ≫ g = k) (hp' : p' ≫ f' = k') (hq' : q' ≫ g' = k')
    (ha : a ≫ f = f') (hb : b ≫ g = g') (hd : d ≫ k = k'),
    admissible f → admissible g → admissible f' → admissible g' →
    IsPullback p.hom q.hom f.hom g.hom →
    IsPullback p'.hom q'.hom f'.hom g'.hom →
    d ≫ p = p' ≫ a → d ≫ q = q' ≫ b →
    external c A Y e f g k p q hp hq ≫ rho c A Y e k d k' hd =
      (rho c A Y e f a f' ha ⊗ₘ rho c A Y e g b g' hb) ≫
        external c A Y e f' g' k' p' q' hp' hq'
  permutation : ∀ {X Z W : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y) (p : W ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ f = k) (hq : q ≫ g = k),
    admissible f → admissible g → IsPullback p.hom q.hom f.hom g.hom →
    (symmetry A _ _).hom ≫ external c A Y e g f k q p hq hp =
      external c A Y e f g k p q hp hq
  associativity : ∀ {X Z V P Q W : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (g : Z ⟶ schemeSpace Y) (h : V ⟶ schemeSpace Y)
    (j : P ⟶ schemeSpace Y) (l : Q ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y)
    (p : P ⟶ X) (q : P ⟶ Z) (r : Q ⟶ Z) (s : Q ⟶ V)
    (a : W ⟶ P) (b : W ⟶ V) (d : W ⟶ X) (v : W ⟶ Q)
    (hp : p ≫ f = j) (hq : q ≫ g = j) (hr : r ≫ g = l) (hs : s ≫ h = l)
    (ha : a ≫ j = k) (hb : b ≫ h = k) (hd : d ≫ f = k) (hv : v ≫ l = k),
    admissible f → admissible g → admissible h →
    IsPullback p.hom q.hom f.hom g.hom → IsPullback r.hom s.hom g.hom h.hom →
    IsPullback a.hom b.hom j.hom h.hom → IsPullback d.hom v.hom f.hom l.hom →
    a ≫ p = d → a ≫ q = v ≫ r → b = v ≫ s →
    (external c A Y e f g j p q hp hq ▷ sections A Y e V h) ≫
        external c A Y e j h k a b ha hb =
      (α_ _ _ _).hom ≫ (sections A Y e X f ◁ external c A Y e g h l r s hr hs) ≫
        external c A Y e f l k d v hd hv
  right_unit : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (hi : (𝟙 X) ≫ f = f) (hf : f ≫ (𝟙 _) = f), admissible f →
    (sections A Y e X f ◁ unit A Y e (schemeSpace Y) (𝟙 _)) ≫
      external c A Y e f (𝟙 _) f (𝟙 X) f hi hf = (ρ_ _).hom
  left_unit : ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (hi : (𝟙 X) ≫ f = f) (hf : f ≫ (𝟙 _) = f), admissible f →
    (unit A Y e (schemeSpace Y) (𝟙 _) ▷ sections A Y e X f) ≫
      external c A Y e (𝟙 _) f f f (𝟙 X) hf hi = (λ_ _).hom

/-- Base change preserves the canonical cup product and unit, using the normalized
scalar tensor. All maps are defined even before their invertibility is asserted.
Source: Stacks 08IR, 0H9A (blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure BaseChangeLaws (c : Comparisons (S := S))
    {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B)) (g : Y' ⟶ Y)
    (t : ScalarTensor (spaceAffineRingMap e e' g)) where
  invertible : ∀ {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)),
    admissible f → IsPullback h.hom f'.hom f.hom
      ((Scheme.fppfTopology.over S).yoneda.map g) →
    IsIso (baseChange c e e' g f h f' sq)
  multiplication : ∀ {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)),
    admissible f → IsPullback h.hom f'.hom f.hom
      ((Scheme.fppfTopology.over S).yoneda.map g) →
    (t.tensor (sections A Y e X f) (sections A Y e X f)).hom ≫
      (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).map
        (mul A Y e X f) ≫ baseChange c e e' g f h f' sq =
      (baseChange c e e' g f h f' sq ⊗ₘ baseChange c e e' g f h f' sq) ≫ mul B Y' e' X' f'
  unit : ∀ {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)),
    admissible f → IsPullback h.hom f'.hom f.hom
      ((Scheme.fppfTopology.over S).yoneda.map g) →
    t.unit.hom ≫
      (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).map
        (FlatExternalCup.unit A Y e X f) ≫ baseChange c e e' g f h f' sq =
      FlatExternalCup.unit B Y' e' X' f'

/-- Base-change naturality for arbitrary morphisms of the two cartesian squares.
The equation is in D(B), so it retains the actual extension-of-scalars functor.
Source: Stacks 0H9A (blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure BaseChangeNaturality (c : Comparisons (S := S))
    {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B)) (g : Y' ⟶ Y)
    (t : ScalarTensor (spaceAffineRingMap e e' g)) where
  pullback : ∀ {X Z X' Z' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (l : Z ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y') (l' : Z' ⟶ schemeSpace Y')
    (h : X' ⟶ X) (j : Z' ⟶ Z) (a : Z ⟶ X) (a' : Z' ⟶ X')
    (sq : h ≫ f = f' ≫ schemeMap g)
    (sq' : j ≫ l = l' ≫ schemeMap g)
    (ha : a ≫ f = l) (ha' : a' ≫ f' = l'),
    admissible f → admissible l → j ≫ a = a' ≫ h →
    IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    IsPullback j.hom l'.hom l.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).map
        (rho c A Y e f a l ha) ≫ baseChange c e e' g l j l' sq' =
      baseChange c e e' g f h f' sq ≫ rho c B Y' e' f' a' l' ha'
  external : ∀ {X Z W X' Z' W' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (l : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y') (l' : Z' ⟶ schemeSpace Y') (k' : W' ⟶ schemeSpace Y')
    (h : X' ⟶ X) (j : Z' ⟶ Z) (d : W' ⟶ W)
    (p : W ⟶ X) (q : W ⟶ Z) (p' : W' ⟶ X') (q' : W' ⟶ Z')
    (sq : h ≫ f = f' ≫ schemeMap g)
    (sq' : j ≫ l = l' ≫ schemeMap g)
    (sqW : d ≫ k = k' ≫ schemeMap g)
    (hp : p ≫ f = k) (hq : q ≫ l = k) (hp' : p' ≫ f' = k') (hq' : q' ≫ l' = k'),
    admissible f → admissible l → d ≫ p = p' ≫ h → d ≫ q = q' ≫ j →
    IsPullback p.hom q.hom f.hom l.hom →
    IsPullback p'.hom q'.hom f'.hom l'.hom →
    IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    IsPullback j.hom l'.hom l.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    IsPullback d.hom k'.hom k.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    (t.tensor (sections A Y e X f) (sections A Y e Z l)).hom ≫
      (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).map
        (FlatExternalCup.external c A Y e f l k p q hp hq) ≫
      baseChange c e e' g k d k' sqW =
    (baseChange c e e' g f h f' sq ⊗ₘ baseChange c e e' g l j l' sq') ≫
      FlatExternalCup.external c B Y' e' f' l' k' p' q' hp' hq'

/-- Identity and composition of the canonical scalar comparison, with its adjoint compositors.
Source: Stacks 08IR, 0H9A (blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure BaseChangeComposition (c : Comparisons (S := S)) where
  identity : ∀ (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (sq : (𝟙 X) ≫ f = f ≫ schemeMap (𝟙 Y)), admissible f →
    baseChange c e e (𝟙 Y) f (𝟙 X) f sq =
      (extensionId A Y e c).hom.app (sections A Y e X f)
  composition : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {Y Y' Y'' : Over S} (e : Y.left ≅ Spec (.of A))
    (e' : Y'.left ≅ Spec (.of B)) (e'' : Y''.left ≅ Spec (.of C))
    (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') {X X' X'' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (f'' : X'' ⟶ schemeSpace Y'')
    (h : X' ⟶ X) (h' : X'' ⟶ X')
    (sq : h ≫ f = f' ≫ schemeMap g)
    (sq' : h' ≫ f' = f'' ≫ schemeMap g')
    (sq'' : (h' ≫ h) ≫ f = f'' ≫ schemeMap (g' ≫ g)),
    admissible f →
    IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g) →
    IsPullback h'.hom f''.hom f'.hom ((Scheme.fppfTopology.over S).yoneda.map g') →
    (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e' e'' g')).map
        (baseChange c e e' g f h f' sq) ≫ baseChange c e' e'' g' f' h' f'' sq' =
      (extensionComp c e e' e'' g g').hom.app (sections A Y e X f) ≫
        baseChange c e e'' (g' ≫ g) f (h' ≫ h) f'' sq''

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Agreement with the ordinary Zariski cup under the canonical derived comparison.
Source: Stacks 071Q, 0FPJ (blueprint: lem-sfb-flat-space-derived-external-cup). -/
structure ZariskiLaws {A : Type u} [CommRing A] {Y Z : Over S}
    {e : Y.left ≅ Spec (.of A)} {g : Z ⟶ Y} (d : ZariskiComparison A Y Z e g) : Prop where
  cup : mul A Y e (schemeSpace Z) (schemeMap g) ≫ d.comparison =
    (d.comparison ⊗ₘ d.comparison) ≫ d.multiplication
  invertible : IsIso d.comparison

/-- Flat qcqs derived external cup, with all its canonical algebra and comparison laws.
Source: Stacks 08IN, 08IR, 071Q, 0FPL, 0FPM, 0FPN and 0H9A
(blueprint: lem-sfb-flat-space-derived-external-cup).

Proof plan (the ten steps of the DAG node).
1. Use fibreProduct_isAlgebraicSpace, quasiCompact_iff_quasiCompact_scheme_tests and
flat_proper_fp_locality to retain flat qcqs under products and arbitrary base change.
The diagonal is a monomorphism, so its own diagonal is an isomorphism and it is qs.
2. Use exists_affineEtaleDerivedModuleRealization, affineDerivedSectionsComposition,
and affineStructureDerivedIso to normalize RΓ, its compositors, and the structural unit.
The chartwise evaluation equations give the two equivalent presentations of sections.
3. The cup is the adjoint of the tensor comparison followed by the two counits.
ringedDerivedMonoidalComparisons and monoidal-adjunction mates give associativity,
unit and symmetry, with the Koszul sign supplied by the representative tensor model.
4. Transpose the geometric unit and regular-function structure map. Unit/counit
naturality gives preservation of cup and unit, and identity/composition of pullbacks.
5. Apply lem-sfb-space-qcqs-derived-projection-formula, followed by
lem-sfb-flat-space-derived-pushforward-base-change along the flat factor. The resulting
isomorphism has transpose the tensor of the two pulled-back counits, hence is external.
6. On four factors, interchange the middle two, then apply the two multiplications.
The representative symmetry contributes (-1)^(bc); the two counits show this is exactly
the multiplication-preservation equation. The unit equation is the same calculation.
7. The already established pullback and algebra equations prove external naturality,
reassociation, permutations, the affine unit factors, and the two projection formulas.
8. For any R → B, flatness of the STRUCTURE morphism gives Tor independence.
Apply the same base-change theorem to O; this proves the canonical scalar-adjoint
comparison invertible, with no flatness assumption on B.
9. ringedExchangeTensorCoherence gives multiplication and unit preservation; mate
pasting gives compatibility with pullbacks, external cup and coefficient composition.
The scalar tensor comparisons descend ordinary scalar extension on flat K-flat models.
10. derived_etale_zariski_equivalence and
lem-sfb-scheme-derived-etale-qcoh-comparison identify the structure object under actual
restriction to opens. The ordinary section and derived-unit equations fix the comparison.
The same tensor-of-counits calculation identifies cup with the Zariski ringed-site cup.
-/
theorem flat_space_derived_external_cup :
    ∃ c : Comparisons (S := S),
      (∀ (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A)),
        Nonempty (AlgebraLaws c A Y e) ∧ Nonempty (ExternalCoherence c A Y e)) ∧
      (∀ {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
        (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B)) (g : Y' ⟶ Y),
        ∃ t : ScalarTensor (spaceAffineRingMap e e' g),
          Nonempty (BaseChangeLaws c e e' g t) ∧
          Nonempty (BaseChangeNaturality c e e' g t)) ∧
      Nonempty (BaseChangeComposition c) ∧
      (∀ (A : Type u) [CommRing A] (Y Z : Over S) (e : Y.left ≅ Spec (.of A))
        (g : Z ⟶ Y), admissible (schemeMap g) →
        ∃ d : ZariskiComparison A Y Z e g, ZariskiLaws d) := by
  sorry

end FlatExternalCup
end AlgebraicGeometry.AlgebraicSpace
