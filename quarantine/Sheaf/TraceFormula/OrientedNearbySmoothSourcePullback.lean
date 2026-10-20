/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.TraceFormula.BoundedConstructibleTransport
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.Paper.OrientedNearbyStrictLocalDescription
import Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes

/-! # Smooth source pullback of oriented nearby cycles

Source: Orgogozo, *Modifications et cycles proches sur une base generale*, Section 9.3,
printed p. 22; ILO, Expose XI 1.4--1.5, 1.9, 4.3
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback).

The smooth-source comparison is an isomorphism on the whole vanishing topos, and its
ordinary counit mate commutes with every Cartesian base change of the base.
This statement packet records the reviewed interface for group Q31.

The helper definitions construct the canonical etale and vanishing-topos pullback
identifications. The latter is specified uniquely by its two projection equations.
`SmoothSourceBaseChangeCompatible` writes out the step-5 pasting equality using them.
The main theorem includes boundedness and constructibility of every cohomology sheaf.

The coefficient universe u+1 is the size convention of the recorded
`OrientedNearbyCycles.IsBoundedConstructible` interface for Scheme.{u}. The ring
`Coeff Λ` is its canonically equivalent ULift; AsSmall changes only the site presentation.
This is the same D^b_c convention as `NearbyProperHyperdescent.hKc`, rather than a
universe restriction imposed by `nearbyCycles` (whose helpers here retain arbitrary v).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The first projection of a composite of two square morphisms, normalized by the
canonical composition of etale site morphisms. Source: ILO XI 1.4--1.5 and 1.9
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback). -/
def squareCompositeFirst {T₀ T₁ T₂ B₀ B₁ B₂ : Scheme.{u}}
    (f₀ : T₀ ⟶ B₀) (f₁ : T₁ ⟶ B₁) (f₂ : T₂ ⟶ B₂)
    (a₁ : T₁ ⟶ T₀) (b₁ : B₁ ⟶ B₀) (c₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
    (a₂ : T₂ ⟶ T₁) (b₂ : B₂ ⟶ B₁) (c₂ : a₂ ≫ f₁ = f₂ ≫ b₂) :
    (((squareMorphism.{u, v} f₁ f₂ a₂ b₂ c₂).comp
      (squareMorphism f₀ f₁ a₁ b₁ c₁)).comp (p₁ f₀)).direct ≅
        ((p₁ f₂).comp (etaleMorphism (a₂ ≫ a₁))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f₀ f₁ a₁ b₁ c₁).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift f₁ f₂ a₂ b₂ c₂).first _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition a₂ a₁)

/-- The second projection, with the same canonical site composition normalization.
Source: ILO XI 1.4--1.5 and 1.9
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback). -/
def squareCompositeSecond {T₀ T₁ T₂ B₀ B₁ B₂ : Scheme.{u}}
    (f₀ : T₀ ⟶ B₀) (f₁ : T₁ ⟶ B₁) (f₂ : T₂ ⟶ B₂)
    (a₁ : T₁ ⟶ T₀) (b₁ : B₁ ⟶ B₀) (c₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
    (a₂ : T₂ ⟶ T₁) (b₂ : B₂ ⟶ B₁) (c₂ : a₂ ≫ f₁ = f₂ ≫ b₂) :
    (((squareMorphism.{u, v} f₁ f₂ a₂ b₂ c₂).comp
      (squareMorphism f₀ f₁ a₁ b₁ c₁)).comp (p₂ f₀)).direct ≅
        ((p₂ f₂).comp (etaleMorphism (b₂ ≫ b₁))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f₀ f₁ a₁ b₁ c₁).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift f₁ f₂ a₂ b₂ c₂).second _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition b₂ b₁)



/-- Projection-normalized uniqueness for the two paths in the vanishing-topos square.
Source: ILO XI 1.4--1.5, 1.9 and 4.3
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback), proof step 5.
Proof: both composites lift the projections p1 followed by a h = h' b and p2 followed
by c. The displayed projection maps are the actual squareLift identifications, followed
by etaleComposition and equality transport. Their orientations agree by ha, hb and the
functoriality of restriction. Apply lem-trf-oriented-product-universal to these two
lifts of the same oriented cone. Its uniqueness clause gives precisely the unique
isomorphism with both displayed projection equations. No base-change theorem or
smoothness hypothesis is used in this construction. -/
theorem smoothSourceVanishingSquare_existsUnique {S X Y S' X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) (h' : X' ⟶ Y') (g' : Y' ⟶ S')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : S' ⟶ S)
    (ha : a ≫ h = h' ≫ b) (hb : b ≫ g = g' ≫ c) :
    ∃! e : ((squareMorphism.{u, v} (h ≫ g) (h' ≫ g') a c
          (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc])).comp
        (squareMorphism g (h ≫ g) h (𝟙 S) (by simp))).direct ≅
      ((squareMorphism g' (h' ≫ g') h' (𝟙 S') (by simp)).comp
        (squareMorphism g g' b c hb)).direct,
      Functor.isoWhiskerRight e (p₁ g).direct ≪≫
          squareCompositeFirst g g' (h' ≫ g') b c hb h' (𝟙 S') (by simp) ≪≫
          Functor.isoWhiskerLeft (p₁ (h' ≫ g')).direct
            (eqToIso (congrArg (fun k ↦ (etaleMorphism.{u, v} k).direct) ha.symm)) =
        squareCompositeFirst g (h ≫ g) (h' ≫ g') h (𝟙 S) (by simp) a c
          (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]) ∧
      Functor.isoWhiskerRight e (p₂ g).direct ≪≫
          squareCompositeSecond g g' (h' ≫ g') b c hb h' (𝟙 S') (by simp) ≪≫
          Functor.isoWhiskerLeft (p₂ (h' ≫ g')).direct
            (eqToIso (congrArg (fun k ↦ (etaleMorphism.{u, v} k).direct)
              (Category.id_comp c))) =
        squareCompositeSecond g (h ≫ g) (h' ≫ g') h (𝟙 S) (by simp) a c
          (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]) ≪≫
          Functor.isoWhiskerLeft (p₂ (h' ≫ g')).direct
            (eqToIso (congrArg (fun k ↦ (etaleMorphism.{u, v} k).direct)
              (Category.comp_id c))) := by
  sorry

/-- The uniquely projection-normalized identification of the two composite morphisms.
Its data is determined by the universal property, including both projection equations.
Source: ILO XI 1.4--1.5, 1.9 (blueprint: lem-trf-oriented-nearby-smooth-source-pullback). -/
def smoothSourceVanishingSquare {S X Y S' X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) (h' : X' ⟶ Y') (g' : Y' ⟶ S')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : S' ⟶ S)
    (ha : a ≫ h = h' ≫ b) (hb : b ≫ g = g' ≫ c) :=
  (smoothSourceVanishingSquare_existsUnique.{u, v} h g h' g' a b c ha hb).choose

/-- The canonical derived identification a* h* = h'* b* from the scheme square.
It is the generator-normalized exact module lift of the inverse-image mate of
squareDirect, which is built from etale site composition, not a chosen isomorphism.
Source: ILO XI 1.9 (blueprint: lem-trf-oriented-nearby-smooth-source-pullback). -/
def smoothSourceEtalePullSquare {X Y X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (h' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : a ≫ h = h' ≫ b) (Λ : Type v) [CommRing Λ] :
    (etaleModules h).pull (Coeff.{u, v} Λ) ⋙ (etaleModules a).pull (Coeff Λ) ≅
      (etaleModules b).pull (Coeff Λ) ⋙ (etaleModules h').pull (Coeff Λ) :=
  CategoryTheory.AdicSites.derivedSquare
    (f := etaleModules b) (g := etaleModules h)
    (h := etaleModules h') (k := etaleModules a)
    (GeometricMorphism.inverseIso (squareDirect h h' a b ha)).symm (Coeff Λ)

/-- The canonical derived identification v_f* hbar* = hbar'* v_g*.
It is the generator-normalized module lift of the unique projection-compatible
oriented-product square, so its maps are fixed before the pasting theorem is stated.
Source: ILO XI 1.4--1.5, 1.9 and 4.3
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback). -/
def smoothSourceVanishingPullSquare {S X Y S' X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) (h' : X' ⟶ Y') (g' : Y' ⟶ S')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : S' ⟶ S)
    (ha : a ≫ h = h' ≫ b) (hb : b ≫ g = g' ≫ c)
    (Λ : Type v) [CommRing Λ] :
    (squareModules g (h ≫ g) h (𝟙 S) (by simp)).pull (Coeff.{u, v} Λ) ⋙
        (squareModules (h ≫ g) (h' ≫ g') a c
          (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc])).pull (Coeff Λ) ≅
      (squareModules g g' b c hb).pull (Coeff Λ) ⋙
        (squareModules g' (h' ≫ g') h' (𝟙 S') (by simp)).pull (Coeff Λ) :=
  CategoryTheory.AdicSites.derivedSquare
    (f := squareModules g g' b c hb)
    (g := squareModules g (h ≫ g) h (𝟙 S) (by simp))
    (h := squareModules g' (h' ≫ g') h' (𝟙 S') (by simp))
    (k := squareModules (h ≫ g) (h' ≫ g') a c
      (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]))
    (GeometricMorphism.inverseIso
      (smoothSourceVanishingSquare h g h' g' a b c ha hb)).symm (Coeff Λ)

end AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- Compatibility with every Cartesian base change of the base, expressed as equality
of the two ordinary counit-mate composites. The two endpoint identifications are the
canonical site/unique-oriented-product identifications defined above.
Source: ILO XI 1.4--1.5, 1.9, 4.3; Orgogozo 9.3
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback), proof step 5. -/
def SmoothSourceBaseChangeCompatible {S X Y : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) (Λ : Type v) [CommRing Λ] (L : EtaleDerived Y Λ) : Prop :=
  ∀ (S' X' Y' : Scheme.{u}) (h' : X' ⟶ Y') (g' : Y' ⟶ S')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : S' ⟶ S)
    (ha : a ≫ h = h' ≫ b) (hb : b ≫ g = g' ≫ c),
    IsPullback a (h' ≫ g') (h ≫ g) c → IsPullback b g' g c →
    ((squareModules (h ≫ g) (h' ≫ g') a c
        (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc])).pull
          (Coeff.{u, v} Λ)).map (baseChange g (h ≫ g) h (𝟙 S) (by simp) Λ L) ≫
      baseChange (h ≫ g) (h' ≫ g') a c
        (by rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]) Λ
        (((etaleModules h).pull (Coeff Λ)).obj L) ≫
      (nearbyCycles (h' ≫ g') Λ).map
        ((smoothSourceEtalePullSquare h h' a b ha Λ).hom.app L) =
    (smoothSourceVanishingPullSquare h g h' g' a b c ha hb Λ).hom.app
        ((nearbyCycles g Λ).obj L) ≫
      ((squareModules g' (h' ≫ g') h' (𝟙 S') (by simp)).pull (Coeff Λ)).map
        (baseChange g g' b c hb Λ L) ≫
      baseChange g' (h' ≫ g') h' (𝟙 S') (by simp) Λ
        (((etaleModules b).pull (Coeff Λ)).obj L)

end AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry

/-- Smooth-source pullback of oriented nearby cycles, including its ordinary
base-change compatibility, for a bounded constructible input.
Source: Orgogozo, Section 9.3, printed p. 22; ILO XI 1.4--1.5 and 4.1--4.3
(blueprint: lem-trf-oriented-nearby-smooth-source-pullback).

The condition hL uses the recorded bounded-constructible predicate, including
constructibility of every cohomology sheaf through the canonical constant-ring
sheafification unit and AsSmall transport in the oriented-site model.
The coefficient universe follows that recorded D^b_c interface, not the more general
universe-polymorphic nearbyCycles construction.

Proof plan (the five DAG steps):
1. Apply lem-trf-oriented-product-universal to h p1 and p2, with the composite
   orientation. This constructs hbar and its projection-compatible identification
   hbar psi_f = psi_g h. By def-trf-oriented-nearby-cycles its counit mate is exactly
   baseChange g (h ≫ g) h (identity S). Smoothness, finite presentation and the
   coefficient annihilator persist after base change.
2. Fix an oriented point (x,t,c), put y = h(x), and identify its image with (y,t,c)
   using both projections and the orientation. By lem-trf-oriented-point-cohomology
   the two stalks are RΓ(Y_(y) ×_{S_(s)} S_(t), L) and
   RΓ(X_(x) ×_{S_(s)} S_(t), h*L), with the fiber products formed through c.
   Boundedness gives bounded-below complexes. Equivalently apply
   lem-trf-oriented-nearby-strict-local-description to sigma_y = hbar sigma_x.
   Naturality of restriction from pointed neighborhoods identifies the stalk arrow
   with the actual pullback map of these strict-local tubes: both arrows are the
   adjoints of the defining counit composite.
3. Apply lem-trf-smooth-source-constructible-local-acyclicity to this pullback map.
   Its hypotheses are the Noetherian base, the two finite-presentation maps,
   smoothness of h, the invertible annihilator and bounded constructibility of L.
   This makes every displayed oriented-point stalk map an isomorphism.
4. The oriented-point inverse images are jointly conservative by
   lem-trf-oriented-product-points-conservative. Thus the comparison is an
   isomorphism of objects on the whole vanishing topos, without Psi-goodness.
5. For any S' → S take the Cartesian X' and Y', with maps a = u, b = w, c and h'.
   The two composite scheme squares coincide. Uniqueness of the oriented-product
   lift, with the two specified projection equations in
   smoothSourceVanishingSquare_existsUnique, identifies hbar v_f with v_g hbar'.
   Canonical etale site composition similarly gives a* h* = h'* b*.
   Each beta is the mate of the psi-square followed by the counit. Clauses 1 and 2
   of lem-weil-pbc-mate-pasting identify both pasted maps with the ordinary comparison
   of the outer square. Therefore beta_a after v_f* beta_h, followed by the etale
   endpoint identification, equals beta_h' after hbar'* beta_b, preceded by the
   vanishing-topos identification. This is the exact equality in
   SmoothSourceBaseChangeCompatible; no Noetherian or other hypothesis on S' is used.
-/
theorem orientedNearby_smoothSource_pullback
    {S X Y : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    [IsNoetherian S]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h] [Smooth h]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]
    (L : EtaleDerived Y Λ) (hL : IsBoundedConstructible Y Λ L) :
    IsIso (baseChange g (h ≫ g) h (𝟙 S) (by simp) Λ L) ∧
      SmoothSourceBaseChangeCompatible h g Λ L := by
  sorry

end AlgebraicGeometry
