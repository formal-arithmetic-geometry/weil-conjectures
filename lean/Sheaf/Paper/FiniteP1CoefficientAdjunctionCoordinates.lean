/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.TowerP1CoefficientCoordinates
public import Sheaf.AlgebraicGeometry.GeoP1Cohomology

/-! # Finite coefficient and adjunction coordinates

Source: blueprint latest, diagonal-tower trace proof (1), identification of
finite coefficient units and direct images before the Chern-class calculation.
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The inverse of the constant-section-normalized coefficient word.
Source: diagonal-tower trace (1), constant coefficient identification
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates). -/
def finiteUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (SpTowerShriek.Ev l E T n).obj (unit T (Arings l E T)) ≅
      (Scheme.sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory.obj
        (geoP1Unit (FiniteRing l E n) T) :=
  (SpTowerP1.nuSingle l E n T _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c.unit ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).symm

/-- Realize a fixed-scalar object on P¹ on an isomorphic scheme X.
Source: diagonal-tower trace (1), transport over the base
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates). -/
abbrev finiteOverRealization (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S) :=
  geoP1Pullback (FiniteRing l E n) e.hom ⋙
    (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor.mapDerivedCategory

/-- The normalized source comparison, including pullback along e.
Source: diagonal-tower trace (1), coefficient units
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates). -/
def finiteOverUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    (SpTowerShriek.Ev l E X n).obj (unit X (Arings l E X)) ≅
      (finiteOverRealization l E n e).obj (geoP1Unit (FiniteRing l E n) (ProjectiveLine S)) :=
  finiteUnitCoordinate l E n X c ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1UnitPullback (FiniteRing l E n) e.hom).symm

/-- Finite coordinate comparisons preserve the ordinary adjunction and the
normalized coefficient pullback. This statement contains no Chern class.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), finite unit and direct-image
identifications; `sk-prop-sp-tower-geometric-p1.proof.md`, Levels.
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates).

Proof: on each etale chart and each pro-etale refinement, the constant module
comparison sends a scalar to that same scalar. For the positive line send
`a tensor z` to `a tensor z`, using cartierRootsIso. The universal properties
of constant-sheaf extension and of the tensor sheaf give CoefficientCoordinates
on S and X; the displayed section formulas determine these isomorphisms.
The section-normalized direct-image realization comparison, derived on
K-injective representatives, identifies intrinsic and fixed-scalar direct
images. Pullback along the isomorphism e is an equivalence, and he identifies
the composite direct image with that for the projection. These comparisons
and their inverse-image mates give p and q. The mate unit equation is the
first displayed equation, for every derived object M. On the coefficient
single complexes the second equation is the ordinary adjoint of cp.iso:
cp.normalization identifies its sections with the constant-ring restriction.
All the realization comparisons have that same section normalization, so
these ordinary maps agree; exact localization and the single comparisons
then give the second displayed equation. No cohomology or decomposition
isomorphism is used. The constructions work for empty schemes and the zero
ring, and the exponent n+1 is positive even at n=0. -/
theorem finiteP1_coefficient_adjunction_coordinates
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (e : X ≅ ProjectiveLine S) (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (g : SpTowerShriek.Geometry l E b f) (cp : CoefficientPullback l E b f g)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    let A := FiniteRing l E n
    let F := (Scheme.sfIntrinsicModuleEquivalence S
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory
    let H := finiteOverRealization l E n e
    let L := Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f
    let R := (Scheme.proEtaleConstantRingPushforward
      (SpTowerShriek.R l E n) f).rightDerivedFunctor
    let ad := (Scheme.proEtaleConstantRingAdjunction
      (SpTowerShriek.R l E n) f).mapDerivedCategoryRightDerivedAdjunction
    let ap := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)
    ∃ (hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
      (cX : SpTowerP1.CoefficientCoordinates l E n X hX)
      (cS : SpTowerP1.CoefficientCoordinates l E n S
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))
      (p : F ⋙ L ≅ geoP1Pullback A (ProjectiveLine S ↘ S) ⋙ H)
      (q : H ⋙ R ≅ geoP1Pushforward A (ProjectiveLine S ↘ S) ⋙ F),
      (∀ M, ad.unit.app (F.obj M) ≫ R.map (p.hom.app M) ≫
        q.hom.app ((geoP1Pullback A (ProjectiveLine S ↘ S)).obj M) = F.map (ap.unit.app M)) ∧
      ((g.pullEvaluation n).inv.app (unit S (Arings l E S)) ≫
        (SpTowerShriek.Ev l E X n).map (cp.derivedIso l E).hom ≫
        (finiteOverUnitCoordinate l E n e cX).hom =
      L.map (finiteUnitCoordinate l E n S cS).hom ≫ p.hom.app (geoP1Unit A S) ≫
        H.map (geoP1UnitPullback A (ProjectiveLine S ↘ S)).hom) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
