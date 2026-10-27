module

public import Sheaf.AlgebraicGeometry.GeoP1Cohomology
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Site comparison of normalized vector-bundle integration

Source: Stacks Project, Tags 099R, 09AF and 0B65; main-20261015,
vector-bundle integration and the normalization in dualizing-object purity.
(blueprint: def-pur-finite-site-coordinates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded exact derived comparison, in ambient coordinates.
Source: Stacks 099R (blueprint: def-pur-finite-site-coordinates). -/
abbrev comparison (T : Scheme.{u}) := geoP1Comparison A T

/-- The ordinary constant complex in comparison coordinates.
Source: Stacks 099R (blueprint: def-pur-finite-site-coordinates). -/
abbrev unit (T : Scheme.{u}) := geoP1Unit A T

/-- The actual inverse-image comparison, with the exact and K-flat presentations identified.
Source: Stacks 099R (blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.ordinaryFinitePullback A f ⋙ comparison A X ≅
      comparison A Y ⋙ (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor :=
  (geoP1PullComparison A f).symm

/-- The canonical mate on ambient realizations of bounded-below inputs.
Source: Stacks 099R and 0B65
(blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def directImage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A Y).obj ((Etale.ordinaryFinitePushforward A f).obj J.obj) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        ((comparison A X).obj J.obj) :=
  (comparison A Y).mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
        J).symm ≪≫
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} A)).app J

/-- The unit identification used in the pro-etale adjunction, in comparison coordinates.
Source: Stacks 099R (blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj (unit A Y) ≅ unit A X :=
  geoP1UnitPullback A f

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The inverse-limit-projection comparison, fixed on every pure root tensor.
This is the existing normalized descent, not a choice of a primitive root or orientation.
Source: Stacks 099R; Cartier Kummer map, projection normalization
(blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def twistComparison (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).obj
      (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d) ≅
        Scheme.finiteTateProSheaf l E n T d :=
  (Scheme.finite_tate_site_descent l E n).choose T hT r hA d

/-- The degree-two pro-etale coefficient expressed in ordinary comparison coordinates.
The isomorphism to the specified inverse-limit twist is `twistComparison` placed in
 degree zero and shifted by two.
Source: projective-line trace (blueprint: def-pur-finite-site-coordinates). -/
abbrev line (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (T : Scheme.{u}) :=
  (comparison (Scheme.finiteTateCoefficient l E n) T).obj
    ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA T)
      ⟦(2 : ℤ)⟧)


/-- The comparison to the inverse-limit twist in the derived category, including shifts.
Source: Stacks 099R (blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def twistDerived (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (m : ℤ) :
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦m⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteTateProSheaf l E n T d))⟦m⟧ :=
  ((comparison (Scheme.finiteTateCoefficient l E n) T).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso
      (((comparisonUpperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (twistComparison l E n T hT r hA d))



/-- Exponent transition fixed by the root power map and the common inverse-limit target.
Source: finite Tate site descent
(blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def exponentTransition (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r r' : ℕ) (h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    Scheme.finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' d ≅
      Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d :=
  ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1 T hT r r' h hA hA' d).exists.choose

/-- The ordered coefficient comparison induced factor by factor by the root power map.
Source: finite Tate site descent and vector integration's ordered coefficient
(blueprint: def-pur-finite-site-coordinates). -/
@[irreducible]
def baseExponentComparison (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r r' : ℕ) (h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (d : ℕ) → Etale.affineLinearBaseCoefficient _ (l ^ (r' + 1)) hA' T d ≅
      Etale.affineLinearBaseCoefficient _ (l ^ (r + 1)) hA T d
  | 0 => Iso.refl _
  | d + 1 =>
    Etale.ordinaryFiniteTensorRightMapIso _ T
      (baseExponentComparison T hT r r' h hA hA' d)
      ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (exponentTransition l E n T hT r r' h hA hA' 1)))

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
