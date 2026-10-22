module

public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.SupportedCup
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Paper.VectorIntegrationSiteComparison

/-! # Coordinate Cartier boundaries in the affine-space tower

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 1--3 (blueprint: def-pur-affine-space-coordinate-boundaries).
The actual normalized ordinary boundary is realized by the exact site comparison
and its closed exchange. All positive coefficient levels are retained.

## Main definitions

- `ordinaryBoundary`: the canonical ordinary coordinate Cartier boundary.
- `realizeBoundary`: the canonical closed-support site comparison on derived arrows.
- `boundary`: its realization in the shifted-line coordinates of ordered gamma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

/-- Positive-level reindexing. Source: finite conventions
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
abbrev setting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_le_succ (Nat.zero_le n) }

/-- The same fixed-scalar category. Source: finite conventions
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
abbrev D (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :=
  CupDerivedCategory (setting P n) X

/-- The degree-zero coefficient unit. Source: the displayed Thom map
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
abbrev unit (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) : D P n X :=
  (cupSingle (setting P n) X).obj ((setting P n).constant X)

/-- The cached coefficient unit is literally the canonical degree-zero complex.
Source: coefficient-unit convention, proof Step 1
(blueprint: def-pur-affine-space-coordinate-boundaries).
Proof: unfold unit, cupSingle and cupHasDerivedCategory. Both sides use the
same canonical HasDerivedCategory instance and the same degree-zero embedding. -/
theorem unit_single_eq (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    unit P n X = (DerivedCategory.singleFunctor _ 0).obj ((setting P n).constant X) := by
  sorry

/-- The zero vector in the standard ordered affine tower. Source: Step 1
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
def zero (B : Scheme.{u}) (c : ℕ) : B ⟶ iteratedAffineLine B c :=
  Scheme.Hom.toIteratedAffineLine (𝟙 B) (fun _ : Fin c ↦ 0)

/-- The coordinate divisor as an actual zero subscheme. Source: coordinate classes
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
abbrev divisor (B : Scheme.{u}) (c : ℕ) (i : Fin c) :=
  (iteratedAffineLine B c).zeroLocusSubscheme
    {iteratedAffineLine.coord B c i}

/-- The coordinate divisor inclusion. Source: coordinate classes
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
abbrev inclusion (B : Scheme.{u}) (c : ℕ) (i : Fin c) :
    divisor B c i ⟶ iteratedAffineLine B c :=
  (iteratedAffineLine B c).zeroLocusSubschemeι {iteratedAffineLine.coord B c i}

/-- Coordinates are Cartier over every base, including a nonreduced or empty base.
Source: proof Step 1 (blueprint: def-pur-affine-space-coordinate-boundaries).
Proof: on a polynomial affine chart each coordinate is a nonzerodivisor, by
coefficient comparison. Its principal ideal is free of rank one and the local
identifications commute with localization, hence glue. -/
theorem coordinate_cartier (B : Scheme.{u}) (c : ℕ) (i : Fin c) :
    (inclusion B c i).ker.IsInvertible := by
  sorry

/-- The zero section is a closed immersion. Source: proof Step 1
(blueprint: def-pur-affine-space-coordinate-boundaries).
Proof: the zero section is the composite of the closed last-coordinate sections;
at dimension zero it is the identity. Closed immersions compose. -/
theorem zero_closed (B : Scheme.{u}) (c : ℕ) : IsClosedImmersion (zero B c) := by
  sorry
attribute [instance] zero_closed

/-- The coordinate-normalized ordinary boundary, at the same exponent as gamma.
This is the already recorded simultaneous Cartier family, not a selected generator.
Source: proof Steps 1--3 (blueprint: def-pur-affine-space-coordinate-boundaries). -/
@[irreducible]
def ordinaryBoundary (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
        (inclusion B c i)).obj ((setting P n).constantEtale (divisor B c i)))
      (Scheme.finiteEtaleTateLine (iteratedAffineLine B c)
        (P.coefficients.l ^ (n + 1 + 1)) (setting P n).Coefficient
        (AffineSpacePurity.annihilates (setting P n))) 2 :=
  (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose.1
    n (n + 1) (AffineSpacePurity.annihilates (setting P n))
    (inclusion B c i) (coordinate_cartier B c i)
    (AffineLinePurity.primeUnit (setting P n) (iteratedAffineLine B c)
      (AffineSpacePurity.towerBase aB c))

/-- Realize a supported ordinary degree-two arrow using the canonical closed
site exchange. Source: proof Step 3
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
@[irreducible]
def realizeBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (α : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) L 2) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj M)) ⟶
      (comparison A X).obj (((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) :=
  letI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  (DerivedCategory.singleFunctor _ 0).map
      (asIso ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app M)).inv ≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0).inv.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) ≫
    (comparison A X).map α.hom

/-- Pull back degree-zero sheaves by the canonical exact derived comparison.
Source: coefficient-unit comparison in Steps 1--3
(blueprint: def-pur-affine-space-coordinate-boundaries). -/
def pullbackSingle (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (e : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    (AffineSpacePurity.inverseImage A f).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj N :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The actual Cartier boundary in the compared shifted-line coordinates.
Source: proof Steps 2--3 (blueprint: def-pur-affine-space-coordinate-boundaries). -/
@[irreducible]
def boundary (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (inclusion B c i)).obj
        ((setting P n).constant (divisor B c i))) ⟶
      AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c) :=
  realizeBoundary (setting P n).Coefficient (inclusion B c i)
    ((setting P n).constantEtale (divisor B c i))
    (Scheme.finiteEtaleTateLine (iteratedAffineLine B c)
      (P.coefficients.l ^ (n + 1 + 1)) (setting P n).Coefficient
      (AffineSpacePurity.annihilates (setting P n))) (ordinaryBoundary P n B aB c i)


end AlgebraicGeometry.ProEtale.AffineZeroPurity
