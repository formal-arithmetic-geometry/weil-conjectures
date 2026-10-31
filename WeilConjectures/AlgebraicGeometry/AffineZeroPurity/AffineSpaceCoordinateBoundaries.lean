/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
import WeilConjectures.AlgebraicGeometry.AffineSpaceCharts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

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
  rfl

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

private theorem affine_coordinate_cartier (B : Scheme.{u}) (i : PUnit.{u + 1}) :
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {AffineSpace.coord B i})).IsInvertible := by
  have : ∀ V : B.affineOpens,
      IsOpenImmersion (AffineSpace.chart PUnit.{u + 1} V.2) := fun V ↦ by
    have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
    have : IsOpenImmersion (AffineSpace.map PUnit.{u + 1} V.2.fromSpec) :=
      AffineSpace.isOpenImmersion_map _
    unfold AffineSpace.chart
    infer_instance
  apply Scheme.IdealSheafData.IsInvertible.of_iSup_opensRange_eq_top
    (fun V : B.affineOpens ↦ AffineSpace.chart PUnit.{u + 1} V.2)
    (AffineSpace.iSup_opensRange_chart PUnit.{u + 1})
  intro V
  rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  apply Scheme.IdealSheafData.IsInvertible.of_isAffine
  rw [Scheme.IdealSheafData.ideal_top_ofIdealTop]
  have he : (AffineSpace.chart PUnit.{u + 1} V.2).appTop (AffineSpace.coord B i) =
      (Scheme.ΓSpecIso (.of (MvPolynomial PUnit.{u + 1} Γ(B, V.1)))).inv
        (MvPolynomial.X i) := by
    simp only [AffineSpace.chart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
  rw [he, ← Set.image_singleton, ← Ideal.map_span]
  exact (Ideal.isRegularPrincipal_span_singleton_of_isRegular
    (MvPolynomial.isRegular_X (R := Γ(B, V.1)) (n := i))).map_of_bijective
      (ConcreteCategory.bijective_of_isIso _)

/-- Coordinates are Cartier over every base, including a nonreduced or empty base.
Source: proof Step 1 (blueprint: def-pur-affine-space-coordinate-boundaries).
Proof: on a polynomial affine chart each coordinate is a nonzerodivisor, by
coefficient comparison. Its principal ideal is free of rank one and the local
identifications commute with localization, hence glue. -/
theorem coordinate_cartier (B : Scheme.{u}) (c : ℕ) (i : Fin c) :
    (inclusion B c i).ker.IsInvertible := by
  change (Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {iteratedAffineLine.coord B c i})).subschemeι.ker.IsInvertible
  rw [Scheme.IdealSheafData.ker_subschemeι]
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact affine_coordinate_cartier (iteratedAffineLine B c) PUnit.unit
    · have : Smooth (AffineSpace PUnit.{u + 1} (iteratedAffineLine B c) ↘
          iteratedAffineLine B c) := SmoothOfRelativeDimension.smooth
            (Nat.card PUnit.{u + 1}) _
      have h := (ih j).comap_of_flat
        (AffineSpace PUnit.{u + 1} (iteratedAffineLine B c) ↘ iteratedAffineLine B c)
      rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton] at h
      exact h

/-- The zero section is a closed immersion. Source: proof Step 1
(blueprint: def-pur-affine-space-coordinate-boundaries).
Proof: the zero section is the composite of the closed last-coordinate sections;
at dimension zero it is the identity. Closed immersions compose. -/
theorem zero_closed (B : Scheme.{u}) (c : ℕ) : IsClosedImmersion (zero B c) := by
  induction c with
  | zero => exact inferInstanceAs (IsClosedImmersion (𝟙 B))
  | succ c ih =>
    have hz : zero B (c + 1) = zero B c ≫
        AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B c) := by
      change AffineSpace.homOfVector (zero B c) (fun _ ↦ 0) = _
      rw [AffineSpace.zeroSection, AffineSpace.comp_homOfVector]
      simp only [Category.comp_id]
      congr 1
      ext j
      exact (map_zero _).symm
    rw [hz]
    exact @IsClosedImmersion.comp _ _ _ (zero B c)
      (AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B c)) ih
      (AffineSpace.isClosedImmersion_zeroSection _ _)
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
  let realize {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
      [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
      [HasDerivedCategory.{u + 1} D] (F : C ⥤ D) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (K L : C) (M : D) (e : M ≅ F.obj K)
      (a : (DerivedCategory.singleFunctor C 0).obj K ⟶
        ((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) :
      (DerivedCategory.singleFunctor D 0).obj M ⟶
        F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) :=
    (DerivedCategory.singleFunctor D 0).map e.hom ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app K ≫ F.mapDerivedCategory.map a
  letI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  realize (comparisonUpperStar (ModuleCat.{u + 1} A) X) _ _ _
    (asIso ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app M)).symm
    α.hom

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
