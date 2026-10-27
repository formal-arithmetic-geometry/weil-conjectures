module

public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.PurityCompositionCoherence

/-! # Coordinates for nested affine orientations

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1)
(blueprint: def-sp-nested-affine-orientation-coordinates).

This definition interface re-exports the specified ordinary diagonal orientation,
its coefficient-unit conversion, the smooth affine-projection evidence, and ordered
shifted Tate concatenation including its zero and successor identifications.
Every abbreviation is the existing construction, with no new choices or proofs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.NestedAffineCoordinates

/-- The ordinary representative of the uniquely specified diagonal orientation.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev chartOrdinaryOrientation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  _root_.WeilConjectures.PurityFiniteSetting.chartOrdinaryOrientation P d f aY

/-- The canonical exceptional image of the coefficient-unit conversion.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev chartDualizingUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalOrdinaryDualizing f :=
  _root_.WeilConjectures.PurityFiniteSetting.chartDualizingUnit P f

/-- The existing smooth rank evidence for the ordered affine projection.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev chartTraceProjection_smooth (B : Scheme.{u}) (r : ℕ) :
    SmoothOfRelativeDimension r (affineTraceProjection B r) :=
  _root_.WeilConjectures.PurityFiniteSetting.chartTraceProjection_smooth B r

/-- The existing recursive ordered tensor-power assembly, with its unit constraints.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev compositionEtalePowerAssembly (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (B : ℕ → _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (z : B 0 ≅ 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology C)))
    (s : ∀ n : ℕ, B (n + 1) ≅ ((Etale.derivedTensor C X).obj (B n)).obj L)
    (d e : ℕ) : B (d + e) ≅ ((Etale.derivedTensor C X).obj (B d)).obj (B e) :=
  _root_.WeilConjectures.PurityFiniteSetting.compositionEtalePowerAssembly C X B L z s d e

/-- The existing degree-zero identification of the shifted Tate power with the unit.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev compositionEtalePowerZero (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) :
    Etale.affineLinearBaseCoefficient A N hA X 0 = Etale.ordinaryFiniteUnit A X :=
  _root_.WeilConjectures.PurityFiniteSetting.compositionEtalePowerZero A N hA X

/-- The existing successor identification with the preceding power tensored with the line.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev compositionEtalePowerSuccessor (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (n : ℕ) :
    Etale.affineLinearBaseCoefficient A N hA X (n + 1) =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Etale.affineLinearBaseCoefficient A N hA X n)).obj
        ((Etale.ordinaryFiniteLine A N
          hA X)⟦(2 : ℤ)⟧) :=
  _root_.WeilConjectures.PurityFiniteSetting.compositionEtalePowerSuccessor A N hA X n

/-- The existing concatenation of ordered even-shifted Tate powers.
Source: composition-factors proof (1), canonical orientation and tensor coordinates
(blueprint: def-sp-nested-affine-orientation-coordinates). -/
abbrev compositionEtalePowerAdd (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (d e : ℕ) :
    Etale.affineLinearBaseCoefficient A N hA X (d + e) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Etale.affineLinearBaseCoefficient A N hA X d)).obj
        (Etale.affineLinearBaseCoefficient A N hA X e) :=
  _root_.WeilConjectures.PurityFiniteSetting.compositionEtalePowerAdd A N hA X d e

end WeilConjectures.PurityFiniteSetting.NestedAffineCoordinates
