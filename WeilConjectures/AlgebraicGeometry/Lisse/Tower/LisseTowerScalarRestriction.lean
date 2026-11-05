/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationSections
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.CategoryTheory.Constant.ConstantDerivedNormalizationUniversalSupplement
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonNormalizationReflectsUniversal
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSourceNormalizationUniversal
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The scalar square for the fixed finite coefficient realization

Source: Stacks Project, Tags 03DA, 06YY, 099Z and 09B1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization

/-- Normalize a scalar square against specified comparisons of underlying objects.
Keeping this generic prevents reduction of the concrete adic coefficient constructions.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def lisseTowerScalarSquareNormalized
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G) : Prop :=
  (Functor.isoWhiskerRight c H' ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F r ≪≫ a).hom =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q a' ≪≫ q).hom

/-- The square is normalized by the identity on the original fixed sections.
Source: Stacks Tags 03CY and 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerScalarSquareSections {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  lisseTowerScalarSquareNormalized c
    (lisseTowerRestrictForgetIso ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (lisseTowerFixedForgetIso f d n) (lisseTowerFixedForgetIso f d (n + 1))
    (lisseTowerFixedRestrictForgetIso (ProEt.topology Z) (lisseTowerEtaleQuotient d n))

/-- Reflection of one actual normalized transition on every etale source through
its section-normalized coefficient square.
Source: Stacks Tags 06YY, 099Z and 09B1
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerScalarSquareReflects {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  ∀ (M : AdicTower X d)
    (C : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
    (C' : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (_hC : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C))
    (_hC' : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C'))
    (e : (lisseTowerEtaleRealization f d (n + 1)).obj C ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1)))
    (e' : (lisseTowerEtaleRealization f d n).obj C' ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology
      (lisseTowerEtaleQuotient d n)).obj C'),
    (lisseTowerEtaleRealization f d (n + 1)).map δ ≫
        (lisseTowerEtaleScalarIso f d n c).hom.app C' ≫
        (pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map e'.hom =
      e.hom ≫ adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n) →
    ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
        (lisseTowerEtaleQuotient d n) δ V)))

/-- Local universality of constant algebraic normalization arrows at this quotient.
Source: Stacks Tags 06YY and 03ED
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerConstantLocalUniversal (Z : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) : Prop :=
  ∀ (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
      ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
          (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow Z.smallEtaleTopology (lisseTowerEtaleQuotient d n) k) V)))

open CoefficientSheafificationSquare

attribute [local irreducible] lisseTowerFiniteScalarMap lisseTowerFiniteCoefficientIso
  pbcLevelConstantComparison pbcAdicQuotient

@[irreducible] private def scalarSquare {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerScalarSquare f d n :=
  coefficientScalarIso (J := ProEt.topology Z) (q := lisseTowerEtaleQuotient d n)
    (b := constantAdicQuotientMap d.ideal (n + 1)) (b' := constantAdicQuotientMap d.ideal n)
    (a := (adicLisseForget Z).map ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (α := lisseTowerFiniteScalarMap f d (n + 1)) (β := lisseTowerFiniteScalarMap f d n)
    (r := Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (h := completionQuotient_square d n) (ha := finiteScalarMap_square f d n)

attribute [local semireducible] pbcDerivedRestrict

end AlgebraicGeometry.Scheme
