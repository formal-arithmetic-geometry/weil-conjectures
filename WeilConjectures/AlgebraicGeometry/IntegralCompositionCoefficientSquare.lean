/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekCompositionNormalization
public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
-- Keep the rework ancestors available when their restored modules are rebuilt.
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionConstructibleIntrinsic

/-! # Integral coefficient compatibility of compact-support composition

The two-field integral step of the normalized compact-support composition argument.
Source: Stacks 0F7J and Bhatt--Scholze Definition 6.7.6.
(blueprint: lem-zl-integral-composition-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport GeneralAlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))


variable (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The integral proper/open compositor square for one coefficient inclusion.

Source: Stacks 0F7J, displayed proper/open formula and independence of choices;
Bhatt--Scholze Definition 6.7.6; blueprint lem-fix-operation-reduction, final
paragraph (blueprint: lem-zl-integral-composition-coefficient-square).

Proof: dominate the three compactifications by a compatible tower. Expand the two
compositors using their assumed SfIntegralCompositionSpec equations on this tower.
The open adjunct defining Gamma is uniquely fixed by inverse Lambda. Scalar
extension respects the open unit, proper counit and pullback compositor defining
Lambda, hence also its inverse and its open adjunct. Paste this square with the
proper and open composition squares to obtain the completed coefficient square on
the tower. Tensor associativity identifies the successive scalar extensions.
The normalized refinement comparisons commute with these scalar mates, so their
inverse pairs cancel when transporting to the three prescribed compactifications.
The projection-normalized qcqs realization identifies this transported square with
the integral functors. To identify each supplied beta, use its finite tensor-unit
mate equation simultaneously on normalized strict quotient towers: these are the
same proper/open mates before total limit, and their normalized Roos maps preserve
both coordinates. Apply the total-limit functor to this equality of tower maps.
To pass from these reduction equations to integral arrow equality, use the
constructible mapping-limit argument of integralConstructibleReductionHom: the
shifted Hom groups into restricted finite reductions are finite, hence their tower
is Mittag--Leffler and the Milnor lim-one obstruction vanishes. For the present qcqs
schemes, which need not be separated over the base, extend the finiteness calculation
from separated schemes using a finite affine open cover. Its intersections are
quasicompact separated finite-type schemes; the Cech spectral sequence in the fixed
Hom degree has finitely many nonzero terms because the inputs are bounded. All terms
are finite by finite-coefficient constructible Hom finiteness. Thus the same Milnor
injectivity applies. The normalized scalar units identify the finite mate equations
with reductions of the two displayed composites, giving the asserted equality.
This applies also to identity coefficient inclusions, zero inputs and empty schemes.
No rationalization or finite-stage transport is used. -/
theorem sfIntegralComposition_coefficient_comm
    (AE : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E)
    (AL : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf L ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg L ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg L)
    (hAE : SfIntegralCompositionSpec l E D.k (coefficientPrimeUnit l D hl) cf cg cfg AE)
    (hAL : SfIntegralCompositionSpec l L D.k (coefficientPrimeUnit l D hl) cf cg cfg AL)
    (bf : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf L)
    (bg : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ⋙
        sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι Z ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι Y ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg L)
    (bfg : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E ⋙
        sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι Z ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg L)
    (hbf : SfCompactSupportIntegralBetaSpec l D.k (coefficientPrimeUnit l D hl) cf E L ι bf)
    (hbg : SfCompactSupportIntegralBetaSpec l D.k (coefficientPrimeUnit l D hl) cg E L ι bg)
    (hbfg : SfCompactSupportIntegralBetaSpec l D.k (coefficientPrimeUnit l D hl) cfg
      E L ι bfg)
    (K : sfIntegralConstructibleCategory l E X) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι Z).map (AE.hom.app K) ≫ bfg.hom.app K =
      bg.hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            cf E).obj K) ≫
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg L).map
          (bf.hom.app K) ≫
        AL.hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) := by sorry

end WeilConjectures
