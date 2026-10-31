/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalDualFormulaAdjunction

/-! # Scalar extension of the normalized dual-formula counit

Source: lem-coef-rational-operations, steps 19--20, applying the integral
dual-formula scalar transpose and localizing its equation
(blueprint: lem-sf-rational-dual-formula-scalar-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (S : System l Ω D hl (f := f))
  (F G : FieldStage.{u} l) (ι : F.carrier →ₐ[Padic l] G.carrier)

/-- The composite duality/pullback scalar map transposes to scalar extension of the
trace-normalized counit. This statement involves no isomorphism from an exceptional
right adjoint: both adjunctions are on the dual formulas themselves.
Source: lem-coef-rational-operations, steps 19--20
(blueprint: lem-sf-rational-dual-formula-scalar-counit).

Proof: unpack both normalization witnesses. Apply
coef_dual_formula_scalar_transpose to their integral adjunctions, using the supplied
ordinary tensor presentations on X and Y and the two witnesses on the compactification.
FormulaNormalized characterizes the identity as the formula isomorphism, so uniqueness
in formula_existsUnique makes both kappa factors identities. Thus exceptionalScalar
is precisely the integral composite beta_X followed by duality of the inverse target
beta and inverse pullback comparison. Cancel the faithful constructible inclusion and
the compact-support realization to obtain its integral counit equation. The normalized
integral comparison of S is the same proper/open finite-free support comparison:
integralLeft_normalized and comparison_normalized identify both completion conjugations.
Localize this equation. The counit clauses in the two normalization witnesses identify
the counits, and normalizedX and normalizedY identify the scalar duality maps with
localized beta. The pure-map clauses for rational duality and the normalization of the
rational pullback comparison identify the inverse and contravariant composite with
dualScalar. Finally rational_normalized identifies the localized support map with
the conjugate of S.fields.rationalComparison.q by the two rationalLeft isomorphisms.
Every rational object is an integral object in raw localization, so this proves the
equation for all M. Only functorial preservation of composition is used to localize an
equation; no faithfulness of finite reductions or choice of exceptional comparison is
used. The identity extension is covered by the same argument. -/
theorem rationalDualFormulaScalarCounit
    (wXF : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (wYF : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
    (wXG : IntegralFiniteExtension.DualizingDatum l X D hl G.carrier)
    (wYG : IntegralFiniteExtension.DualizingDatum l Y D hl G.carrier)
    (DXF : RationalVerdier.Datum D l hl X F.carrier wXF)
    (DYF : RationalVerdier.Datum D l hl Y F.carrier wYF)
    (DXG : RationalVerdier.Datum D l hl X G.carrier wXG)
    (DYG : RationalVerdier.Datum D l hl Y G.carrier wYG)
    (adjF : sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
        dualFormula l X D hl (f := f) F wXF wYF DXF DYF)
    (adjG : sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c G.carrier ⊣
        dualFormula l X D hl (f := f) G wXG wYG DXG DYG)
    (hF : DualFormulaAdjunctionNormalized D l hl X c F wXF wYF DXF DYF adjF)
    (hG : DualFormulaAdjunctionNormalized D l hl X c G wXG wYG DXG DYG adjG)
    (eX : RationalVerdier.Extension D l hl X F.carrier G.carrier ι wXF wXG DXF DXG)
    (eY : RationalVerdier.Extension D l hl Y F.carrier G.carrier ι wYF wYG DYF DYG)
    (normalizedX : RationalVerdier.ExtensionProperties D l hl X F.carrier G.carrier ι
      wXF wXG DXF DXG eX)
    (normalizedY : RationalVerdier.ExtensionProperties D l hl Y F.carrier G.carrier ι
      wYF wYG DYF DYG eY)
    (M : sfRationalConstructibleCategory l F.carrier Y) :
    let alpha :=
      Functor.isoWhiskerRight (S.ring.rationalLeft c F).symm
          (RationalVerdier.scalar l Y F.carrier G.carrier ι) ≪≫
        (S.fields.rationalComparison c F G ι).q ≪≫
        Functor.isoWhiskerLeft (RationalVerdier.scalar l X F.carrier G.carrier ι)
          (S.ring.rationalLeft c G)
    let delta :=
      eX.comparison.hom.app (op
          ((@rationalDerivedPullback l _ F.carrier _ _ _ X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
              (DYF.dual.obj (op M)))) ≫
        DXG.dual.map
          (((@rationalDerivedPullback l _ G.carrier _ _ _ X Y f
              (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).map
                (eY.comparison.inv.app (op M)) ≫
            (@rationalPullbackScalarComparison l _ F.carrier _ _ _ G.carrier _ _ _ ι X Y f
              (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).inv.app
                (DYF.dual.obj (op M))).op)
    (sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c G.carrier).map
          delta ≫
      adjG.counit.app ((RationalVerdier.scalar l Y F.carrier G.carrier ι).obj M) =
    alpha.inv.app ((dualFormula l X D hl (f := f) F wXF wYF DXF DYF).obj M) ≫
      (RationalVerdier.scalar l Y F.carrier G.carrier ι).map (adjF.counit.app M) := by sorry

end WeilConjectures.RationalOperations
