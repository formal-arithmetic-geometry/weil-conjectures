/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurityFiniteSetting.IsomorphismFiniteMateNormalization
public import WeilConjectures.SixFunctors.FiniteExchangeCoherence.IsomorphismFiniteExchangeCoherence
public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReductionReindexing
public import WeilConjectures.AlgebraicGeometry.Pur.PurStrictIntegralExchangeNormalization

/-! # Definition exports for semilinear exchange reindexing

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility
(blueprint: def-pur-semilinear-exchange-reindexing-data).

These transparent exports give the canonical definitions a definition-node owner.
Each right-hand side is the existing construction or predicate, with all original
arguments and universes. No normalization theorem is asserted or used here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace WeilConjectures.PurReindexing

/-- Finite section-normalized Cartesian and open reindexing construction.
Transparent export of `WeilConjectures.PurityFiniteSetting.finiteMateCartesian`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev finiteMateCartesian :=
  @WeilConjectures.PurityFiniteSetting.finiteMateCartesian.{u}

/-- Finite section-normalized Cartesian and open reindexing construction.
Transparent export of `WeilConjectures.PurityFiniteSetting.finiteMateDerivedOpenReindexing`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev finiteMateDerivedOpenReindexing :=
  @WeilConjectures.PurityFiniteSetting.finiteMateDerivedOpenReindexing.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.constantSystem`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev constantSystem :=
  @WeilConjectures.FiniteExchangeCoherence.constantSystem.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.constantChange`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev constantChange :=
  @WeilConjectures.FiniteExchangeCoherence.constantChange.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.pullId`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev pullId :=
  @WeilConjectures.FiniteExchangeCoherence.pullId.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.pushComp`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev pushComp :=
  @WeilConjectures.FiniteExchangeCoherence.pushComp.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.openComp`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev openComp :=
  @WeilConjectures.FiniteExchangeCoherence.openComp.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.composition`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev composition :=
  @WeilConjectures.FiniteExchangeCoherence.composition.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.lower`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev lower :=
  @WeilConjectures.FiniteExchangeCoherence.lower.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.quotient`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev quotient :=
  @WeilConjectures.FiniteExchangeCoherence.quotient.{u}

/-- The existing constant-coefficient operation or its unit-normalized comparison.
Transparent export of `WeilConjectures.FiniteExchangeCoherence.tensorQuotient`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev tensorQuotient :=
  @WeilConjectures.FiniteExchangeCoherence.tensorQuotient.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.purIntegralReindexingExchange`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev purIntegralReindexingExchange :=
  @AlgebraicGeometry.Scheme.purIntegralReindexingExchange.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurIntegralStrictMapNormalization`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurIntegralStrictMapNormalization :=
  @AlgebraicGeometry.Scheme.PurIntegralStrictMapNormalization.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurIntegralStrictHorizontal`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurIntegralStrictHorizontal :=
  @AlgebraicGeometry.Scheme.PurIntegralStrictHorizontal.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurIntegralStrictVertical`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurIntegralStrictVertical :=
  @AlgebraicGeometry.Scheme.PurIntegralStrictVertical.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurIntegralStrictReduction`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurIntegralStrictReduction :=
  @AlgebraicGeometry.Scheme.PurIntegralStrictReduction.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurIntegralCompletedCoherence`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurIntegralCompletedCoherence :=
  @AlgebraicGeometry.Scheme.PurIntegralCompletedCoherence.{u}

/-- The existing strict integral construction or its explicit normalization predicate.
Transparent export of `AlgebraicGeometry.Scheme.PurStrictIntegralGeometricNormalization`.
Source: constituent-compatibility assembly, semilinear exchange definitions
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
abbrev PurStrictIntegralGeometricNormalization :=
  @AlgebraicGeometry.Scheme.PurStrictIntegralGeometricNormalization.{u}

end WeilConjectures.PurReindexing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
open WeilConjectures WeilConjectures.PurityFiniteSetting

namespace WeilConjectures

/-- The finite two-factor identity, with proper counit and open unit normalizations.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
@[irreducible] def PurSemilinearFiniteNormalization (P : PurityFiniteSetting.{u}) : Prop :=
  ∀
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f' : X' ⟶ Y') (g : Y' ≅ Y) (g' : X' ≅ X)
    (c : Compactification f) (c' : Compactification f') (b : c'.Z ≅ c.Z)
    (sqP : ChosenCartesianSquare b.hom c'.g c.g g.hom)
    (sqJ : ChosenCartesianSquare g'.hom c'.i c.i b.hom),
    (mateEquiv (sfCartesianOpenPullPushAdjunction P.Ring c.g)
      (sfCartesianOpenPullPushAdjunction P.Ring c'.g)
      (TwoSquare.mk _ _ _ _
        (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm).hom)
        ).natTrans =
      (sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
        (PurReindexing.finiteMateCartesian sqP).flip).hom ∧
    (∀ M : proEtaleDerivedCategory c.Z P.Ring,
      (sfIntrinsicDerivedPullback P.Ring c'.g).map
          ((sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
            (PurReindexing.finiteMateCartesian sqP).flip).hom.app M) ≫
        (sfCartesianOpenPullPushAdjunction P.Ring c'.g).counit.app
          ((sfIntrinsicDerivedPullback P.Ring b.hom).obj M) =
      (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm).hom.app
          ((proEtaleConstantDerivedDirectImage c.g P.Ring).obj M) ≫
        (sfIntrinsicDerivedPullback P.Ring b.hom).map
          ((sfCartesianOpenPullPushAdjunction P.Ring c.g).counit.app M)) ∧
    (PurReindexing.finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
        (PurReindexing.finiteMateCartesian sqJ)).inv =
      sfIntrinsicDerivedOpenMate P.Ring g'.hom c'.i c.i b.hom sqJ.w ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (PurReindexing.finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
        (PurReindexing.finiteMateCartesian sqJ)).inv.app K =
      ((exceptionalOpenAdjunction c'.i P.Ring).homEquiv _ _).symm
        ((sfIntrinsicDerivedPullback P.Ring g'.hom).map
            ((exceptionalOpenAdjunction c.i P.Ring).unit.app K) ≫
          (sfIntrinsicDerivedSquarePullback P.Ring g'.hom c'.i c.i b.hom sqJ.w).hom.app
            ((sfIntrinsicDerivedOpen P.Ring c.i).obj K))) ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
        (sfIntrinsicDerivedOpen P.Ring c.i) (sfIntrinsicDerivedOpen P.Ring c'.i)
        (sfIntrinsicDerivedPullback P.Ring c.g)
        (proEtaleConstantDerivedDirectImage c.g P.Ring)
        (sfCartesianOpenPullPushAdjunction P.Ring c.g)
        (sfIntrinsicDerivedPullback P.Ring c'.g)
        (proEtaleConstantDerivedDirectImage c'.g P.Ring)
        (sfCartesianOpenPullPushAdjunction P.Ring c'.g)
        (sfIntrinsicDerivedPullback P.Ring g.hom)
        (sfIntrinsicDerivedPullback P.Ring g'.hom)
        (sfIntrinsicDerivedPullback P.Ring b.hom)
        (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm)
        (PurReindexing.finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
          (PurReindexing.finiteMateCartesian sqJ))).app K =
      (sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
          (PurReindexing.finiteMateCartesian sqP).flip).hom.app ((sfIntrinsicDerivedOpen P.Ring
      c.i).obj K) ≫
        (proEtaleConstantDerivedDirectImage c'.g P.Ring).map
          ((PurReindexing.finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
            (PurReindexing.finiteMateCartesian sqJ)).hom.app K)) ∧
    (∀ (F : Sheaf (Scheme.ProEt.topology c.Z)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring))) (V : Y'.ProEt),
      ((sfProperOpenFixedRestrictionIso P.Ring c'.g b.hom g.hom c.g
          (PurReindexing.finiteMateCartesian sqP).flip).hom.app F).hom.app (Opposite.op V) =
        F.obj.map ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : WeaklyEtale g.hom) (inferInstance : WeaklyEtale b.hom)
          (PurReindexing.finiteMateCartesian sqP).flip.toCommSq).app V).op)

/-- The identity clause for the same finite proper/open exchange.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
@[irreducible] def PurSemilinearFiniteIdentity (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} [ X.Over (Spec (.of P.field.k))]
  [ Y.Over (Spec (.of P.field.k))]
  [ LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [ QuasiCompact (X ↘ Spec (.of P.field.k))]
  [ IsSeparated (X ↘ Spec (.of P.field.k))]
  [ LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [ QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [ IsSeparated (Y ↘ Spec (.of P.field.k))]
{f : X ⟶ Y} [ f.IsOver (Spec (.of P.field.k))]
  [ IsSeparated f] [ LocallyOfFiniteType f] [ QuasiCompact f]
    (c : Compactification f)
    (sp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)),
    ordinaryH P.Coefficient c c (𝟙 Y) (𝟙 X) (𝟙 c.Z) sp sj =
      Functor.whiskerLeft (ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g)
          (PurReindexing.pullId P.Coefficient Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (PurReindexing.pullId P.Coefficient X).inv
          (ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g)

/-- The horizontal clause for the same finite proper/open exchange.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
@[irreducible] def PurSemilinearFiniteHorizontal (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} [ X.Over (Spec (.of P.field.k))]
  [ Y.Over (Spec (.of P.field.k))]
  [ LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [ QuasiCompact (X ↘ Spec (.of P.field.k))]
  [ IsSeparated (X ↘ Spec (.of P.field.k))]
  [ LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [ QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [ IsSeparated (Y ↘ Spec (.of P.field.k))]
{f : X ⟶ Y} [ f.IsOver (Spec (.of P.field.k))]
  [ IsSeparated f] [ LocallyOfFiniteType f] [ QuasiCompact f]
    {X' X'' Y' Y'' : Scheme.{u}}
    {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [X''.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X'' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X'' ↘ Spec (.of P.field.k))]
    [IsSeparated (X'' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [Y''.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y'' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y'' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y'' ↘ Spec (.of P.field.k))]
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y') [IsIso g] [IsIso h]
    (x : X' ⟶ X) (x' : X'' ⟶ X') (z : c'.Z ⟶ c.Z) (z' : c''.Z ⟶ c'.Z)
    (sp : IsPullback z c'.g c.g g) (sp' : IsPullback z' c''.g c'.g h)
    (sj : IsPullback x c'.i c.i z) (sj' : IsPullback x' c''.i c'.i z'),
    ordinaryH P.Coefficient c c'' (h ≫ g) (x' ≫ x) (z' ≫ z)
        (sp'.paste_horiz sp) (sj'.paste_horiz sj) =
      paste (ordinaryGComp P.Coefficient h g) (ordinaryGComp P.Coefficient x' x)
        (ordinaryH P.Coefficient c c' g x z sp sj)
        (ordinaryH P.Coefficient c' c'' h x' z' sp' sj')

/-- The vertical clause for the same finite proper/open exchange.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
@[irreducible] def PurSemilinearFiniteVertical (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} [ X.Over (Spec (.of P.field.k))]
  [ Y.Over (Spec (.of P.field.k))]
  [ LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [ QuasiCompact (X ↘ Spec (.of P.field.k))]
  [ IsSeparated (X ↘ Spec (.of P.field.k))]
  [ LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [ QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [ IsSeparated (Y ↘ Spec (.of P.field.k))]
{f : X ⟶ Y} [ f.IsOver (Spec (.of P.field.k))]
  [ IsSeparated f] [ LocallyOfFiniteType f] [ QuasiCompact f]
    {Z X' Y' Z' : Scheme.{u}} {h : Y ⟶ Z}
    {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [Z'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z' ↘ Spec (.of P.field.k))]
    [IsSeparated (Z' ↘ Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) [IsIso g]
    (A : CompositionBaseChange T T' x y g),
    Functor.whiskerRight (PurReindexing.composition P.Coefficient T) (ordinaryG P.Coefficient g) ≫
        ordinaryH P.Coefficient T.cfg T'.cfg g x A.s A.cfg_g A.cfg_i =
      Functor.whiskerLeft (ordinaryJ P.Coefficient T.cf.i ⋙ ordinaryR P.Coefficient T.cf.g)
          (ordinaryH P.Coefficient T.cg T'.cg g y A.t A.cg_g A.cg_i) ≫
        Functor.whiskerRight
          (ordinaryH P.Coefficient T.cf T'.cf y x A.d A.cf_g A.cf_i)
          (ordinaryJ P.Coefficient T'.cg.i ⋙ ordinaryR P.Coefficient T'.cg.g) ≫
        Functor.whiskerLeft (ordinaryG P.Coefficient x) (PurReindexing.composition P.Coefficient T')

/-- The coefficient clause for the same finite proper/open exchange.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
@[irreducible] def PurSemilinearFiniteCoefficient (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (h : m ≤ P.level)

    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (g : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z) [IsIso g]
    (sp : IsPullback z c'.g c.g g) (sj : IsPullback x c'.i c.i z)
    (K : DerivedCategory (Modules P.Coefficient X))
    (_hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X K),
    (PurReindexing.tensorQuotient P m hm h Y').map ((ordinaryH P.Coefficient c c' g x z sp sj).app
      K) ≫
        (PurCompactSupport.comparison (PurReindexing.constantChange (PurReindexing.quotient P m hm
      h)) c').app
          ((ordinaryG P.Coefficient x).obj K) ≫
        (ordinaryJ (PurReindexing.lower P m hm).Coefficient c'.i ⋙
          ordinaryR (PurReindexing.lower P m hm).Coefficient c'.g).map
          ((PurCompactSupport.scalarPull (PurReindexing.constantChange (PurReindexing.quotient P m
      hm h)) x).hom.app K) =
      (PurCompactSupport.scalarPull (PurReindexing.constantChange (PurReindexing.quotient P m hm
      h)) g).hom.app
          ((ordinaryJ P.Coefficient c.i ⋙ ordinaryR P.Coefficient c.g).obj K) ≫
        (ordinaryG (PurReindexing.lower P m hm).Coefficient g).map
          ((PurCompactSupport.comparison (PurReindexing.constantChange (PurReindexing.quotient P m
      hm h)) c).app K) ≫
        (ordinaryH (PurReindexing.lower P m hm).Coefficient c c' g x z sp sj).app
          ((PurReindexing.tensorQuotient P m hm h X).obj K)

end WeilConjectures
