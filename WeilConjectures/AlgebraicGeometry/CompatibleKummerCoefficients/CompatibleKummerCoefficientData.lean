/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-! # Native coefficient data for the compatible-root Kummer boundary

Source: the compatible-root construction and native coefficient insertion in
Steps 2, 5, and 6 of `lem-pur-proetale-kummer-limit-boundary`.
(blueprint: def-pur-compatible-kummer-coefficient-data).

These are data types and explicit maps. No existence or exactness assertion is
postulated: an integral Kummer datum includes its normalization and exactness
proofs. The constant, generator, and root insertion use the actual sheaf,
monoidal unit, and scalar extension unit, respectively.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.CompatibleKummerCoefficients

variable (ell : ℕ) [Fact ell.Prime]

/-- The integral Kummer limit, with both maps specified on every finite projection.
Source: compatible-root Kummer boundary, Steps 2 and 5
(blueprint: def-pur-compatible-kummer-coefficient-data). -/
structure IntegralKummer (T : Scheme.{u}) where
  level : ∀ n : ℕ, (tateModuleLevel T ell (n + 1)).X ≅
    Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))
  level_normalized : ∀ n : ℕ,
    (level n).inv = (rootComparison T (ell ^ (n + 1))).inv ≫
      (λ_ (rootsOfUnitySheaf T (ell ^ (n + 1)))).inv ≫
      η[condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) T] ▷ _
  inclusion : (tateModule T ell).X ⟶ limit (SpTowerClasses.powerUnits ell T)
  inclusion_normalized : ∀ n : ℕ,
    inclusion ≫ limit.π (SpTowerClasses.powerUnits ell T) (op n) =
      (limit.π (tateModuleSystem T ell) (op (n + 1))).hom ≫ (level n).hom ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  projection : limit (SpTowerClasses.powerUnits ell T) ⟶ Scheme.proEtaleUnitsSheaf T
  projection_normalized : projection =
    limit.π (SpTowerClasses.powerUnits ell T) (op 0) ≫ Scheme.proEtaleUnitsPower T ell
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The integral constant sheaf on the pro-etale site.
Source: compatible-root Kummer boundary, Step 6
(blueprint: def-pur-compatible-kummer-coefficient-data). -/
abbrev integralConstant (X : Scheme.{u}) :=
  (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The coefficient unit sends the integral section one to the ring section one.
Source: compatible-root Kummer boundary, Step 6
(blueprint: def-pur-compatible-kummer-coefficient-data). -/
def generator (c : Coefficient ell) (X : Scheme.{u}) :
    integralConstant X ⟶ condensedRingObj (c.obj ell) X :=
  (Functor.Monoidal.εIso (constantSheaf (ProEt.topology X) Ab.{u + 1})).inv ≫ η

/-- The actual scalar insertion into the shifted Tate line.
Source: compatible-root Kummer boundary, Step 5
(blueprint: def-pur-compatible-kummer-coefficient-data). -/
def rootInsertion (c : Coefficient ell) (T : Scheme.{u}) :
    (tateModule T ell).X ⟶ (c.line ell T 1).X :=
  (Mod.extendUnit (coefficientMap (c.integralMap ell) T) (tateModule T ell)).hom ≫
    (λ_ (c.firstLine ell T)).inv.hom

end AlgebraicGeometry.ProEtale.CompatibleKummerCoefficients
