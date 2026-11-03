/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso

/-! # Classical adic comparison: a coefficient-complex step -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace RealSheaves

/-- The canonical reduction tower of compact direct image is the image of the
integral reduction tower, including its transitions and adjunction-unit projections.
Source: current blueprint d-real-cohom, Comparison with the classical description,
compact analogue; step 4, identification of the two reduction towers
(blueprint: lem-wf-classical-adic-compact-tower-comparison).

Proof: apply scalar-six for each O_E -> O_E/pi^(n+1) to compact direct image of K,
using the same compactification c. Integral bounded constructibility gives the
finite Tor amplitude needed for this comparison. Restriction from the finite
coefficient ring to O_E commutes with the proper direct image and exact open
extension: compare their adjunctions through the canonical coefficient-restriction
squares. Paste this restriction isomorphism with the scalar-six comparison to
obtain e_n. The coefficient-composition equation for scalar-six, after the two
restriction compositors, gives the displayed transition equation. Its scalar
adjunction-unit equation gives the projection equation. Both equations concern the
specified derived adjunctions and actual quotient maps; equality after reduction
alone is not used. These constructions include torsion K, zero K and the empty
scheme. No global sections, point tensor comparison or inverse limit is involved. -/
theorem classicalAdicCompactTowerComparison
    (D : Setup.{u, v}) (E : PadicAlgCl.FiniteIntermediateField D.l)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a)
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X))
    (hK : constantModelBoundedConstructible
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) X K) :
    let Y := Spec (.of D.k)
    let G := CondensedRing.rightDerivedLowerShriekOfCompactification
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c
    let M := G.obj K
    ∃ e : ∀ n : ℕ, AdicCompletion.integralLevel D.l (ULift.{u} E.val) Y M n ≅
        G.obj (AdicCompletion.integralLevel D.l (ULift.{u} E.val) X K n),
      (∀ n : ℕ, (e (n + 1)).hom ≫
          G.map (AdicCompletion.integralStep D.l (ULift.{u} E.val) X K n) =
        AdicCompletion.integralStep D.l (ULift.{u} E.val) Y M n ≫ (e n).hom) ∧
      (∀ n : ℕ,
        (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient D.l (ULift.{u} E.val) Y n)).unit.app M ≫ (e n).hom =
          G.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient D.l (ULift.{u} E.val) X n)).unit.app K)) := by
  sorry

end RealSheaves
