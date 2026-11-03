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
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso

/-! # Classical adic comparison: a coefficient-complex step -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace RealSheaves

/-- Scalar-six comparisons after passage to the actual coefficient complexes.
Source: current blueprint d-real-cohom, Comparison with the classical description,
coefficient comparisons and their compact analogues; step 2 of the classical-adic node
(blueprint: lem-wf-classical-adic-scalar-comparisons).

Proof: the integral criterion puts K in Dctf. On the algebraically closed base of
characteristic different from l, apply the scalar-six direct-image and compact-support
comparisons to O_E -> E -> Qbar and to each positive quotient. Transport the source
integral presentation by integralIso, and the finite presentation by the normalized
quotient ring isomorphism. Use exactly the supplied compactification for lower shriek.
On Spec k, terminal sections are exact and are evaluation at the final object. Ringed
point evaluation commutes with scalar tensor: evaluate a flat-term K-flat model of the
input and either the flat rational coefficient module or the two-term Koszul model of
the positive quotient. Evaluation preserves the quasi-isomorphisms and the tensor
comparison, so localization gives the displayed isomorphisms over the actual section
rings, with their specified coefficient maps. The same argument applies to Ra_* K
and Ra_! K; no inverse limit is used here. Naturality and scalar composition identify
the composite integral-to-Qbar map with the one displayed. Positive exponents include
n=0, and torsion K, zero K and the empty scheme require no extra hypothesis. -/
theorem classicalAdicScalarComparisons
    (D : Setup.{u, v}) (E : PadicAlgCl.FiniteIntermediateField D.l)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a)
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X))
    (hK : constantModelBoundedConstructible
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) X K) :
    (
      let φ := CoefficientHomComparison.integralToField D.l E ≫
              Profinite.padicSubfieldRingObjToPadicAlgCl D.l E
      let T := (Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor
      letI := ModuleCat.extendScalars_preservesKFlatQuasiIso (MonObj.Γ.map φ)
      let U := (ModuleCat.extendScalars (MonObj.Γ.map φ)).leftDerivedFunctor
      Nonempty (U.obj ((CondensedRing.condensedRingOrdinaryCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) a).obj K) ≅
        (CondensedRing.condensedRingOrdinaryCoefficientComplex
          (Profinite.padicAlgClRingObj D.l) a).obj (T.obj K)) ∧
      Nonempty (U.obj ((CondensedRing.condensedRingCompactCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c).obj K) ≅
        (CondensedRing.condensedRingCompactCoefficientComplex
          (Profinite.padicAlgClRingObj D.l) c).obj (T.obj K))) ∧
    (∀ n : ℕ,
      let φ := DerivedNakayama.reductionRing D.l (ULift.{u} E.val) (n + 1)
      let T := (Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor
      letI := ModuleCat.extendScalars_preservesKFlatQuasiIso (MonObj.Γ.map φ)
      let U := (ModuleCat.extendScalars (MonObj.Γ.map φ)).leftDerivedFunctor
      Nonempty (U.obj ((CondensedRing.condensedRingOrdinaryCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) a).obj K) ≅
        (CondensedRing.condensedRingOrdinaryCoefficientComplex
          (DerivedNakayama.quotientRing D.l (ULift.{u} E.val) (n + 1)) a).obj (T.obj K)) ∧
      Nonempty (U.obj ((CondensedRing.condensedRingCompactCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c).obj K) ≅
        (CondensedRing.condensedRingCompactCoefficientComplex
          (DerivedNakayama.quotientRing D.l (ULift.{u} E.val) (n + 1)) c).obj (T.obj K))) := by
  sorry

end RealSheaves
