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

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion

/-! # Completeness of compact direct image of an integral lattice -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace RealSheaves

/-- Compact direct image of an integral constructible complex is derived complete.
Source: current blueprint d-real-cohom, Comparison with the classical description,
compact analogue via ctf stability and the integral criterion
(blueprint: lem-wf-classical-adic-compact-output-complete).

Proof: integral bounded constructibility gives finite Tor amplitude by the integral
criterion. The spectral integral coefficient is admissible via integralIso. Apply
compactification ctf stability to the supplied proper/open compactification. Its
output on Spec k is bounded constructible, so the integral criterion there gives
canonical derived completeness. The characteristic hypotheses follow from the
finite-field datum and are unchanged by passage to its algebraic closure. -/
theorem classicalAdicCompactOutputComplete
    (D : Setup.{u, v}) (E : PadicAlgCl.FiniteIntermediateField D.l)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a)
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X))
    (hK : constantModelBoundedConstructible
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) X K) :
    IsDerivedComplete D.l (ULift.{u} E.val) (Spec (.of D.k))
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c).obj K) := by
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans D.ringChar_eq
  have : Fact (ringChar D.k).Prime := ⟨by rw [hchar]; exact D.p_prime⟩
  have : Fact (ringChar D.k ≠ D.l) := ⟨by rw [hchar]; exact Ne.symm D.l_ne_p⟩
  let : X.Over (Spec (.of D.k)) := ⟨a⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := ⟨⟩
  have ha : (X ↘ Spec (.of D.k)) = a := rfl
  have : LocallyOfFiniteType (X ↘ Spec (.of D.k)) := by rw [ha]; infer_instance
  have : QuasiCompact (X ↘ Spec (.of D.k)) := by rw [ha]; infer_instance
  have : IsSeparated (X ↘ Spec (.of D.k)) := by rw [ha]; infer_instance
  have : a.IsOver (Spec (.of D.k)) := ⟨by simpa using ha.symm⟩
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : QuasiCompact c.i := quasiCompact_of_compactSpace c.i
  let O := DerivedNakayama.integerRing D.l (ULift.{u} E.val)
  have hO : IsLocalizingAdmissibleCoefficient D.l O := by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨?_⟩⟩))))
    let e := CoefficientHomComparison.integralIso.{u} D.l E
    exact
      { hom := Mon.ofHom e.inv
        inv := Mon.ofHom e.hom
        hom_inv_id := by apply Mon.Hom.ext; exact e.inv_hom_id
        inv_hom_id := by apply Mon.Hom.ext; exact e.hom_inv_id }
  have hctf := ((condensed_integral_criterion D.l (ULift.{u} E.val) X K).out 0 3).mp hK
  have houtput := (CondensedRing.compactification_localizing O D.l D.k a
    ⟨⟨c, inferInstance⟩⟩ hO).2.2.2 K hctf
  have hcomplete := ((condensed_integral_criterion D.l (ULift.{u} E.val) (Spec (.of D.k))
    ((CondensedRing.rightDerivedLowerShriekOfCompactification O c).obj K)).out 0 1).mp
      houtput.1
  exact hcomplete.1

end RealSheaves
