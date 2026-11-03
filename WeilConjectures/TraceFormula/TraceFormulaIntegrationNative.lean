/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.FiniteRingTrace.TraceFormulaIntegrationNativeInputs
public import WeilConjectures.TraceFormula.FiniteRingTrace.TraceFormulaFiniteCoefficientPrimary
public import WeilConjectures.NumberTheory.Padics.Extension

/-! # Integration with the current discrete condensed finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-d-integral/def-trf-integration.md
(blueprint: def-trf-integration). The proper comparison is the inverse of the canonical
map from compact supports to ordinary direct image. The exceptional datum below is
exactly the datum selected by FiniteRingTrace.exceptional, including its counit.
The coefficient scalar is the degree-zero endomorphism evaluated at the unit section.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

section FiniteRing



variable (A : Type) [CommRing A] [Finite A]

/-- The actual regular coefficient module in degree zero.
Source: def-trf-integration (blueprint: def-trf-integration). -/
abbrev traceFormulaIntegrationConstant (Y : Scheme.{u}) : FiniteRingTrace.Ambient A Y :=
  constantCoefficientObject (FiniteRingTrace.coefficient A) Y

/-- The same native ambient derived category used by the current dualizing-complex node.
Source: def-trf-integration (blueprint: def-trf-integration). -/
abbrev traceFormulaIntegrationFixed (Y : Scheme.{u}) := FiniteRingTrace.Ambient A Y

omit [Finite A] in
/-- The coefficient unit is bounded constructible of finite Tor amplitude.
Source: the unit clause of def-trf-integration (blueprint: def-trf-integration).

Proof: the constant object A_Y is the regular coefficient module placed in degree zero.
It is constructible by lem-weil-constant-coefficient-objects-constructible, and it has
Tor amplitude [0,0] because A_Y tensored with M is M. This is the membership statement
`constantCoefficientObject_mem` for the discrete coefficient `FiniteRingTrace.coefficient A`. -/
theorem traceFormulaIntegrationConstantOrigin (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (constantModelBoundedConstructible (FiniteRingTrace.coefficient A) Y ⊓
      DerivedCategory.finiteTorAmplitude _) (traceFormulaIntegrationConstant A Y) := by
  sorry

/-- The coefficient unit as an object of the current constructible finite-Tor subcategory.
Source: def-trf-integration (blueprint: def-trf-integration). -/
def traceFormulaIntegrationUnit (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y] :
    FiniteRingTrace.Ctf A Y :=
  ⟨traceFormulaIntegrationConstant A Y, traceFormulaIntegrationConstantOrigin A Y⟩

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
  (Y : Over (Spec (.of D.k))) [IsProper Y.hom]

/-- Exceptional admissibility is realized by the current constructible adjunction itself.
Source: def-trf-admissibility (blueprint: def-trf-admissibility). -/
abbrev traceFormulaIntegrationAdmissible :=
  FiniteRingTrace.integrationExceptionalData A D ell hell hA Y

/-- The selected right adjoint applied to A_s is definitionally the recorded dualizing
complex. Source: def-trf-dualizing-complex (blueprint: def-trf-dualizing-complex). -/
def traceFormulaIntegrationDualizingIso :
    ((FiniteRingTrace.exceptional A D ell hell hA Y).obj
      (traceFormulaIntegrationUnit A (Spec (.of D.k)))).obj ≅
        FiniteRingTrace.dualizingComplex A D ell hell hA Y := Iso.refl _

/-- The ordinary direct image is identified with the left functor of the very same
constructible adjunction, by the inverse of its normalized support comparison.
Source: P_a in def-trf-integration (blueprint: def-trf-integration). -/
def traceFormulaIntegrationProperIso (K : FiniteRingTrace.Ctf A Y.left) :
    ((lowerStar (FiniteRingTrace.coefficient A) Y.hom).rightDerivedFunctor).obj K.obj ≅
      ((FiniteRingTrace.integrationLower A D ell hell hA Y).obj K).obj := by
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  letI : IsProper (Over.mkIdTerminal.from Y).left := by
    rw [Over.mkIdTerminal_from_left]
    infer_instance
  let c := compactificationOverField (Over.mkIdTerminal.from Y)
  letI := FiniteRingTrace.supportToOrdinary_isIso A c K.obj
  exact eqToIso (congrArg
      (fun f ↦ ((lowerStar (FiniteRingTrace.coefficient A) f).rightDerivedFunctor).obj K.obj)
      (Over.mkIdTerminal_from_left Y).symm) ≪≫
    (asIso (FiniteRingTrace.supportToOrdinary A c K.obj)).symm ≪≫
    (eqToIso (congrArg (fun F ↦ F.obj K)
      (traceFormulaIntegrationAdmissible A D ell hell hA Y).lower_eq)).symm

/-- Compose the ordinary adjunction unit, proper comparison, Ra_! tau, and the current
exceptional counit at A_s. Every ambient tau is admitted since Ctf is full.
Source: the displayed integration composite (blueprint: def-trf-integration). -/
def traceFormulaIntegrationEndomorphism
    (tau : traceFormulaIntegrationConstant A Y.left ⟶
      FiniteRingTrace.dualizingComplex A D ell hell hA Y) :
    End (traceFormulaIntegrationConstant A (Spec (.of D.k))) := by
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  let d := traceFormulaIntegrationAdmissible A D ell hell hA Y
  let U := traceFormulaIntegrationUnit A Y.left
  let V := traceFormulaIntegrationUnit A (Spec (.of D.k))
  let t : U ⟶ d.right.obj V :=
    ⟨tau ≫ (traceFormulaIntegrationDualizingIso A D ell hell hA Y).inv⟩
  exact (derivedUpperStarLowerStarAdjunction (FiniteRingTrace.coefficient A) Y.hom).unit.app
      V.obj ≫
    ((lowerStar (FiniteRingTrace.coefficient A) Y.hom).rightDerivedFunctor).map
      (leftDerivedUpperStarUnitIso (FiniteRingTrace.coefficient A) Y.hom).hom ≫
    (traceFormulaIntegrationProperIso A D ell hell hA Y U).hom ≫
    (d.lower.map t).hom ≫ (d.adjunction.counit.app V).hom

/-- Read H^0(v)(1): fully faithful single-in-degree-zero identifies v with its module
endomorphism; evaluate on the regular module unit, descend the point equivalence, and
then evaluate the discrete condensed coefficient section at the singleton.
Source: the final scalar clause of def-trf-integration (blueprint: def-trf-integration). -/
def traceFormulaIntegrationScalar
    (v : End (traceFormulaIntegrationConstant A (Spec (.of D.k)))) : A := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let F := upperStarFromPoint (Spec (.of D.k))
  let m := (DerivedCategory.singleFunctor _ 0).preimage v
  let one : 𝟙_ _ ⟶ condensedRingObj (FiniteRingTrace.coefficient A) (Spec (.of D.k)) :=
    MonObj.one
  let σ : F.obj (𝟙_ _) ⟶ F.obj (FiniteRingTrace.coefficient A) :=
    (Functor.Monoidal.εIso F).inv ≫ one ≫ m.hom
  let sec := F.preimage σ
  exact (Sheaf.unitHomEval (Profinite.of PUnit.{u + 1}) sec).down PUnit.unit

end FiniteRing

/-- Integration is the scalar of the specified unit/proper-comparison/map/counit
composite at A=A_E,n, with the current finite-ring dualizing complex.
The primary witness is supplied by the quotient coefficient theorem.
Source: def-trf-integration (blueprint: def-trf-integration). -/
def traceFormulaIntegration (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : IntermediateField (Padic ell) (PadicAlgCl ell))
    [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Over (Spec (.of D.k))) [IsProper Y.hom] :
    let A := Padic.coefficientExtensionRing ell E n
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    let hA := FiniteRingTrace.coefficientExtensionRing_primary ell E n hn
    (traceFormulaIntegrationConstant A Y.left ⟶
      FiniteRingTrace.dualizingComplex A D ell hell hA Y) → A := by
  let A := Padic.coefficientExtensionRing ell E n
  letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  let hA := FiniteRingTrace.coefficientExtensionRing_primary ell E n hn
  exact fun tau ↦ traceFormulaIntegrationScalar A D
    (traceFormulaIntegrationEndomorphism A D ell hell hA Y tau)

end WeilConjectures
