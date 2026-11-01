/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.RationalOperations.RationalExceptionalIdentifications
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteExceptionalCoreNaturality

/-! Core finite exceptional comparison data.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

abbrev specifiedExceptionalFormulaCore (BX : Duality D l hl Ω X)
    (BY : Duality D l hl Ω Y) :=
  BY.duality.dual.rightOp ⋙ (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual

/-- The finite comparison data, before imposing scalar compatibility.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-core) -/
structure FiniteExceptionalFormulaCore
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    where
  finite (E : Index l Ω) :
    RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
      S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E)
  comparison (E : Index l Ω) :
    finiteRight D l hl Ω X f c S E ⋙ inclusion (Y := X) E ≅
      inclusion (Y := Y) E ⋙ specifiedExceptionalFormulaCore D l hl Ω X f BX BY
  normalized (E : Index l Ω) (M : Stage l Ω Y E) :
    (inclusion E).map ((finite E).comparison.hom.app M) ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op =
    (comparison E).hom.app M

/-- The core data exist by the finite rational exceptional comparison construction.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-core)

Proof: choose the normalized rational exceptional identifications at each finite field;
transport their components through the prescribed inclusion and duality comparisons.
Naturality is checked by the naturality of the three comparison isomorphisms and the
pullback object comparison. The resulting component formula is the displayed normalized
identity. Scalar compatibility is deliberately omitted and supplied separately. -/
theorem finite_exceptional_formula_core
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    Nonempty (FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S) := by
  classical
  let finite : ∀ E : Index l Ω,
      RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
        S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
        (BX.finite.datum E) (BY.finite.datum E) := by
    intro E
    let h := RationalOperations.rationalExceptional_identifications
      D l hl X (AuxiliaryClosure.{u} l) c S (fieldStage l Ω E) (fieldStage l Ω E)
      (coefficientInclusion l Ω E E le_rfl)
      (BX.finite.omega E) (BY.finite.omega E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E) (BX.finite.datum E) (BY.finite.datum E)
      (BX.finite.hom E) (BY.finite.hom E) (BX.finite.hom E) (BY.finite.hom E)
      (BX.finite.scalar E E le_rfl) (BY.finite.scalar E E le_rfl)
      (BX.finite.normalized E E le_rfl) (BY.finite.normalized E E le_rfl)
    exact RationalOperations.exceptionalIdentificationOfIso
      D l hl X (AuxiliaryClosure.{u} l) c S (fieldStage l Ω E)
      (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E) (Classical.choose h)
  let comparison : ∀ E : Index l Ω,
      finiteRight D l hl Ω X f c S E ⋙ inclusion (Y := X) E ≅
        inclusion (Y := Y) E ⋙ specifiedExceptionalFormulaCore D l hl Ω X f BX BY := by
    intro E
    let e := finite E
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · let p := (CoefQbarPullback D l hl Ω f).mapIso ((BY.comparison E).symm.app (op M)) ≪≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).symm
      exact (inclusion E).mapIso (e.comparison.app M) ≪≫
        (BX.comparison E).app (op ((@rationalDerivedPullback l _
          (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≪≫
          BX.duality.dual.mapIso p.op
    · intro M N g
      simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map,
        Functor.comp_obj, Category.assoc]
      exact finite_exceptional_comparison_naturality D l hl Ω X f BX BY c S E e g
  refine ⟨{ finite := finite, comparison := comparison, normalized := ?_ }⟩
  intro E M
  rfl

end WeilConjectures.CoefQbarVerdier
