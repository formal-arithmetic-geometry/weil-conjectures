/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

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
open AlgebraicallyClosedCoefficients (Index Coefficient)
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
    Nonempty (FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S) := by sorry

end WeilConjectures.CoefQbarVerdier
