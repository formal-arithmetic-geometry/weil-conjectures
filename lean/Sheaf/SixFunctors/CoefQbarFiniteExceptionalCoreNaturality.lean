/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData
import Sheaf.SixFunctors.RationalExceptionalIdentifications

/-! Naturality of the transported finite exceptional comparison component.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-core-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

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
  (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))

/-- The explicit component used to transport a finite exceptional comparison is natural.
The proof is the pasting of naturality for the rational exceptional comparison, the
finite Verdier comparison, the pullback comparison, and the common-stage duality map.
-/
theorem finite_exceptional_comparison_naturality
    (E : Index l Ω)
    (e : RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
      S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E))
    {M N : Stage l Ω Y E} (g : M ⟶ N) :
    (inclusion E).map ((finiteRight D l hl Ω X f c S E).map g) ≫
        (inclusion E).map (e.comparison.app N).hom ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op N)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op N)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op N))).inv).op =
    (inclusion E).map (e.comparison.app M).hom ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op ≫
      (inclusion E ⋙ BY.duality.dual.rightOp ⋙
        (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual).map g  := by sorry

end WeilConjectures.CoefQbarVerdier
