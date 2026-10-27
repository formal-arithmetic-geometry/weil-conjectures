/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData
import Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar

/-! # Finite exceptional comparisons for specified Verdier dualities

Source: thm-coef-qbar-verdier, retained proof step 9. This file concerns only
finite coefficient restrictions and their scalar squares, before gluing.
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

/-- The specified duality-pullback-duality functor, without an exceptional adjunction.
Source: thm-coef-qbar-verdier, proof step 9
(blueprint: lem-coef-qbar-finite-exceptional-formula). -/
abbrev specifiedExceptionalFormula (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y) :=
  BY.duality.dual.rightOp ⋙ (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual

/-- Local comparison data, containing no functor or adjunction obtained by descent.
All comparison functors have a single finite coefficient category as their source.
Source: thm-coef-qbar-verdier, proof step 9
(blueprint: lem-coef-qbar-finite-exceptional-formula). -/
structure FiniteExceptionalFormula (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    where
  finite (E : Index l Ω) :
    RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
      S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E)
  comparison (E : Index l Ω) :
    finiteRight D l hl Ω X f c S E ⋙ inclusion (Y := X) E ≅
      inclusion (Y := Y) E ⋙ specifiedExceptionalFormula D l hl Ω X f BX BY
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
  scalar (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E) :
    (inclusion L).map ((finiteRightScalar D l hl Ω X f c S E L h).hom.app M) ≫
      (comparison L).hom.app ((transition l Ω Y E L h).obj M) =
    (inclusionTransition l Ω X E L h).hom.app
        ((finiteRight D l hl Ω X f c S E).obj M) ≫
      (comparison E).hom.app M ≫
      (specifiedExceptionalFormula D l hl Ω X f BX BY).map
        ((inclusionTransition l Ω Y E L h).inv.app M)

/-- The finite exceptional formula with its normalized scalar square, for a fixed
coefficient system and the specified finite-origin dualities.
Source: thm-coef-qbar-verdier, retained proof step 9
(blueprint: lem-coef-qbar-finite-exceptional-formula).

Proof: apply rationalExceptional_identifications to the given finite dualizing
presentations, Hom identifications and normalized Extension data of BX and BY.
Use the adjunction transpose of the evaluation-defined integral exceptional
comparison to choose its component at each field. The evaluation and counit
normalizations fix that transpose, so the comparisons obtained for two different
scalar extensions have the same component at their common endpoint. The scalar
identity in rationalExceptional_identifications therefore holds for this one
family. Rationalize the integral comparisons and retain their transported
adjunctions to obtain finite. Whisker the comparison at E by inclusion, then by
BX.comparison, inverse BY.comparison and the inverse pullbackInclusion. This is
comparison E, and its component formula is normalized. To check scalar, expand
this composite. The finite exceptional scalar identity replaces the first two
factors. The BX and BY duality scalar squares replace the duality factors, and
the published pullback scalar square replaces its pullback factor. Naturality
moves these comparisons past each other; inverse pairs cancel. The result is
exactly inclusionTransition on X followed by comparison E followed by the
formula functor applied to inverse inclusionTransition on Y. Every equation
uses the actual units and counits; repeated fields use their identity scalar
comparisons and the argument also applies to zero objects. No gluing of functors
on the pair category is part of this statement. -/
theorem finite_exceptional_formula (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    Nonempty (FiniteExceptionalFormula D l hl Ω X f BX BY c S) := by
  obtain ⟨t⟩ := finite_exceptional_formula_core D l hl Ω X f BX BY c S
  let z : FiniteExceptionalFormula D l hl Ω X f BX BY c S :=
    { finite := t.finite
      comparison := t.comparison
      normalized := t.normalized
      scalar := finite_exceptional_formula_scalar D l hl Ω X f BX BY c S t }
  exact ⟨z⟩

end WeilConjectures.CoefQbarVerdier
