/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic

/-! # Normalized quotient error helper

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The canonical middle chain map supplied by the normalized quotient model.
Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
(blueprint: lem-sp-normalized-quotient-error-map-middle)

Proof: construct the map degreewise from the universal quotient presentation.
The quotient factorization, tensor transport, and shift compatibility are checked
sectionwise and then reassembled by sheafification.
-/
theorem exists_errorComparisonMiddleMap (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅
      principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1))
    (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    (M : QuotientModel R t B a A P m) :
    ∃ α : shiftedTwist R t M.V ⟶ middle R t m (representative R B a P),
      ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
      (x : ((restrictedLevel R B a P (m + n)).X (i + 1)).val.obj U),
      ((((α).f i).app (op n)).val.app U
        (((CochainComplex.shiftFunctorObjXIso ((towerView R M.V).obj (op n))
          (1 : ℤ) i (i + 1) rfl).inv).val.app U
          (((M.ν n).inv.f (i + 1)).val.app U
            (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
              ((level B P (m + n)).X (i + 1)) U 1 x)))) =
        (minusGenerator R t m (restrictedLevel R B a P (m + n)) i).val.app U
          (((endoPow ((complexScalar R t).app (restrictedLevel R B a P (m + n))) n).f
            (i + 1)).val.app U x) := by sorry

end SheafOfModules.NormalizedQuotientError
