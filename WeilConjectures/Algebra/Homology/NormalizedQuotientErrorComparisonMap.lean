/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic
import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorMiddleMap
import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorMiddleMapZero

/-! # Comparisons for the normalized quotient error cone

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The unnormalized comparison with the error cocone, including its prescribed
components. Source: blueprint sk-lem-sp-tower proof, paragraph 2
(blueprint: lem-sp-normalized-quotient-error-map). -/
structure ErrorComparisonMap (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    (M : QuotientModel R t B a A P m) where
  /-- The error comparison before inverting normalization. -/
  j : shiftedTwist R t M.V ⟶ CochainComplex.mappingCocone M.ε
  /-- At level m+n this is the degree-minus-one generator multiplied by t^n. -/
  j_generator : ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
    (x : ((restrictedLevel R B a P (m + n)).X (i + 1)).val.obj U),
    ((((j ≫ CochainComplex.mappingCocone.fst M.ε).f i).app (op n)).val.app U
      (((CochainComplex.shiftFunctorObjXIso ((towerView R M.V).obj (op n))
        (1 : ℤ) i (i + 1) rfl).inv).val.app U
        (((M.ν n).inv.f (i + 1)).val.app U
          (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
            ((level B P (m + n)).X (i + 1)) U 1 x)))) =
    (minusGenerator R t m (restrictedLevel R B a P (m + n)) i).val.app U
      (((endoPow ((complexScalar R t).app (restrictedLevel R B a P (m + n))) n).f
        (i + 1)).val.app U x)
  /-- Its component in the quotient target summand is zero. -/
  j_target : ∀ (i : ℤ), j.f i ≫
    (CochainComplex.mappingCocone.snd M.ε).v i (i - 1) (by omega) = 0


/-- The prescribed Koszul error map, without a quasi-isomorphism assertion.
Source: blueprint sk-lem-sp-tower proof, paragraph 2, coefficient generator formula
(blueprint: lem-sp-normalized-quotient-error-map).

Proof: at level m+n, multiplication by t^n takes a t^(m+1)-multiple to a
t^(m+n+1)-multiple, hence factors through the lower quotient. Construct this
factorization on sectionwise principal quotients and sheafify it. Local
surjectivity of the structural quotient maps forces every system transition to
be the canonical quotient reduction, by compatibility with a. Tensor the map over
B_(m+n) with P_(m+n), and use the balanced isomorphism M.mu and the specified
Koszul generator inclusion. This defines the degree-i component from V_n^(i+1)
to the minus-one Koszul summand. The differential on that summand is t^(m+1);
its composite with t^n is zero, and the second-factor differential has sign -1,
which agrees with the shift. Thus these components are a chain map alpha from
the shifted V tower to the middle tower. The augmentation has zero composite
with alpha, by its two summand formulas. The cocone lift of alpha with zero
homotopy gives j and its zero target summand. For successor transitions the two
composites have scalar factors t^(n+1) and t^n*t respectively; the quotient
maps and P transitions are the original ones. They agree strictly, and iterating
gives a map of whole towers. For arbitrary M the augmentation is degreewise
epimorphic, since the coefficient quotient projection is locally surjective;
its naturality therefore forces the M.nu transport of these same transitions.
Transport by M.nu gives exactly the recorded
unit-generator formula. This construction uses no regularity or K-flatness. -/
theorem exists_errorComparisonMap (R : Sheaf J CommRingCat.{r})
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
    Nonempty (ErrorComparisonMap R t B a A P m M) := by
  classical
  obtain ⟨α, hα⟩ := exists_errorComparisonMiddleMap R t B a q hq A P m M
  have hzero : α ≫ M.ε = 0 :=
    errorComparisonMiddleMap_comp_epsilon_zero R t B a q hq A P m M α hα
  let j := CochainComplex.mappingCocone.lift M.ε α 0 (by simpa [hzero])
  refine ⟨{ j := j, j_generator := ?_, j_target := ?_ }⟩
  · intro n i U x
    simpa [j] using hα n i U x
  · intro i
    simpa [j] using
      (CochainComplex.mappingCocone.lift_f_snd_v M.ε α 0
        i (i - 1) (by omega))

end SheafOfModules.NormalizedQuotientError
