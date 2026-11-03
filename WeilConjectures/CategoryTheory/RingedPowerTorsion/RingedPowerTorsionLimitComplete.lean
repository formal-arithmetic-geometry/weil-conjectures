/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosInterchange
import WeilConjectures.CategoryTheory.RingedPowerTorsion.NilpotentKoszulRowRetraction
import WeilConjectures.CategoryTheory.RingedPowerTorsion.KoszulQuotientCompletionComparison
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import Mathlib.Algebra.GroupWithZero.Action.Units

/-! # Canonical completeness of limits of power-torsion module sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 3.4,
Proposition 3.5.1, Definition 3.5.2 and Lemma 3.5.7, regular principal refinement
(blueprint: lem-sp-ringed-power-torsion-limit-complete).

Positive quotient level j is indexed by j-1. All limits use the existing strict
Roos functor and its actual projections. Completion uses the existing universal
principal quotient model, including its prescribed unit, rather than an arbitrary map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.RingedPowerTorsion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalar_pow_apply (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (M : ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (n : ℕ)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) n).val.app V x =
      (show R.obj.obj V from (@id (R.obj.obj V) (t.val V))) ^ n • x := by
  induction n with
  | zero => change x = ((@id (R.obj.obj V) (t.val V))) ^ 0 • x; simp
  | succ n ih =>
    change ((@id (R.obj.obj V) (t.val V))) •
      ((endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) n).val.app V x) = _
    rw [ih, smul_smul, pow_succ']

omit [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem multiplication_pow_apply (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) (n : ℕ)
    (V : Cᵒᵖ) (x : R.obj.obj V) :
    (endoPow (globalSectionMultiplication R t) n).val.app V x =
      x * (@id (R.obj.obj V) (t.val V)) ^ n := by
  induction n with
  | zero => change x = x * ((@id (R.obj.obj V) (t.val V))) ^ 0; simp
  | succ n ih =>
    change (show R.obj.obj V from
      (endoPow (globalSectionMultiplication R t) n).val.app V x) * (@id (R.obj.obj V) (t.val V)) = _
    rw [ih, pow_succ, mul_assoc]

omit [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem nilpotent_parameter_change (t s unit : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    [hu : IsIso (globalSectionMultiplication R unit)] (e n : ℕ)
    (h : globalSectionMultiplication R t = globalSectionMultiplication R unit ≫
      endoPow (globalSectionMultiplication R s) e)
    (M : ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (hn : endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) n = 0) :
    endoPow ((SheafOfModules.RegularQuotientCone.scalar R s).app M) (e * n) = 0 := by
  ext V x
  rw [scalar_pow_apply]
  change ((@id (R.obj.obj V) (s.val V))) ^ (e * n) • x = 0
  have ht : (@id (R.obj.obj V) (t.val V)) =
      (@id (R.obj.obj V) (unit.val V)) * (@id (R.obj.obj V) (s.val V)) ^ e := by
    have he := congrArg (fun f ↦ f.val.app V (1 : R.obj.obj V)) h
    change (1 : R.obj.obj V) * (@id (R.obj.obj V) (t.val V)) =
      (endoPow (globalSectionMultiplication R s) e).val.app V
        (1 * (@id (R.obj.obj V) (unit.val V))) at he
    simpa only [multiplication_pow_apply, one_mul] using he
  have hunit : IsUnit (show R.obj.obj V from (@id (R.obj.obj V) (unit.val V))) := by
    let g := inv (globalSectionMultiplication R unit)
    have hg := congrArg (fun f ↦ f.val.app V (1 : R.obj.obj V))
      (IsIso.inv_hom_id (globalSectionMultiplication R unit))
    apply isUnit_iff_exists_inv.mpr
    refine ⟨(@id (R.obj.obj V) (g.val.app V (1 : R.obj.obj V))), ?_⟩
    change (@id (R.obj.obj V) (unit.val V)) *
      (@id (R.obj.obj V) (g.val.app V (1 : R.obj.obj V))) = 1
    change (@id (R.obj.obj V) (g.val.app V (1 : R.obj.obj V))) *
      (@id (R.obj.obj V) (unit.val V)) = 1 at hg
    exact (mul_comm _ _).trans hg
  have hz := congrArg (fun f ↦ f.val.app V x) hn
  change (endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) n).val.app V x
    = 0 at hz
  rw [scalar_pow_apply, ht, mul_pow, ← pow_mul, mul_smul] at hz
  exact (hunit.pow n).smul_eq_zero.mp hz

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

set_option maxHeartbeats 1600000 in
-- Elaborating all representative comparison squares exceeds the default heartbeat budget.
/-- The actual quotient completion unit of a limit of termwise power-torsion rows is
invertible. The double-limit comparison is natural on every strict double system and
has the four product-coordinate formulas for the sign (-1)^(pq). On the Koszul double
system it intertwines the completion unit with the limit of the actual row units.
Each torsion row has its own cutoff, a compatible splitting on that tail, and an
inverse to its actual row unit. The final clause uses any other regular parameter
whose positive power differs from t by an invertible global section.

Source: Bhatt--Scholze, Section 3.4, Proposition 3.5.1(1)--(2), Definition 3.5.2,
and Lemma 3.5.7 proof (blueprint: lem-sp-ringed-power-torsion-limit-complete).

Proof plan, following the node's eight steps:
1. By lem-weil-strict-roos-comparison use the fixed Cone(1-s)[-1] model, with its
   actual evaluations and augmentation (gamma,0). Exact countable products suffice.
2. By lem-pur-derived-complete-koszul-reconstruction and
   lem-cbc-signed-koszul-finite-coordinates, the raw U_n tensor K_j computes derived
   quotient reduction with its unit. Resolve only to compare with the quotient:
   no K-flat replacement is asserted to retain termwise torsion.
3. In row n, cut off at r_n using lem-sp-roos-finite-tail-cone. The cross differential
   vanishes, and the degree sign identifies the two summands with U_n and U_n[1].
   Transitions are (1,t), and the actual unit includes the first summand.
4. The shifted product shift S satisfies S^r_n=0. Its finite geometric series inverts
   1-S. The constant summand is split by (ev,1-S), with inverse x_0=u,
   x_(j+1)=x_j-y_j. Thus the row retraction is inverse to this same row unit.
5. Distribute the finite free K_j across products and the cone. The full tensor
   inclusion and Roos-coordinate equations fix this comparison, including its signs.
   On every K-flat resolution a:P→Roos(U), invert the actual Koszul-to-quotient map
   after localization, compose with the Koszul image of a and this distribution.
   The comparison e is required to equal that composite after M.counit.app P;
   this fixes e independently of the completion unit and independently of a.
6. Transpose the two product indices and give the doubly shifted component a minus
   sign. The two differential squares give (-1)^((p+1)q)=(-1)^q(-1)^(pq) and
   (-1)^(p(q+1))=(-1)^p(-1)^(pq). These yield a natural chain isomorphism.
7. Apply Roos to the row units, which are quasi-isomorphisms by step 4. The nonzero
   augmentation component has second Roos degree zero, so the sign is one. This
   gives etaL ≫ T = Roos(gamma) as a chain-map equality. The two product
   coordinates fix etaL as Roos_j of the j-indexed Roos_n augmentations. The
   counit computation and the quotient augmentation identify unit ≫ e with Q(etaL),
   for the e already fixed in step 5, and prove invertibility of the actual unit.
8. If t=u*s^e, invert u^r_n to deduce s^(e*r_n)U_n=0. Repeat the argument with the
   actual s-power quotients and units. No common exponent, normalization, cohomological
   bound or constructibility has been used. -/
theorem limit_complete
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : Mono (globalSectionMultiplication R t)) :
    ∃ T : ∀ V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
        doubleLimit R V.flip ≅ doubleLimit R V,
      (∀ V (k : ℤ) (n j : ℕ),
        (T V).hom.f k ≫ doubleCoordinate R V k false false n j =
          doubleCoordinate R V.flip k false false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true false n j =
          doubleCoordinate R V.flip k false true j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k false true n j =
          doubleCoordinate R V.flip k true false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true true n j =
          -doubleCoordinate R V.flip k true true j n) ∧
      (∀ {V W} (f : V ⟶ W),
        doubleMap R ((flipFunctor _ _ _).map f) ≫ (T W).hom =
          (T V).hom ≫ doubleMap R f) ∧
      (∀ U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
        ∀ (rU : ℕ → ℕ), (∀ n, 1 ≤ rU n) →
        (∀ (n : ℕ) (a : ℤ),
          endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app
            ((U.asFunctor.obj (op n)).X a)) (rU n) = 0) →
        (∀ M : PrincipalQuotientCompletion.Model R t,
          IsIso (M.unit.app (DerivedCategory.Q.obj (roosF.obj U))) ∧
          ∃ (γ : U.asFunctor ⟶ koszulDouble R t U ⋙ limitComplex R)
            (θ : ∀ j : ℕ, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
            (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R t U).flip)
            (D : (koszulRows R t).obj (roosF.obj U) ≅
              (koszulDouble R t U).flip ⋙ limitComplex R)
            (e : M.completion.obj (DerivedCategory.Q.obj (roosF.obj U)) ≅
              DerivedCategory.Q.obj (doubleLimit R (koszulDouble R t U).flip)),
            (∀ n, γ.app (op n) = rowUnit R t (U.asFunctor.obj (op n))) ∧
            (∀ (j n : ℕ), (θ j).app (op n) =
              koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j) ∧
            (∀ k : ℤ, etaL.f (k + 1) ≫
              (roosχ (koszulTowerComplex R
                ((koszulDouble R t U).flip ⋙ limitComplex R)) k).hom =
              biprod.lift 0 ((Pi.lift (fun j : ℕ ↦
                roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1))) ∧
            etaL ≫ (T (koszulDouble R t U)).hom =
              roosF.map (koszulTowerComplexMap R γ) ∧
            M.unit.app (DerivedCategory.Q.obj (roosF.obj U)) ≫ e.hom =
              DerivedCategory.Q.map etaL ∧
            distributionCoordinates R t U D ∧
            (∀ (P : CochainComplex (ringedSiteModules.{r}
                (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
              (a : P ⟶ roosF.obj U),
              CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso a →
              ∃ b : DerivedCategory.Q.obj ((koszulCompletion R t).obj P) ≅
                  DerivedCategory.Q.obj ((PrincipalQuotientCompletion.quotientRoos R t).obj P),
                b.hom = DerivedCategory.Q.map (quotientComparison R t P) ∧
                M.completion.map (DerivedCategory.Q.map a) ≫ e.hom =
                  M.counit.app P ≫ b.inv ≫
                    DerivedCategory.Q.map ((koszulCompletion R t).map a) ≫
                    DerivedCategory.Q.map ((limitComplex R).mapIso D).hom)) ∧
        (∀ n : ℕ,
          QuasiIso (rowUnit R t (U.asFunctor.obj (op n))) ∧
          ∃ back : (limitComplex R).obj
              (koszulTensorTower R (U.asFunctor.obj (op n)) t) ⟶ U.asFunctor.obj (op n),
            rowUnit R t (U.asFunctor.obj (op n)) ≫ back = 𝟙 _ ∧
            IsIso (DerivedCategory.Q.map back)) ∧
        (∀ n : ℕ, ∃ φ : ∀ k : ℕ,
            (koszulTensorTower R (U.asFunctor.obj (op n)) t).obj
                (op (rU n - 1 + k)) ≅
              U.asFunctor.obj (op n) ⊞ (U.asFunctor.obj (op n))⟦(1 : ℤ)⟧,
          (∀ k : ℕ,
            koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t
                (rU n - 1 + k) ≫ (φ k).hom = biprod.inl) ∧
          (∀ k : ℕ,
            (koszulTensorTower R (U.asFunctor.obj (op n)) t).map
                (homOfLE (Nat.le_succ (rU n - 1 + k))).op ≫ (φ k).hom =
              (φ (k + 1)).hom ≫ biprod.map (𝟙 _)
                (((SheafOfModules.RegularQuotientCone.complexScalar R t).app
                  (U.asFunctor.obj (op n)))⟦(1 : ℤ)⟧'))) ∧
        (∀ (s unit : (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
          (e : ℕ), Mono (globalSectionMultiplication R s) →
          IsIso (globalSectionMultiplication R unit) → 1 ≤ e →
          globalSectionMultiplication R t = globalSectionMultiplication R unit ≫
            endoPow (globalSectionMultiplication R s) e →
          ∀ M : PrincipalQuotientCompletion.Model R s,
            IsIso (M.unit.app (DerivedCategory.Q.obj (roosF.obj U))))) := by
  classical
  obtain ⟨T, hT, hnatural, haugment⟩ := signed_double_roos_interchange R
  have hcore (s : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
      (hs : Mono (globalSectionMultiplication R s))
      (U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (rU : ℕ → ℕ)
      (hr : ∀ n, 1 ≤ rU n)
      (hn : ∀ (n : ℕ) (a : ℤ),
        endoPow ((SheafOfModules.RegularQuotientCone.scalar R s).app
          ((U.asFunctor.obj (op n)).X a)) (rU n) = 0) :
        (∀ M : PrincipalQuotientCompletion.Model R s,
          IsIso (M.unit.app (DerivedCategory.Q.obj (roosF.obj U))) ∧
          ∃ (γ : U.asFunctor ⟶ koszulDouble R s U ⋙ limitComplex R)
            (θ : ∀ j : ℕ, U.asFunctor ⟶ (koszulDouble R s U).flip.obj (op j))
            (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R s U).flip)
            (D : (koszulRows R s).obj (roosF.obj U) ≅
              (koszulDouble R s U).flip ⋙ limitComplex R)
            (e : M.completion.obj (DerivedCategory.Q.obj (roosF.obj U)) ≅
              DerivedCategory.Q.obj (doubleLimit R (koszulDouble R s U).flip)),
            (∀ n, γ.app (op n) = rowUnit R s (U.asFunctor.obj (op n))) ∧
            (∀ (j n : ℕ), (θ j).app (op n) =
              koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) s j) ∧
            (∀ k : ℤ, etaL.f (k + 1) ≫
              (roosχ (koszulTowerComplex R
                ((koszulDouble R s U).flip ⋙ limitComplex R)) k).hom =
              biprod.lift 0 ((Pi.lift (fun j : ℕ ↦
                roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1))) ∧
            etaL ≫ (T (koszulDouble R s U)).hom =
              roosF.map (koszulTowerComplexMap R γ) ∧
            M.unit.app (DerivedCategory.Q.obj (roosF.obj U)) ≫ e.hom =
              DerivedCategory.Q.map etaL ∧
            distributionCoordinates R s U D ∧
            (∀ (P : CochainComplex (ringedSiteModules.{r}
                (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
              (a : P ⟶ roosF.obj U),
              CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso a →
              ∃ b : DerivedCategory.Q.obj ((koszulCompletion R s).obj P) ≅
                  DerivedCategory.Q.obj ((PrincipalQuotientCompletion.quotientRoos R s).obj P),
                b.hom = DerivedCategory.Q.map (quotientComparison R s P) ∧
                M.completion.map (DerivedCategory.Q.map a) ≫ e.hom =
                  M.counit.app P ≫ b.inv ≫
                    DerivedCategory.Q.map ((koszulCompletion R s).map a) ≫
                    DerivedCategory.Q.map ((limitComplex R).mapIso D).hom)) ∧
        (∀ n : ℕ,
          QuasiIso (rowUnit R s (U.asFunctor.obj (op n))) ∧
          ∃ back : (limitComplex R).obj
              (koszulTensorTower R (U.asFunctor.obj (op n)) s) ⟶ U.asFunctor.obj (op n),
            rowUnit R s (U.asFunctor.obj (op n)) ≫ back = 𝟙 _ ∧
            IsIso (DerivedCategory.Q.map back)) ∧
        (∀ n : ℕ, ∃ φ : ∀ k : ℕ,
            (koszulTensorTower R (U.asFunctor.obj (op n)) s).obj
                (op (rU n - 1 + k)) ≅
              U.asFunctor.obj (op n) ⊞ (U.asFunctor.obj (op n))⟦(1 : ℤ)⟧,
          (∀ k : ℕ,
            koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) s
                (rU n - 1 + k) ≫ (φ k).hom = biprod.inl) ∧
          (∀ k : ℕ,
            (koszulTensorTower R (U.asFunctor.obj (op n)) s).map
                (homOfLE (Nat.le_succ (rU n - 1 + k))).op ≫ (φ k).hom =
              (φ (k + 1)).hom ≫ biprod.map (𝟙 _)
                (((SheafOfModules.RegularQuotientCone.complexScalar R s).app
                  (U.asFunctor.obj (op n)))⟦(1 : ℤ)⟧'))) := by
    obtain ⟨γ, θ, etaL, hγ, hθ, hη, htrans⟩ := haugment s U
    obtain ⟨D, hD, hcomparison⟩ :=
      koszul_quotient_completion_comparison R s hs U θ etaL hθ hη
    have hrows (n : ℕ) :=
      nilpotent_koszul_row_retraction R s (U.asFunctor.obj (op n)) (rU n) (hr n) (hn n)
    have hγq : QuasiIso (koszulTowerComplexMap R γ) := by
      apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
      rintro ⟨n⟩
      change QuasiIso (γ.app (op n))
      rw [hγ n]
      exact (hrows n).1.1
    have hroos : QuasiIso (roosF.map (koszulTowerComplexMap R γ)) :=
      CategoryTheory.roos_map_quasiIso _
    have hηiso : IsIso (DerivedCategory.Q.map etaL) := by
      have he : DerivedCategory.Q.map etaL ≫
          DerivedCategory.Q.map (T (koszulDouble R s U)).hom =
          DerivedCategory.Q.map (roosF.map (koszulTowerComplexMap R γ)) := by
        rw [← Functor.map_comp, htrans]
      have hc : IsIso (DerivedCategory.Q.map etaL ≫
          DerivedCategory.Q.map (T (koszulDouble R s U)).hom) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_right (DerivedCategory.Q.map etaL)
        (DerivedCategory.Q.map (T (koszulDouble R s U)).hom)
    refine ⟨?_, fun n ↦ (hrows n).1, fun n ↦ (hrows n).2⟩
    intro M
    obtain ⟨e, hunit, hresolution⟩ := hcomparison M
    have hi : IsIso (M.unit.app (DerivedCategory.Q.obj (roosF.obj U))) := by
      have hc : IsIso (M.unit.app (DerivedCategory.Q.obj (roosF.obj U)) ≫ e.hom) := by
        rw [hunit]
        exact hηiso
      exact IsIso.of_isIso_comp_right
        (M.unit.app (DerivedCategory.Q.obj (roosF.obj U))) e.hom
    exact ⟨hi, γ, θ, etaL, D, e, hγ, hθ, hη, htrans, hunit, hD, hresolution⟩
  refine ⟨T, hT, hnatural, ?_⟩
  intro U rU hr hn
  obtain ⟨hcomplete, hrows, htail⟩ := hcore t ht U rU hr hn
  refine ⟨hcomplete, hrows, htail, ?_⟩
  intro s unit e hs hu he hrelation M
  have := hu
  have hn' (n : ℕ) (a : ℤ) :
      endoPow ((SheafOfModules.RegularQuotientCone.scalar R s).app
        ((U.asFunctor.obj (op n)).X a)) (e * rU n) = 0 :=
    nilpotent_parameter_change R t s unit e (rU n) hrelation _ (hn n a)
  exact ((hcore s hs U (fun n ↦ e * rU n)
    (fun n ↦ Nat.mul_pos he (hr n)) hn').1 M).1

end CategoryTheory.RingedPowerTorsion
