/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionRealization
public import WeilConjectures.AlgebraicGeometry.CompactSupportCompletedScalarArrow
import all WeilConjectures.AlgebraicGeometry.CompactSupportProjectionRealization
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientModels
import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison

/-! # Identification of the strict scalar-limit arrow

The finite comparison equation and constructible Milnor injection identify the
strict scalar arrow with the actual proper/open mate.
Source: Stacks Tags 0941, 0A07, 07A6 and 0B56.
(blueprint: lem-pur-compact-support-scalar-gamma-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurScalarProjection
open PurCompactSupport

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedCoefficientMap PurCompactSupport.comparison

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

include hl in
private theorem scheme_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    IsUnit (l : Γ(W, ⊤)) := by
  let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
  simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom

include hl in
private theorem residue_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (w : W) :
    IsUnit (l : W.residueField w) := by
  let ρ := W.presheaf.germ ⊤ w trivial
  have hs := (scheme_unit l D hl W).map ρ.hom
  exact (by simpa only [map_natCast] using hs.map (W.residue w).hom)

include hl in
private theorem constructible_cofinal_reduction_ext
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))]
    {A B : DerivedCategory (scalarReductionSource l E W)}
    (hA : sfIntegralConstructible l E W A) (hB : sfIntegralConstructible l E W B)
    (a b : A ⟶ B) (e : ℕ) (he : 1 ≤ e)
    (hab : ∀ n : ℕ,
      (pbcDerivedExtend (projection l E (e * (n + 1)) (Nat.mul_pos he (by omega)) W)).map a =
      (pbcDerivedExtend (projection l E (e * (n + 1)) (Nat.mul_pos he (by omega)) W)).map b) :
    a = b := by
  apply constructible_reduction_ext l E D hl W hA hB a b
  intro n
  let m := e * (n + 1) - 1
  have hm : m + 1 = e * (n + 1) := Nat.sub_add_cancel (Nat.mul_pos he (by omega))
  have hnm : n ≤ m := by
    have h := Nat.mul_le_mul_right (n + 1) he
    dsimp only [m]
    omega
  have hmred : (scalarReductionDerivedExtension l E W m).map a =
      (scalarReductionDerivedExtension l E W m).map b := by
    have hpos (q : ℕ) (hq : 1 ≤ q) (hqeq : q = e * (n + 1)) :
        (pbcDerivedExtend (projection l E q hq W)).map a =
          (pbcDerivedExtend (projection l E q hq W)).map b := by
      subst q
      exact hab n
    have h := hpos (m + 1) (Nat.le_add_left 1 m) hm
    apply (cancel_epi ((finiteReductionIso l E W m).hom.app A)).1
    rw [← (finiteReductionIso l E W m).hom.naturality,
      ← (finiteReductionIso l E W m).hom.naturality, h]
  have hu : a ≫ (sfDerivedReductionUnit l E W m).app B =
      b ≫ (sfDerivedReductionUnit l E W m).app B := by
    have ha := (sfDerivedReductionUnit l E W m).naturality a
    have hb := (sfDerivedReductionUnit l E W m).naturality b
    dsimp only [Functor.id_map, Functor.comp_map] at ha hb
    rw [ha, hb, hmred]
  apply ((derivedScalarExtensionRestrictionAdjunction l E W n).choose.homEquiv _ _).injective
  change (sfDerivedReductionUnit l E W n).app A ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionDerivedExtension l E W n).map a) =
    (sfDerivedReductionUnit l E W n).app A ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionDerivedExtension l E W n).map b)
  have ha := (sfDerivedReductionUnit l E W n).naturality a
  have hb := (sfDerivedReductionUnit l E W n).naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at ha hb
  rw [← ha, ← hb]
  have hc := (sfIntegralReductionCone l E W B).w (homOfLE hnm).op
  change (sfDerivedReductionUnit l E W m).app B ≫ _ =
    (sfDerivedReductionUnit l E W n).app B at hc
  rw [← hc, ← Category.assoc, ← Category.assoc, hu]

include D hl in
private theorem realization_positive
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) (m : ℕ) (hm : 1 ≤ m) :
    (pbcDerivedExtend (projection l E m hm Y)).map
        (realization l E D hl f c S M hM).hom ≫
      PurStrictScalar.scalarSupportPositiveCounit l E c S m hm M =
        (comparison (reduction l E m hm) c).app M := by
  cases m with
  | zero => omega
  | succ n => exact (realization_existsUnique l E D hl f c S M hM).exists.choose_spec n

include D hl in
/-- The strict scalar limit map is the actual ordinary proper/open scalar mate
under the canonical realizations. This is an equality of integral maps.
Source: Stacks 07A6, 0B56, 0941;
(blueprint: lem-pur-compact-support-scalar-gamma-identification), Step 7.
Proof: the scalar-limit theorem gives the scalar-extended finite-Tor domain,
identifies its normalized arrow with completedArrow, and gives that arrow's finite
counit equation. The actual proper/open comparison has its prescribed reduction
equation, and the realizations have their normalized finite counits. Naturality
of scalar balancing therefore makes both integral composites have equal reductions
at exponents e(n+1), after cancelling the invertible counit and balancing maps.
The source and target are constructible by the qcqs realization, the coefficient
model and the F realization. Reduction-unit transitions descend these equalities
to every exponent. Finite shifted Hom groups kill the Milnor obstruction, so the
constructible Milnor injection proves equality. This uses no faithfulness claim
for arbitrary derived objects. -/
theorem gamma_identification
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ∃ hCM : finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          (realization l E D hl f c SE M hM).hom ≫
          PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM =
        (comparison (completedChange l E F i) c).app M ≫
          (realization l F D hl f c SF
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hCM).hom := by
  obtain ⟨γ, _, hγ⟩ := PurStrictScalar.compactSupportScalarLimitReduction
    l E F i D hl f c SE SF e he hepos
  have hCM := (hγ ⟨M, hM⟩).1
  refine ⟨hCM, ?_⟩
  have hγeq : γ.app ⟨M, hM⟩ =
      PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM := by
    apply (PurScalarArrow.completedArrow_existsUnique
      l E F i D hl f c SE SF e he hepos M hM).unique
    · exact (hγ ⟨M, hM⟩).2.2.2.2.2.2.2.2.1.symm
    · exact (PurScalarArrow.completedArrow_existsUnique
        l E F i D hl f c SE SF e he hepos M hM).exists.choose_spec
  let A := (image (completed l E) c).obj M
  let CM := (pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M
  have hA := image_constructible l E D hl f c M hM.1
  let (y : Y) : Invertible (l : Y.residueField y) := (residue_unit l D hl Y y).invertible
  have hAT : finiteTorConstructibleIntegral l E Y A := by
    rw [← (integral_residue_tor D l hl E Y).2]
    exact hA
  have hCA := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he Y A hAT).1.1
  have hB : sfIntegralConstructible l F Y ((PurStrictScalar.scalarSupport l F c SF).obj CM) :=
    ObjectProperty.prop_of_iso (sfIntegralConstructible l F Y)
      (realization l F D hl f c SF CM hCM)
      (image_constructible l F D hl f c CM hCM.1)
  apply constructible_cofinal_reduction_ext l F D hl Y hCA hB _ _ e hepos
  intro n
  let m := e * (n + 1)
  have hm : 1 ≤ m := Nat.mul_pos hepos (Nat.le_add_left 1 n)
  let R := pbcDerivedExtend (projection l F m hm Y)
  let PF := image (finite l F m hm) c
  have hε' (q : ℕ) (hq : 1 ≤ q) :
      IsIso (PurStrictScalar.scalarSupportPositiveCounit l F c SF q hq CM) := by
    cases q with
    | zero => omega
    | succ k => exact ((hγ ⟨M, hM⟩).2.2.2.2.2.2.1 k).2
  have := hε' m hm
  apply (Iso.cancel_iso_hom_right _ _
    (asIso (PurStrictScalar.scalarSupportPositiveCounit l F c SF m hm CM))).1
  apply (Iso.cancel_iso_hom_right _ _ (PF.mapIso
    ((PurStrictScalar.scalarReductionBalancing l E F i X e he hepos n).app M))).1
  have hfinite := (hγ ⟨M, hM⟩).2.2.2.2.2.2.2.2.2.2.2.1 n
  rw [hγeq] at hfinite
  have hE := (realization_existsUnique l E D hl f c SE M hM).exists.choose_spec n
  have hF := realization_positive l F D hl f c SF CM hCM m hm
  have hbal := (PurStrictScalar.scalarReductionBalancing l E F i Y e he hepos n).hom.naturality
    (realization l E D hl f c SE M hM).hom
  with_unfolding_all simp only [Functor.comp_map] at hbal
  have hcomp := comparison_reduction l E F i e he hepos (n + 1)
    (Nat.le_add_left 1 n) c M
  have hfin :
      (comparison (finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)) c).app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M) =
        finiteTensorMap l E F i e he hepos n c M :=
    comparison_factorization (finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)) c _
  dsimp only [ReductionComparisonEquation] at hcomp
  erw [hfin] at hcomp
  dsimp only [asIso, Functor.mapIso, Iso.app]
  simp only [Functor.map_comp, Category.assoc]
  erw [hfinite, reassoc_of% hbal]
  erw [← Functor.map_comp_assoc, hE]
  erw [reassoc_of% hF]
  exact hcomp.symm

end WeilConjectures.PurScalarProjection
