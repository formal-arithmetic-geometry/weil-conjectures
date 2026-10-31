/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import all WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData

/-! # Normalization of the shifted coefficient root pair -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open WeilConjectures.ConstantPurityFrobenius
attribute [local instance 1100] CategoryTheory.instOverClass
namespace WeilConjectures.NativeCoefficientCohomology

private theorem common_shift_stage
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) (n : ℤ) :
    HEq (((commonStageDerivedPullback l Ω f).commShiftIso n).hom.app
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        (((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).commShiftIso n).hom.app
            K)) := by
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, _, _, hc, _⟩ :=
    (automorphismConstructibleStage_descended_shifts l Ω C f
      (Iso.refl Y) (Iso.refl X) (by simp)).2
  have hn (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) (r : ℤ) :
      HEq ((Functor.commShiftIso (commonStageDerivedPullback l Ω f)
        (self := c) r).hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          (((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).commShiftIso r).hom.app
              K)) := by
    have h := hc L
    obtain ⟨s, hs, hn⟩ := h
    have he := fieldRationalShift_normalization l Ω f L s hs
    subst s
    exact hn K r
  have he : c = fieldCommonPullShift l Ω f := by
    apply (fieldCommonPullShift_existsUnique l Ω f).unique
    · intro L K
      exact hn L K 1
    · exact (fieldCommonPullShift_existsUnique l Ω f).exists.choose_spec
  subst c
  exact hn L K n

private theorem normalized_shift_square
    {C D : Type*} [Category C] [Category D]
    (I : C ⥤ D) (P S : C ⥤ C) (F T : D ⥤ D)
    (hF : ∀ K, F.obj (I.obj K) = I.obj (P.obj K))
    (hT : ∀ K, T.obj (I.obj K) = I.obj (S.obj K))
    (e : ∀ K, I.obj (S.obj K) ≅ T.obj (I.obj K))
    (he : ∀ K, HEq (e K).hom (𝟙 (I.obj (S.obj K))))
    (c : ∀ K, F.obj (I.obj K) ≅ I.obj (P.obj K))
    (hc : ∀ K, (c K).hom = eqToHom (hF K))
    (p : ∀ K, P.obj (S.obj K) ⟶ S.obj (P.obj K))
    (q : ∀ K, F.obj (T.obj (I.obj K)) ⟶ T.obj (F.obj (I.obj K)))
    (hq : ∀ K, HEq (q K) (I.map (p K))) (K : C) :
    F.map (e K).hom ≫ q K ≫ T.map (c K).hom =
      (c (S.obj K)).hom ≫ I.map (p K) ≫ (e (P.obj K)).hom := by
  have heq (K : C) : (e K).hom = eqToHom (hT K).symm :=
    eq_of_heq ((he K).trans
      (eqToHom_heq_id_dom _ _ (hT K).symm).symm)
  have hq' : q K =
      eqToHom ((congrArg F.obj (hT K)).trans (hF (S.obj K))) ≫
        I.map (p K) ≫
        eqToHom ((hT (P.obj K)).symm.trans (congrArg T.obj (hF K).symm)) :=
    (conj_eqToHom_iff_heq' _ _ _ _).mpr (hq K)
  rw [heq, hc, hq', hc, heq]
  simp only [eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

private def shifted_pair_comparison
    {C : Type*} [Category C] [HasShift C ℤ] (F : C ⥤ C) [F.CommShift ℤ]
    (K : IsoAlgebra F) (n : ℤ) :
    K⟦n⟧ ≅ (IsoAlgebra.mapOfNatIso (F.commShiftIso n)).obj K :=
  (Algebra.IsIsoStr F).fullyFaithfulι.preimageIso
    (((IsoAlgebra.ι F).commShiftIso n).app K)

private def pair_stage_shift_iso
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (I : C ⥤ D) [I.CommShift ℤ] (P : C ⥤ C) [P.CommShift ℤ]
    (F : D ⥤ D) [F.CommShift ℤ]
    (c : ∀ K, F.obj (I.obj K) ≅ I.obj (P.obj K)) (n : ℤ)
    (hn : ∀ K, F.map (((I.commShiftIso n).app K).hom) ≫
      ((F.commShiftIso n).app (I.obj K)).hom ≫
      (shiftFunctor D n).map (c K).hom =
      (c (K⟦n⟧)).hom ≫ I.map (((P.commShiftIso n).app K).hom) ≫
        ((I.commShiftIso n).app (P.obj K)).hom)
    (K : C) (t : P.obj K ≅ K) :
    IsoAlgebra.mk (I.obj (K⟦n⟧))
        (c (K⟦n⟧) ≪≫ I.mapIso (((P.commShiftIso n).app K) ≪≫
          (shiftFunctor C n).mapIso t)) ≅
      (IsoAlgebra.mk (I.obj K) (c K ≪≫ I.mapIso t))⟦n⟧ := by
  let A := IsoAlgebra.mk (I.obj K) (c K ≪≫ I.mapIso t)
  refine Iso.trans ?_ (shifted_pair_comparison F A n).symm
  apply IsoAlgebra.isoMk ((I.commShiftIso n).app K)
  change F.map (((I.commShiftIso n).app K).hom) ≫
      (((F.commShiftIso n).app (I.obj K)).hom ≫
        (shiftFunctor D n).map ((c K).hom ≫ I.map t.hom)) =
    ((c (K⟦n⟧)).hom ≫
      I.map (((P.commShiftIso n).app K).hom ≫ (shiftFunctor C n).map t.hom)) ≫
        ((I.commShiftIso n).app K).hom
  rw [(shiftFunctor D n).map_comp, I.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn K]
  exact congrArg (fun z ↦ (c (K⟦n⟧)).hom ≫
    I.map (((P.commShiftIso n).app K).hom) ≫ z)
      (((I.commShiftIso n).hom.naturality t.hom).symm)

attribute [local irreducible] sfWeilStagePullbackIdentification in
private theorem geometric_stage_shift_square
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
      (D.geometricFiber X₀).left L) (n : ℤ) :
    (sourceFrobenius D l hl Ω X₀).map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion L).commShiftIso n).app K).hom ≫
      (((sourceFrobenius D l hl Ω X₀).commShiftIso n).app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)).hom ≫
      (shiftFunctor _ n).map (sfWeilStagePullbackIdentification D l hl X₀ Ω L K).hom =
    (sfWeilStagePullbackIdentification D l hl X₀ Ω L (K⟦n⟧)).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        (((sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).commShiftIso n).app K).hom ≫
      (((GeneralAlgebraicallyClosedCoefficients.inclusion L).commShiftIso n).app
        ((sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj K)).hom := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
    (Y := (D.geometricFiber X₀).left) L
  let P := sfWeilFrobeniusPullback D l hl X₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
  let F := sourceFrobenius D l hl Ω X₀
  have hF (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
      (D.geometricFiber X₀).left L) : F.obj (I.obj M) = I.obj (P.obj M) :=
    (commonStageDerivedPullback_existsUnique l Ω
      (D.geometricFrobenius X₀).hom).exists.choose_spec.1 _
  have hT (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
      (D.geometricFiber X₀).left L) :
      (shiftFunctor _ n).obj (I.obj M) = I.obj (M⟦n⟧) :=
    (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
      (l := l) (Ω := Ω) (Y := (D.geometricFiber X₀).left)).exists.choose_spec.2.1 n _
  refine normalized_shift_square (C := _) (D := _) (I := I) (P := P)
    (S := shiftFunctor _ n) (F := F) (T := shiftFunctor _ n)
    (hF := hF) (hT := hT) (e := fun M ↦ (I.commShiftIso n).app M)
    (c := sfWeilStagePullbackIdentification D l hl X₀ Ω L)
    (he := ?_) (hc := by intro M; unfold sfWeilStagePullbackIdentification; exact eqToIso.hom _)
    (p := fun M ↦ ((P.commShiftIso n).app M).hom)
    (q := fun M ↦ ((F.commShiftIso n).app (I.obj M)).hom)
    (hq := ?_) (K := K)
  · intro M
    exact (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
      (l := l) (Ω := Ω) (Y := (D.geometricFiber X₀).left)).exists.choose_spec.2.2.2.choose_spec
        n L M
  · intro M
    exact common_shift_stage l Ω (D.geometricFrobenius X₀).hom L M n

/-- Including the finite-stage shifted root line gives the canonical shift of its
common-stage Frobenius pair.

Source: coefficient Tate convention, least finite coefficient stage and normalized shifts.
(blueprint: lem-sf-coefficient-tate-shift-normalization)

Proof: the normalized common-stage pullback shift agrees with the rational shift
on every finite representative. Its uniqueness at shift one identifies the selected
shift with the descended one, whose normalization holds at every integer. Inclusion
shift components are identity transports. These normalizations give the square
between inclusion, pullback and shift. Naturality of the inclusion shift moves the
finite root-line structure through this square. Thus its carrier comparison is a
morphism of Frobenius pairs; its inverse is as well. The fully faithful inclusion
of invertible-structure algebras identifies this with the published pair shift.
The same argument covers zero shifts and zero objects. -/
theorem coefficient_tate_shift_normalization
    (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (d : ℕ) :
    Nonempty (IsoAlgebra.mk
        (shiftedLine P.field P.coefficients.l P.coefficients.different
          P.coefficients.Qbar X₀ d)
        (shiftedLineTheta P.field P.coefficients.l P.coefficients.different
          P.coefficients.Qbar X₀ d) ≅
      (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ))⟦2 * (d : ℤ)⟧) := by
  let := fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l
    P.coefficients.different X₀ x
  let := fieldWeilFrobeniusShift P.field P.coefficients.l P.coefficients.different
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
      P.coefficients.Qbar
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)) X₀
  exact ⟨pair_stage_shift_iso
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar))
    (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different X₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)))
    (sourceFrobenius P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar X₀)
    (sfWeilStagePullbackIdentification P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar))
    (2 * (d : ℤ))
    (fun K ↦ geometric_stage_shift_square P.field P.coefficients.l
      P.coefficients.different P.coefficients.Qbar X₀ _ K (2 * (d : ℤ)))
    (sfRationalTwistingCoefficient P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar))
      (P.field.geometricFiber X₀).left (d : ℤ))
    (FrobeniusCoefficientTwists.rationalDerivedLineMap P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar))
      (P.field.geometricFrobenius X₀).hom (d : ℤ))⟩

end WeilConjectures.NativeCoefficientCohomology
