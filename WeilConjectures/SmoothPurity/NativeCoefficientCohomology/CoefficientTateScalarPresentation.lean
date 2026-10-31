/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackTensorNaturality
import WeilConjectures.SmoothPurity.Common.CommonStageTensorRightUnitorNaturality
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateShiftNormalization
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTateRationalScalarNormalization
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientRegularUnitFrobenius

/-! # A scalar presentation of the coefficient Tate constant

This assertion concerns only the coefficient category, before any native realization.
Source: the canonical root-line convention in
`lem-pur-constant-purity-frobenius-square`.
(blueprint: lem-sf-coefficient-tate-scalar-presentation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open WeilConjectures.ConstantPurityFrobenius
attribute [local instance 1100] CategoryTheory.instOverClass
namespace WeilConjectures.NativeCoefficientCohomology

section ScalarPresentation
variable {C : Type*} [Category C] [Preadditive C] {F : C ⥤ C}

private theorem scalar_presentation_of_square
    (K U : IsoAlgebra F) (b : K.carrier ≅ U.carrier) (n : ℕ)
    (h : n • (K.str.hom ≫ b.hom) = F.map b.hom ≫ U.str.hom) :
    ∃ a : U.carrier ≅ U.carrier,
      n • a.hom = 𝟙 U.carrier ∧
      Nonempty (K ≅ IsoAlgebra.mk U.carrier (U.str ≪≫ a)) := by
  let a := U.str.symm ≪≫ F.mapIso b.symm ≪≫ K.str ≪≫ b
  refine ⟨a, ?_, ⟨IsoAlgebra.isoMk b ?_⟩⟩
  · change n • (U.str.inv ≫ F.map b.inv ≫ (K.str.hom ≫ b.hom)) = _
    rw [← Preadditive.comp_nsmul, ← Preadditive.comp_nsmul, h]
    simp only [← F.map_comp_assoc, b.inv_hom_id, F.map_id,
      Category.id_comp, Iso.inv_hom_id]
  · change F.map b.hom ≫ (U.str.hom ≫ a.hom) = K.str.hom ≫ b.hom
    simp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc,
      ← F.map_comp_assoc, b.hom_inv_id, F.map_id, Category.id_comp]

private theorem map_scaled_square
    {D : Type*} [Category D] [Preadditive D]
    (L : C ⥤ D) [L.Additive] (G : D ⥤ D)
    (c : ∀ M, G.obj (L.obj M) ≅ L.obj (F.obj M))
    (K U : IsoAlgebra F) (b : K.carrier ≅ U.carrier) (n : ℕ)
    (h : n • (K.str.hom ≫ b.hom) = F.map b.hom ≫ U.str.hom)
    (hc : G.map (L.map b.hom) ≫ (c U.carrier).hom =
      (c K.carrier).hom ≫ L.map (F.map b.hom)) :
    n • ((c K.carrier).hom ≫ (L.map K.str.hom ≫ L.map b.hom)) =
      G.map (L.map b.hom) ≫ (c U.carrier).hom ≫ L.map U.str.hom := by
  rw [← L.map_comp, ← Preadditive.comp_nsmul, ← L.map_nsmul, h, L.map_comp,
    ← Category.assoc, ← hc]
  simp only [Category.assoc]

omit [Preadditive C] in
private theorem tensor_right_unit_weil_square
    (T : C × C ⥤ C) (K U I : C) (tK : F.obj K ≅ K) (tU : F.obj U ≅ U)
    (μ : ∀ M N, F.obj (T.obj (M, N)) ≅ T.obj (F.obj M, F.obj N))
    (ρ : ∀ M, T.obj (M, I) ≅ M) (ε : F.obj I ≅ I) (b : U ≅ I)
    (hμ : F.map (T.map (Prod.mkHom (𝟙 K) b.hom)) ≫ (μ K I).hom =
      (μ K U).hom ≫ T.map (Prod.mkHom (𝟙 (F.obj K)) (F.map b.hom)))
    (hb : F.map b.hom ≫ ε.hom = tU.hom ≫ b.hom)
    (hε : (μ K I).hom ≫ T.map (Prod.mkHom (𝟙 _) ε.hom) ≫
      (ρ (F.obj K)).hom = F.map (ρ K).hom)
    (hρ : T.map (Prod.mkHom tK.hom (𝟙 I)) ≫ (ρ K).hom =
      (ρ (F.obj K)).hom ≫ tK.hom) :
    (μ K U).hom ≫ T.map (Prod.mkHom tK.hom tU.hom) ≫
      T.map (Prod.mkHom (𝟙 K) b.hom) ≫ (ρ K).hom =
    F.map (T.map (Prod.mkHom (𝟙 K) b.hom) ≫ (ρ K).hom) ≫ tK.hom := by
  have ht : T.map (Prod.mkHom tK.hom tU.hom) ≫
      T.map (Prod.mkHom (𝟙 K) b.hom) =
      T.map (Prod.mkHom (𝟙 (F.obj K)) (F.map b.hom)) ≫
      T.map (Prod.mkHom (𝟙 (F.obj K)) ε.hom) ≫
      T.map (Prod.mkHom tK.hom (𝟙 I)) := by
    rw [← T.map_comp, ← T.map_comp, ← T.map_comp]
    congr 1
    ext <;> simp [hb]
  calc
    _ = (μ K U).hom ≫ (T.map (Prod.mkHom tK.hom tU.hom) ≫
        T.map (Prod.mkHom (𝟙 K) b.hom)) ≫ (ρ K).hom := by simp
    _ = (μ K U).hom ≫
        T.map (Prod.mkHom (𝟙 (F.obj K)) (F.map b.hom)) ≫
        T.map (Prod.mkHom (𝟙 (F.obj K)) ε.hom) ≫
        (ρ (F.obj K)).hom ≫ tK.hom := by rw [ht]; simp only [Category.assoc, hρ]
    _ = F.map (T.map (Prod.mkHom (𝟙 K) b.hom)) ≫
        (μ K I).hom ≫ T.map (Prod.mkHom (𝟙 (F.obj K)) ε.hom) ≫
        (ρ (F.obj K)).hom ≫ tK.hom := by rw [reassoc_of% hμ]
    _ = _ := by rw [reassoc_of% hε, ← F.map_comp_assoc]

end ScalarPresentation

-- Turn the existing heterogeneous inclusion-map formula into the required square.
private theorem transport_stage_hom {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h

attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory in
private theorem coefficient_stage_naturality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type u) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K M : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left)
    (f : K ⟶ M) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫
      (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom =
    (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  have h := commonStageDerivedPullback_map_inclusion l Qbar
    (D.geometricFrobenius Y₀).hom L K M f
  have hm := (@commonStageDerivedPullback_existsUnique l _ Qbar _ _ _ _ _
    (D.geometricFrobenius Y₀).hom
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec
  have ht := transport_stage_hom
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) _ _ h
  apply (cancel_epi (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  simpa only [sfWeilStagePullbackIdentification, sfCommonStageWeilFrobeniusPullback,
    sfWeilFrobeniusPullback, eqToIso] using ht

variable (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

@[local instance]
private theorem tatePointFiniteType : LocallyOfFiniteType (point P.field).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of P.field.k₀))))
@[local instance]
private theorem tatePointQuasiCompact : QuasiCompact (point P.field).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of P.field.k₀))))

@[instance_reducible, local instance]
private def coefficientTateResidueUnits : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x

private abbrev tateBaseField := AlgebraicallyClosedCoefficients.Coefficient.{u}
  P.coefficients.l P.coefficients.Qbar
  (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)

private abbrev tateRationalLine (d : ℕ) := FrobeniusCoefficientTwists.rationalWeilLine
  P.field P.coefficients.l P.coefficients.different X₀ (tateBaseField P) (d : ℤ)

private abbrev tateRationalUnit := constantWeilRationalComplex
  P.coefficients.l (tateBaseField P) P.field P.coefficients.different X₀

private abbrev tateUnit :=
  constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
    P.coefficients.different X₀ P.coefficients.Qbar

private abbrev tateTensorUnit := pullbackTensorCommonUnit P.coefficients.l
  P.coefficients.Qbar (P.field.geometricFiber X₀).left

private abbrev tateTensor := commonStageDerivedTensor P.coefficients.l
  P.coefficients.Qbar (P.field.geometricFiber X₀).left

private abbrev tatePull := sourceFrobenius P.field P.coefficients.l
  P.coefficients.different P.coefficients.Qbar X₀

omit [IsSeparated X₀.hom] in
private theorem coefficient_common_square_of_rational_square (d : ℕ)
    (b : (tateRationalLine P X₀ d).carrier ≅ (tateRationalUnit P X₀).carrier)
    (hb : (Nat.card P.field.k₀ ^ d) •
      ((tateRationalLine P X₀ d).str.hom ≫ b.hom) =
      (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different X₀
        (tateBaseField P)).map b.hom ≫ (tateRationalUnit P X₀).str.hom) :
    ∃ c : (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).carrier ≅
      (tateUnit P X₀).carrier,
      (Nat.card P.field.k₀ ^ d) •
        ((FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
          P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).str.hom ≫ c.hom) =
        (tatePull P X₀).map c.hom ≫ (tateUnit P X₀).str.hom := by
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
    (Y := (P.field.geometricFiber X₀).left)
    (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
  let c := sfWeilStagePullbackIdentification P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar
    (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
  refine ⟨I.mapIso b, ?_⟩
  have hn := coefficient_stage_naturality P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀
    (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
    (tateRationalLine P X₀ d).carrier (tateRationalUnit P X₀).carrier b.hom
  have hs := map_scaled_square (L := I) (G := tatePull P X₀) (c := c)
    (K := tateRationalLine P X₀ d) (U := tateRationalUnit P X₀) (b := b)
    (n := Nat.card P.field.k₀ ^ d) (h := hb) (hc := hn)
  change (Nat.card P.field.k₀ ^ d) •
      (((c (tateRationalLine P X₀ d).carrier).hom ≫
        I.map (tateRationalLine P X₀ d).str.hom) ≫ I.map b.hom) =
    (tatePull P X₀).map (I.map b.hom) ≫
      ((c (tateRationalUnit P X₀).carrier).hom ≫ I.map (tateRationalUnit P X₀).str.hom)
  simpa only [Category.assoc] using hs

private def coefficient_source_pair_iso (d : ℕ)
    (b : (tateUnit P X₀).carrier ≅ tateTensorUnit P X₀)
    (ε : (tatePull P X₀).obj (tateTensorUnit P X₀) ≅ tateTensorUnit P X₀)
    (hb : (tatePull P X₀).map b.hom ≫ ε.hom = (tateUnit P X₀).str.hom ≫ b.hom)
    (hε : ∀ M,
      (canonicalCommonStagePullbackTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFrobenius X₀).hom M (tateTensorUnit P X₀)).hom ≫
        (tateTensor P X₀).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        (pullbackTensorCommonRightUnitor P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFiber X₀).left ((tatePull P X₀).obj M)).hom =
      (tatePull P X₀).map (pullbackTensorCommonRightUnitor P.coefficients.l
        P.coefficients.Qbar (P.field.geometricFiber X₀).left M).hom) :
    twistedConstant P X₀ d ≅ IsoAlgebra.mk
      (shiftedLine P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ d)
      (shiftedLineTheta P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ d) := by
  let F := tatePull P X₀
  let T := tateTensor P X₀
  let I := tateTensorUnit P X₀
  let U := tateUnit P X₀
  let K := shiftedLine P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀ d
  let tK := shiftedLineTheta P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀ d
  let μ := canonicalCommonStagePullbackTensor P.coefficients.l P.coefficients.Qbar
    (P.field.geometricFrobenius X₀).hom
  let ρ := pullbackTensorCommonRightUnitor P.coefficients.l P.coefficients.Qbar
    (P.field.geometricFiber X₀).left
  let i := sourceUnit P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) d
  let e := i ≪≫ T.mapIso (Iso.prod (Iso.refl K) b) ≪≫ ρ K
  have hμ : F.map (T.map (Prod.mkHom (𝟙 K) b.hom)) ≫ (μ K I).hom =
      (μ K U.carrier).hom ≫ T.map (Prod.mkHom (𝟙 (F.obj K)) (F.map b.hom)) := by
    have h := commonStagePullbackTensor_naturality P.coefficients.l P.coefficients.Qbar
      (P.field.geometricFrobenius X₀).hom
      (fun E _ _ _ {_ _ _ _} a b ↦ canonicalRationalPullbackTensor_naturality
        P.coefficients.l E (P.field.geometricFrobenius X₀).hom a b) (𝟙 K) b.hom
    change F.map (T.map (Prod.mkHom (𝟙 K) b.hom)) ≫ (μ K I).hom =
      (μ K U.carrier).hom ≫ T.map (Prod.mkHom (F.map (𝟙 K)) (F.map b.hom)) at h
    rw [F.map_id] at h
    exact h
  have hρ := commonStageTensorRightUnitor_naturality P.coefficients.l
    (P.field.geometricFiber X₀).left P.coefficients.Qbar tK.hom
  have hs := tensor_right_unit_weil_square (F := F) T K U.carrier I tK U.str
    μ ρ ε b hμ hb (hε K) hρ
  apply IsoAlgebra.isoMk e
  change F.map (i.hom ≫ T.map (Prod.mkHom (𝟙 K) b.hom) ≫ (ρ K).hom) ≫ tK.hom =
    (F.map i.hom ≫ (μ K U.carrier).hom ≫
      T.map (Prod.mkHom tK.hom U.str.hom) ≫ i.inv) ≫
      (i.hom ≫ T.map (Prod.mkHom (𝟙 K) b.hom) ≫ (ρ K).hom)
  simpa only [F.map_comp, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun z ↦ F.map i.hom ≫ z) hs.symm

omit [IsSeparated X₀.hom] in
private theorem coefficient_scalar_presentation_from_data (d : ℕ)
    (b : (tateUnit P X₀).carrier ≅ tateTensorUnit P X₀)
    (ε : (tatePull P X₀).obj (tateTensorUnit P X₀) ≅ tateTensorUnit P X₀)
    (hb : (tatePull P X₀).map b.hom ≫ ε.hom = (tateUnit P X₀).str.hom ≫ b.hom)
    (hε : ∀ M,
      (canonicalCommonStagePullbackTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFrobenius X₀).hom M (tateTensorUnit P X₀)).hom ≫
        (tateTensor P X₀).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        (pullbackTensorCommonRightUnitor P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFiber X₀).left ((tatePull P X₀).obj M)).hom =
      (tatePull P X₀).map (pullbackTensorCommonRightUnitor P.coefficients.l
        P.coefficients.Qbar (P.field.geometricFiber X₀).left M).hom)
    (c : (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).carrier ≅
        (tateUnit P X₀).carrier)
    (hc : (Nat.card P.field.k₀ ^ d) •
      ((FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).str.hom ≫ c.hom) =
      (tatePull P X₀).map c.hom ≫ (tateUnit P X₀).str.hom)
    (s : IsoAlgebra.mk
      (shiftedLine P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ d)
      (shiftedLineTheta P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ d) ≅
      (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ))⟦2 * (d : ℤ)⟧) :
    ∃ a : (tateUnit P X₀).carrier ≅ (tateUnit P X₀).carrier,
      (Nat.card P.field.k₀ ^ d) • a.hom = 𝟙 (tateUnit P X₀).carrier ∧
      Nonempty (twistedConstant P X₀ d ≅
        (IsoAlgebra.mk (tateUnit P X₀).carrier
          ((tateUnit P X₀).str ≪≫ a))⟦2 * (d : ℤ)⟧) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := scalar_presentation_of_square
    (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ))
    (tateUnit P X₀) c (Nat.card P.field.k₀ ^ d) hc
  exact ⟨a, ha, ⟨coefficient_source_pair_iso P X₀ d b ε hb hε ≪≫ s ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso e⟩⟩

omit [IsSeparated X₀.hom] in
private theorem coefficient_scalar_presentation_reduction (d : ℕ)
    (hunit : ∃ b : (tateUnit P X₀).carrier ≅ tateTensorUnit P X₀,
      (tatePull P X₀).map b.hom ≫
        (pullbackTensorCommonStageUnitCoherence P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFrobenius X₀).hom).exists.choose.hom =
        (tateUnit P X₀).str.hom ≫ b.hom)
    (hline : ∃ c : (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).carrier ≅
        (tateUnit P X₀).carrier,
       (Nat.card P.field.k₀ ^ d) •
      ((FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).str.hom ≫ c.hom) =
      (tatePull P X₀).map c.hom ≫ (tateUnit P X₀).str.hom)
    :
    ∃ a : (tateUnit P X₀).carrier ≅ (tateUnit P X₀).carrier,
      (Nat.card P.field.k₀ ^ d) • a.hom = 𝟙 (tateUnit P X₀).carrier ∧
      Nonempty (twistedConstant P X₀ d ≅
        (IsoAlgebra.mk (tateUnit P X₀).carrier
          ((tateUnit P X₀).str ≪≫ a))⟦2 * (d : ℤ)⟧) := by
  let hU := pullbackTensorCommonStageUnitCoherence P.coefficients.l
    P.coefficients.Qbar (P.field.geometricFrobenius X₀).hom
  let ε := hU.exists.choose
  have hε := hU.exists.choose_spec
  obtain ⟨b, hb⟩ := hunit
  obtain ⟨c, hc⟩ := hline
  obtain ⟨s⟩ := coefficient_tate_shift_normalization P X₀ d
  exact coefficient_scalar_presentation_from_data P X₀ d b ε hb
    (fun M ↦ (hε M).2) c hc s

-- Preserve the separation binder of the original statement for downstream compatibility.
set_option linter.unusedSectionVars false in
/-- Trivializing the coefficient Tate line expresses its action as the inverse of
multiplication by `q^d` on the constant unit, followed by the canonical even shift.

Source: canonicalSourceTheta in lem-pur-constant-purity-frobenius-square;
Weil I (2.2), geometric Frobenius on roots of unity.
(blueprint: lem-sf-coefficient-tate-scalar-presentation)

Proof: choose compatible primitive ell-power roots in the algebraically closed
geometric field. At each finite level the root generator identifies the root line
with the regular coefficient module. The power maps send the chosen generator to
its predecessor, so these identifications form an isomorphism of inverse systems.
Taking the inverse limit and extending integral coefficients gives a trivialization
of the completed root line. Tensor the same trivialization d times, rationalize,
and include its least finite coefficient stage into the common-stage category.
The arithmetic q-power map sends each root to its q-th power. Its inverse,
geometric Frobenius, therefore multiplies the chosen line by q inverse; on the
ordered d-fold tensor power it multiplies by q^(-d). This scalar is independent
of the generator since multiplication by a unit commutes with it. Let a be
multiplication by q^(-d) on the regular unit. Since q is nonzero in characteristic
zero, this is an automorphism and q^d times its hom is the identity.
Apply sourceUnit to replace pullback of the point unit by the source unit, use
the normalized comparison of the regular coefficient with the tensor unit, and
apply the tensor right unitor. The coefficient inclusion shift comparison moves
the even shift from the least-stage line to this trivialized constant pair.
Substitution of canonicalSourceTheta cancels the unit comparisons; the remaining
root-line map is the scalar a just computed. Thus the carrier comparison is a
morphism of Frobenius pairs, as is its inverse, giving the stated isomorphism.
For d=0 use the identity scalar and zero-shift unit map. For an empty scheme all
these objects and morphisms are zero and the same identities hold. -/
theorem coefficient_tate_scalar_presentation (d : ℕ) :
    let U := constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
      P.coefficients.different X₀ P.coefficients.Qbar
    ∃ a : U.carrier ≅ U.carrier,
      (Nat.card P.field.k₀ ^ d) • a.hom = 𝟙 U.carrier ∧
      Nonempty (twistedConstant P X₀ d ≅
        (IsoAlgebra.mk U.carrier (U.str ≪≫ a))⟦2 * (d : ℤ)⟧) := by
  obtain ⟨A⟩ := coefficient_tate_root_frames P.field P.coefficients.l
    P.coefficients.different X₀
  have hp := coefficient_tate_frame_power_scalar_law P.coefficients.l (tateBaseField P)
    (P.field.geometricFrobenius X₀).hom (Nat.card P.field.k₀) A
  apply coefficient_scalar_presentation_reduction P X₀ d
  · exact coefficient_regular_unit_frobenius P X₀
  · obtain ⟨b, hb⟩ := coefficient_tate_rational_scalar_normalization P X₀ A hp d
    exact coefficient_common_square_of_rational_square P X₀ d b hb

end WeilConjectures.NativeCoefficientCohomology
