/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.FiniteP1CoefficientSplitting
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitInsertion
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarBalancingExistence
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarLineNormalizationOfBalancing

/-! # Normalized scalar squares for the two projective-line columns

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-scalar-projective-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

private noncomputable def canonicalEndpoint
    (φ : A →+* B) (N : ℕ) (_hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    P1KummerScalarEndpoints φ N hA hB T := {
  unitInsertion := Functor.LaxMonoidal.ε
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
  lineInsertion := ProEtale.reductionEtaleTateMap φ T N hA hB
  unit_normalization := balancingRestrictionUnit φ T
  line_normalization := by
    intro W a z
    exact (ProEtale.reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec W a z
  unitIso := ExceptionalCoefficients.unitIso φ T
  lineIso := ProEtale.reductionEtaleTateIso φ T N hA hB hT
  unit_derived := WeilConjectures.finiteCoefficient_unit_eq_scalarInsertion φ T
  line_derived := by
    dsimp only [ProEtale.reductionEtaleTateIso, asIso_hom,
      ProEtale.reductionEtaleTateExtensionMap, p1KummerDerivedInsertion]
    have h := FiniteSmoothPurity.scalarSingleMap_eq_scalarInsertion φ T
      (Scheme.finiteEtaleTateLine T N A hA) (Scheme.finiteEtaleTateLine T N B hB)
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
        (ProEtale.reductionEtaleTateMap φ T N hA hB))
    simpa only [ordinaryFiniteLine, ordinaryFiniteDegreeZero,
      FiniteSmoothPurity.scalarSingleMap, Equiv.apply_symm_apply] using h }

private theorem canonicalEndpoint_unit
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (canonicalEndpoint φ N hN hA hB T hT).unitIso.hom = unit φ T := by
  exact (scalar_unit_map φ T).symm

private theorem canonicalEndpoint_shiftedLine
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (canonicalEndpoint φ N hN hA hB T hT).shiftedLineIso.hom =
      line φ N hN hA hB T hT := by
  have hstalk (x : T) : IsUnit (N : T.presheaf.stalk x) := by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom
  have norm := finite_tate_scalar_source_normalization φ N hN hA hB T hstalk
  have hb := (Classical.choose_spec norm.2.exists).1.1 1
  have he : ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
      (balancing φ N hN hA hB T hT 1).hom) =
      ProEtale.reductionEtaleTateMap φ T N hA hB := by
    apply (ProEtale.reductionEtaleTateMap_existsUnique φ T N hA hB).unique
    · intro W a z
      have hg := hb W a 1 (fun _ ↦ z)
      simp only [one_smul, mul_one, Scheme.finiteTateEtalePowerGenerator] at hg
      rw [Adjunction.homEquiv_unit]
      unfold balancing
      exact hg
    · exact (ProEtale.reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec
  have hh : ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (ProEtale.reductionEtaleTateMap φ T N hA hB) =
      (balancing φ N hN hA hB T hT 1).hom := by
    apply ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact he.symm
  dsimp only [canonicalEndpoint, P1KummerScalarEndpoints.shiftedLineIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    ProEtale.reductionEtaleTateIso, asIso_hom,
    ProEtale.reductionEtaleTateExtensionMap, line, finiteTateScalarLineMap]
  simp only [Int.natCast_one]
  rw [hh]
  rfl

private theorem columns_of_splitting
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive]
    {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (x : F.obj X ⟶ X') (y : F.obj Y ⟶ Y') (e : F.obj Z ⟶ Z')
    (h : F.map (biprod.desc a b) ≫ e =
      biprod.lift (F.map biprod.fst ≫ x) (F.map biprod.snd ≫ y) ≫
        biprod.desc a' b') :
    (F.map a ≫ e = x ≫ a') ∧ (F.map b ≫ e = y ≫ b') := by
  constructor
  · have hh := congrArg (F.map biprod.inl ≫ ·) h
    simpa only [← F.map_comp_assoc, biprod.inl_desc, Category.assoc,
      biprod.lift_desc, Preadditive.comp_add, ← F.map_comp_assoc,
      biprod.inl_fst, biprod.inl_snd, F.map_id, F.map_zero,
      Category.id_comp, zero_comp, zero_add, add_zero] using hh
  · have hh := congrArg (F.map biprod.inr ≫ ·) h
    simpa only [← F.map_comp_assoc, biprod.inr_desc, Category.assoc,
      biprod.lift_desc, Preadditive.comp_add, ← F.map_comp_assoc,
      biprod.inr_fst, biprod.inr_snd, F.map_id, F.map_zero,
      Category.id_comp, zero_comp, add_zero, zero_add] using hh

/-- The normalized scalar maps preserve separately the twisted unit and the Kummer
column.

Source: vector-bundle-purity proof paragraph 2; scalar-descent proof Steps 1--3.
Proof: construct the normalized Kummer endpoints from the ordinary coefficient unit
and the canonical Tate reduction map. The adjoint-insertion formula computes their
derived maps. The unit map agrees with the specified multiplication comparison.
For the line map, evaluate the normalized balancing formula at the pure generator
`(z ⊗ 1) ⊗ 1`; uniqueness of the roots-normalized reduction map identifies its
adjoint with balancing. Applying the degree-zero and shift functors identifies the
shifted endpoint with the specified `line` map, including its shift comparison.

Apply the proved projective-line coefficient splitting to these endpoints and the
specified projective trace data. Its comparison is the actual proper scalar mate.
Rewrite each splitting as the biproduct descent of its twisted-unit and Kummer
columns, then precompose respectively with the scalar images of `biprod.inl` and
`biprod.inr`. Additivity eliminates the other column and gives the two equations.
This uses the normalized unit/Kummer and actual adjunction comparisons of the
blueprint; it asserts no affine or bundle compatibility. No flatness of the
coefficient map, or nonzero-ring hypothesis, enters the argument.
(blueprint: lem-pur-vector-scalar-projective-components). -/
theorem projective_components (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ((scalarExtension φ S).map
        (ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA) S hS) ≫
      projective φ N hN hA hB S hS =
      line φ N hN hA hB S hS ≫
        ordinaryFiniteP1Unit B N hB (projectiveLineTraceTransport N hN B hB) S hS) ∧
    ((scalarExtension φ S).map (ordinaryFiniteP1ChernPushforward A N hA S
        (projectiveLineTraceDatum N hN A hA S hS).chern) ≫
      projective φ N hN hA hB S hS =
      unit φ S ≫ ordinaryFiniteP1ChernPushforward B N hB S
        (projectiveLineTraceDatum N hN B hB S hS).chern) := by
  let eS := canonicalEndpoint φ N hN hA hB S hS
  let eP := canonicalEndpoint φ N hN hA hB (ProjectiveLine S)
    (ordinaryFiniteP1_isUnit N S hS)
  have hh := (finiteP1CoefficientSplitting N hN φ hA hB S hS eS eP
    (projectiveLineTraceTransport N hN A hA)
    (projectiveLineTraceTransport N hN B hB)
    (projectiveLineTraceDatum N hN A hA S hS)
    (projectiveLineTraceDatum N hN B hB S hS)).1
  rw [(projectiveLineTraceDatum N hN A hA S hS).decomposition_hom,
    (projectiveLineTraceDatum N hN B hB S hS).decomposition_hom] at hh
  have : (scalarExtension φ S).Additive := by
    unfold scalarExtension ProEtale.pbcFixedScalarExtension
    exact (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ)).left_adjoint_additive
  have hc := columns_of_splitting (scalarExtension φ S) _ _ _ _
    eS.shiftedLineIso.hom eS.unitIso.hom _ hh
  simpa only [eS, eP, canonicalEndpoint_shiftedLine, canonicalEndpoint_unit,
    projective, Category.assoc] using hc

end AlgebraicGeometry.Etale.VectorTraceScalar
