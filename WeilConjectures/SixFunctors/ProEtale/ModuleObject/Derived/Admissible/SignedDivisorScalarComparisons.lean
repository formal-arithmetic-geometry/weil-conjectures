/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Derived coefficient change of the signed divisor class

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an,
thm-pur-rank-one-thom.proof.md Step 2 and lem-pur-divisor-class.proof.md (b);
Wei Yang #1441, item 26 (blueprint: def-pur-signed-divisor-scalar-comparisons).
The scalar functor is the ordinary unbounded derived extension, including for
nonflat quotients. The supported class is the published glued frame class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
attribute [local implicit_reducible] CategoryTheory.CommMon.toMon CategoryTheory.Mod.comap
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

variable (P : WeilConjectures.PurityFiniteSetting.{u})
variable {Λ Λ' Λ'' : ScalarSixRing.{u}}

/-- Forget only the bundled commutativity proof, retaining the identical coefficient ring.
Source: the coefficient list (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
abbrev divisorRing (Λ : ScalarSixRing.{u}) : Profinite.CondensedRing.{u} := ⟨Λ.X⟩

/-- The existing pulled-back commutativity instance in the bundled-map presentation.
Source: pulled-back coefficients (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
instance divisorCoefficientComm (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj Γ.toMon.X X) :=
  inferInstanceAs (IsCommMonObj (condensedRingObj Γ.X X))

/-- The specified scalar adjunction applied to a degree-zero semilinear map.
Source: derived scalar unit and counit, Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarAdjunct (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M : Modules (divisorRing Λ) X} {N : Modules (divisorRing Λ') X}
    (s : M ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N) :
    (scalarSixChange a X).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a.hom.hom X)).homEquiv _ _ |>.symm <|
      (DerivedCategory.singleFunctor _ 0).map s ≫
        ((Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategorySingleFunctor 0).inv.app N

/-- The derived adjunct transposes back to the specified semilinear map.
Source: the normalized scalar adjunction in Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: apply the inverse-law of the scalar adjunction Hom equivalence. -/
theorem divisorScalarAdjunct_spec (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M : Modules (divisorRing Λ) X} {N : Modules (divisorRing Λ') X}
    (s : M ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a.hom.hom X)).homEquiv _ _ (divisorScalarAdjunct a X s) =
      (DerivedCategory.singleFunctor _ 0).map s ≫
        ((Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategorySingleFunctor 0).inv.app N :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a.hom.hom X)).homEquiv _ _ |>.apply_symm_apply _

/-- The scalar unit followed by the specified adjunct recovers the semilinear map.
Source: source and root normalization in Steps 1 and 3
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: rewrite the first two factors as the scalar Hom transpose, use its
specification, and cancel the inverse single/restriction comparison. -/
theorem divisorScalarAdjunct_unit (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M : Modules (divisorRing Λ) X} {N : Modules (divisorRing Λ') X}
    (s : M ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a.hom.hom X)).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategory.map
        (divisorScalarAdjunct a X s) ≫
      ((Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor _ 0).map s := by
  dsimp only [divisorRing, CommMon.toMon] at *
  have h := congrArg
    (fun f ↦ f ≫ (Functor.mapDerivedCategorySingleFunctor
      (Mod.comap (coefficientMap a.hom.hom X)) 0).hom.app N)
    (divisorScalarAdjunct_spec a X s)
  simp only [Adjunction.homEquiv_unit, Category.assoc, Iso.inv_hom_id_app] at h
  repeat erw [Category.comp_id] at h
  exact h

/-- Degree-zero semilinear maps are determined by their specified derived adjuncts.
Source: injectivity of the Hom bijections in Step 4
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: apply the scalar Hom equivalence, cancel the single/restriction
comparison, and use faithfulness of the single functor. -/
theorem divisorScalarAdjunct_injective (a : Λ ⟶ Λ') (X : Scheme.{u})
    (M : Modules (divisorRing Λ) X) (N : Modules (divisorRing Λ') X) :
    Function.Injective (divisorScalarAdjunct a X (M := M) (N := N)) := by
  dsimp only [divisorRing, CommMon.toMon] at *
  intro s t h
  have h' := congrArg
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a.hom.hom X)).homEquiv _ _) h
  rw [divisorScalarAdjunct_spec, divisorScalarAdjunct_spec] at h'
  apply (DerivedCategory.singleFunctor (Modules (divisorRing Λ) X) 0).map_injective
  exact (cancel_mono
    (((Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategorySingleFunctor 0).inv.app N)).1 h'

/-- The actual derived adjunct is natural in its degree-zero source.
Source: transposition in Step 4
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: naturality of the inverse Hom equivalence moves the source map through
scalar extension; the single functor preserves its composite. -/
theorem divisorScalarAdjunct_naturality_left (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M M' : Modules (divisorRing Λ) X} {N : Modules (divisorRing Λ') X}
    (f : M ⟶ M') (s : M' ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N) :
    divisorScalarAdjunct a X (f ≫ s) =
      (scalarSixChange a X).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
        divisorScalarAdjunct a X s := by
  dsimp only [divisorRing, CommMon.toMon] at *
  unfold divisorScalarAdjunct
  rw [Functor.map_comp, Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  rfl

/-- The actual derived adjunct is natural in its degree-zero target.
Source: transposition in Step 4
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the single/restriction comparison is natural, so the target map passes
through it; naturality of the inverse scalar Hom equivalence finishes. -/
theorem divisorScalarAdjunct_naturality_right (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M : Modules (divisorRing Λ) X} {N N' : Modules (divisorRing Λ') X}
    (s : M ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N) (f : N ⟶ N') :
    divisorScalarAdjunct a X
        (s ≫ (Mod.comap (coefficientMap a.hom.hom X)).map f) =
      divisorScalarAdjunct a X s ≫ (DerivedCategory.singleFunctor _ 0).map f := by
  dsimp only [divisorRing, CommMon.toMon] at *
  have hn := (Functor.mapDerivedCategorySingleFunctor
    (Mod.comap (coefficientMap a.hom.hom X)) 0).inv.naturality f
  dsimp only [Functor.comp_map] at hn
  unfold divisorScalarAdjunct
  rw [Functor.map_comp, Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  exact Adjunction.homEquiv_naturality_right_symm _ _ _

/-- The scalar/single comparison is computed by the localized cochain counit.
Source: the K-flat representative calculation in Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: transpose the cochain unit with the derived scalar adjunction.  The
unit-counit compatibility at Qh identifies its adjunct with the derived-functor
counit.  Naturality of the restriction/single comparison then gives the result. -/
theorem divisorScalarAdjunct_extendUnit (a : Λ ⟶ Λ') (X : Scheme.{u})
    (M : Modules (divisorRing Λ) X) :
    let φ := coefficientMap a.hom.hom X
    let E := Mod.extendScalars φ
    let K := (CochainComplex.singleFunctor _ 0).obj M
    divisorScalarAdjunct a X ((Mod.extendRestrictAdjunction φ).unit.app M) =
      E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj K) ≫
        DerivedCategory.Q.map ((E.mapCochainComplexSingleFunctor 0).hom.app M) := by
  dsimp only [divisorRing, CommMon.toMon] at *
  let φ := coefficientMap a.hom.hom X
  let E : Modules (divisorRing Λ) X ⥤ Modules (divisorRing Λ') X := Mod.extendScalars φ
  let R : Modules (divisorRing Λ') X ⥤ Modules (divisorRing Λ) X := Mod.comap φ
  let adj := Mod.extendRestrictAdjunction φ
  let dadj := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let K := (CochainComplex.singleFunctor _ 0).obj M
  have hfac : R.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)) =
      R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (Iso.inv_eq_inv
      (R.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)))
      (R.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj K))).2
    change R.mapDerivedCategoryFactorsh.hom.app _ = R.mapDerivedCategoryFactors.hom.app _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change R.mapDerivedCategory.map (𝟙 _) ≫ R.mapDerivedCategoryFactors.hom.app _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  have hε : (dadj.homEquiv _ _).symm
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K)) =
      E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj K) := by
    apply (dadj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    have h := (Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh φ
      ((HomotopyCategory.quotient _ _).obj K)).symm
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
    erw [hfac] at h
    exact h
  rw [← hε]
  erw [← dadj.homEquiv_naturality_right_symm]
  unfold divisorScalarAdjunct
  congr 1
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor _ 0).obj (E.obj M)))).1
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  have hn := R.mapDerivedCategoryFactors.hom.naturality
    ((E.mapCochainComplexSingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, Iso.inv_hom_id_app_assoc]
  let Q := DerivedCategory.Q (C := Modules (divisorRing Λ) X)
  change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1
  ext n : 1
  by_cases hn : n = 0
  · subst n
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq]
    change adj.unit.app M ≫ (𝟙 _ ≫ R.map (𝟙 _)) = adj.unit.app M ≫ R.map (𝟙 _)
    rw [Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_src _ _

/-- Flat source modules compute the scalar/single comparison without a resolution.
Source: the flat-term adjunction of Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the single complex of a flat module is K-flat.  Its derived-functor
counit and the single-complex comparison are therefore both invertible. -/
theorem divisorScalarAdjunct_extendUnit_isIso (a : Λ ⟶ Λ') (X : Scheme.{u})
    (M : Modules (divisorRing Λ) X) (hM : ObjectProperty.flat M) :
    IsIso (divisorScalarAdjunct a X
      ((Mod.extendRestrictAdjunction (coefficientMap a.hom.hom X)).unit.app M)) := by
  rw [divisorScalarAdjunct_extendUnit]
  have hK := (CochainComplex.kFlat_single_obj_iff_flat M 0).2 hM
  let E := Mod.extendScalars (coefficientMap a.hom.hom X)
  let K := (CochainComplex.singleFunctor (Modules (divisorRing Λ) X) 0).obj M
  haveI hc := Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat E K hK
  let e := (E.mapCochainComplexSingleFunctor 0).app M
  haveI he : IsIso ((DerivedCategory.Q (C := Modules (divisorRing Λ') X)).map e.hom) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso

/-- A flat degree-zero source reduces invertibility to the ordinary scalar adjunct.
Source: Steps 1 and 3, flat representatives
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the ordinary adjunction expresses the semilinear map as its unit
followed by restriction of the ordinary adjunct. Derived naturality gives the
same factorization, and the flat scalar/single comparison is invertible. -/
theorem divisorScalarAdjunct_isIso (a : Λ ⟶ Λ') (X : Scheme.{u})
    {M : Modules (divisorRing Λ) X} {N : Modules (divisorRing Λ') X}
    (s : M ⟶ (Mod.comap (coefficientMap a.hom.hom X)).obj N)
    (hM : ObjectProperty.flat M)
    [IsIso (Mod.extendHom (coefficientMap a.hom.hom X) s)] :
    IsIso (divisorScalarAdjunct a X s) := by
  let φ := coefficientMap a.hom.hom X
  have hs : (Mod.extendRestrictAdjunction φ).unit.app M ≫
      (Mod.comap φ).map (Mod.extendHom φ s) = s :=
    (Mod.extendHomEquiv φ _ _).apply_symm_apply s
  rw [← hs, divisorScalarAdjunct_naturality_right]
  haveI := divisorScalarAdjunct_extendUnit_isIso a X M hM
  infer_instance

/-- Multiplication S⊗ᴸ_R R → S, the adjunct of the actual unital coefficient map.
Source: u_D in the statement (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarUnit (a : Λ ⟶ Λ') (X : Scheme.{u}) :=
  divisorScalarAdjunct a X (Mod.comapUnitHom (coefficientMap a.hom.hom X))

/-- Multiplication on the scalar extension of the regular coefficient module is invertible.
Source: the unit comparison in Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the ordinary multiplication adjunct is the invertible monoidal unit
comparison of extension of scalars.  Its derived adjunct is the scalar/single
comparison on the regular module followed by this multiplication in degree
zero.  The regular module is flat, so both factors are isomorphisms, even for
nonflat coefficient maps. -/
theorem divisorScalarUnit_isIso (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    IsIso (divisorScalarUnit a X) := by
  let φ := coefficientMap a.hom.hom X
  let m := Mod.extendHom φ (Mod.comapUnitHom φ)
  haveI hm : IsIso m := by
    have h := Mod.isIso_extendScalarsOplaxMonoidal_η φ
    simpa only [Mod.extendScalarsOplaxMonoidal_η] using h
  have hs : (Mod.extendRestrictAdjunction φ).unit.app (unit (divisorRing Λ) X) ≫
      (Mod.comap φ).map m = Mod.comapUnitHom φ := by
    exact (Mod.extendHomEquiv φ _ _).apply_symm_apply (Mod.comapUnitHom φ)
  unfold divisorScalarUnit
  rw [← hs, divisorScalarAdjunct_naturality_right]
  haveI := divisorScalarAdjunct_extendUnit_isIso a X (unit (divisorRing Λ) X)
    ObjectProperty.flat.prop_unit
  exact inferInstance

set_option maxHeartbeats 2000000 in
-- Elaborating the integral scalar tower compares the native pulled-back ring instances.
/-- The semilinear root map is uniquely fixed on the complete integral root generator.
Source: Step 3; root-normalized Tate comparison of the compatible Kummer boundary
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: both integral coefficient maps are unital continuous maps from Z_l, so
uniqueness of integralMap identifies their composite. Transitivity of ordinary
extension of scalars defines the map on the extended Tate module. Its scalar
adjunction unit equation is exactly the displayed generator equation. Conversely
that adjunction says a semilinear map from this extension is fixed on the integral
module. Thus the specified map exists uniquely, including for ramified extensions
and quotient maps; no finite-reduction detection of derived morphisms is used. -/
theorem divisorRootMap_existsUnique
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    ∃! s : line P (divisorRing Λ) hΛ X ⟶
        (Mod.comap (coefficientMap a.hom.hom X)).obj (line P (divisorRing Λ') hΛ' X),
      rootInsertion P (divisorRing Λ) hΛ X ≫ s.hom =
        rootInsertion P (divisorRing Λ') hΛ' X := by
  let f := integralMap P (divisorRing Λ) hΛ
  let f' := integralMap P (divisorRing Λ') hΛ'
  have hf : f ≫ a.hom = f' :=
    (integralMap_existsUnique P (divisorRing Λ') hΛ').unique trivial trivial
  let φ := coefficientMap f.hom X
  let ψ := coefficientMap a.hom.hom X
  let φ' := coefficientMap f'.hom X
  have hφ : φ' = φ ≫ ψ := by
    change coefficientMap f'.hom X = coefficientMap f.hom X ≫ ψ
    rw [← coefficientMap_comp]
    have hf' : f.hom ≫ a.hom.hom = f'.hom := congrArg Mon.Hom.hom hf
    exact congrArg (fun g ↦ (upperStarFromPoint X).map g) hf'.symm
  let M := tateModule X P.coefficients.l
  let N := line P (divisorRing Λ') hΛ' X
  let t : M ⟶ (Mod.comap φ).obj ((Mod.comap ψ).obj N) :=
    Mod.extendUnit φ' M ≫ (Mod.comapCongr hφ).hom.app N ≫
      (Mod.comapComp φ ψ).hom.app N
  let s := Mod.extendHom φ t
  have hs : rootInsertion P (divisorRing Λ) hΛ X ≫ s.hom =
      rootInsertion P (divisorRing Λ') hΛ' X := by
    change Mod.extendUnitHom φ M ≫ (Mod.extendHom φ t).hom =
      Mod.extendUnitHom φ' M
    rw [Mod.extendUnitHom_extendHom]
    simp only [t, Mod.comp_hom', Mod.extendUnit_hom,
      Mod.comapCongr_hom_app_hom, Mod.comapComp_hom_app_hom]
    change Mod.extendUnitHom φ' M ≫ 𝟙 _ ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.comp_id]
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  apply (Mod.extendHomEquiv φ M ((Mod.comap ψ).obj N)).injective
  apply Mod.hom_ext
  change rootInsertion P (divisorRing Λ) hΛ X ≫ s'.hom =
    rootInsertion P (divisorRing Λ) hΛ X ≫ s.hom
  exact hs'.trans hs.symm

/-- The actual semilinear root comparison, uniquely fixed before passage to D(Λ).
Source: Step 3 (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorRootMap
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :=
  (divisorRootMap_existsUnique P hΛ hΛ' a X).choose

/-- The chosen comparison carries each complete root generator to itself.
Source: Step 3 (blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: this is the defining property in the existence-and-uniqueness theorem. -/
theorem divisorRootMap_spec
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    rootInsertion P (divisorRing Λ) hΛ X ≫ (divisorRootMap P hΛ hΛ' a X).hom =
      rootInsertion P (divisorRing Λ') hΛ' X :=
  (divisorRootMap_existsUnique P hΛ hΛ' a X).choose_spec.1

set_option maxHeartbeats 2000000 in
-- Elaborating the integral scalar tower compares the native pulled-back ring instances.
/-- Identity coefficients preserve the complete root line by the identity map.
Source: Step 6 (blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: identity restriction has identity underlying map and preserves root insertion.
Uniqueness of the generator-normalized comparison identifies it with the chosen map. -/
theorem divisorRootMap_id
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ)) (X : Scheme.{u}) :
    (divisorRootMap P hΛ hΛ (𝟙 Λ) X).hom = 𝟙 _ := by
  let N := line P (divisorRing Λ) hΛ X
  let t : N ⟶ (Mod.comap (coefficientMap (𝟙 Λ : Λ ⟶ Λ).hom.hom X)).obj N :=
    (Mod.comapId (condensedRingObj Λ.X X)).inv.app N ≫
      (Mod.comapCongr (coefficientMap_id (Λ := Λ.X) X).symm).hom.app N
  have ht : rootInsertion P (divisorRing Λ) hΛ X ≫ t.hom =
      rootInsertion P (divisorRing Λ) hΛ X := by
    change rootInsertion P (divisorRing Λ) hΛ X ≫ (𝟙 _ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.comp_id]
  have he := (divisorRootMap_existsUnique P hΛ hΛ (𝟙 Λ) X).unique
    (divisorRootMap_spec P hΛ hΛ (𝟙 Λ) X) ht
  have he' := congrArg Mod.Hom.hom he
  change (divisorRootMap P hΛ hΛ (𝟙 Λ) X).hom = 𝟙 _ ≫ 𝟙 _ at he'
  exact he'.trans (Category.comp_id _)

set_option maxHeartbeats 2000000 in
-- Elaborating the integral scalar tower compares the native pulled-back ring instances.
/-- Composing coefficient maps composes their actual root-generator comparisons.
Source: Step 6 (blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: restriction transitivity has identity underlying map. The composite therefore
preserves the root insertion by the two generator equations. Uniqueness identifies
it with the direct comparison, before passing to the derived category. -/
theorem divisorRootMap_comp
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (hΛ'' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ''))
    (a : Λ ⟶ Λ') (a' : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    (divisorRootMap P hΛ hΛ' a X).hom ≫ (divisorRootMap P hΛ' hΛ'' a' X).hom =
      (divisorRootMap P hΛ hΛ'' (a ≫ a') X).hom := by
  let φ := coefficientMap a.hom.hom X
  let ψ := coefficientMap a'.hom.hom X
  let χ := coefficientMap (a ≫ a').hom.hom X
  have hχ : χ = φ ≫ ψ := coefficientMap_comp a.hom.hom a'.hom.hom X
  let N := line P (divisorRing Λ'') hΛ'' X
  let t : line P (divisorRing Λ) hΛ X ⟶ (Mod.comap χ).obj N :=
    divisorRootMap P hΛ hΛ' a X ≫
      (Mod.comap φ).map (divisorRootMap P hΛ' hΛ'' a' X) ≫
      (Mod.comapComp φ ψ).inv.app N ≫ (Mod.comapCongr hχ.symm).hom.app N
  have ht : rootInsertion P (divisorRing Λ) hΛ X ≫ t.hom =
      rootInsertion P (divisorRing Λ'') hΛ'' X := by
    change rootInsertion P (divisorRing Λ) hΛ X ≫
      ((divisorRootMap P hΛ hΛ' a X).hom ≫
        (divisorRootMap P hΛ' hΛ'' a' X).hom ≫ 𝟙 _ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.comp_id, ← Category.assoc,
      divisorRootMap_spec, divisorRootMap_spec]
  have he := (divisorRootMap_existsUnique P hΛ hΛ'' (a ≫ a') X).unique
    ht (divisorRootMap_spec P hΛ hΛ'' (a ≫ a') X)
  have he' := congrArg Mod.Hom.hom he
  change (divisorRootMap P hΛ hΛ' a X).hom ≫
    (divisorRootMap P hΛ' hΛ'' a' X).hom ≫ 𝟙 _ ≫ 𝟙 _ = _ at he'
  simpa only [Category.comp_id] using he'

set_option maxHeartbeats 2000000 in
/-- Ordinary extension of the Tate line is identified by the root-generator equation.
Source: scalar transitivity in Step 3
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: compose the two extension/restriction adjunctions and identify their
right adjoint with restriction along the unique integral coefficient map.
Uniqueness of left adjoints gives an isomorphism. Its unit equation says that
it preserves the integral root insertion. Uniqueness of divisorRootMap then
identifies its transpose with the specified root map. -/
theorem divisorRootMap_extend_isIso
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    IsIso (Mod.extendHom (coefficientMap a.hom.hom X)
      (divisorRootMap P hΛ hΛ' a X)) := by
  let f := integralMap P (divisorRing Λ) hΛ
  let f' := integralMap P (divisorRing Λ') hΛ'
  have hf : f ≫ a.hom = f' :=
    (integralMap_existsUnique P (divisorRing Λ') hΛ').unique trivial trivial
  let φ := coefficientMap f.hom X
  let ψ := coefficientMap a.hom.hom X
  let φ' := coefficientMap f'.hom X
  have hφ : φ' = φ ≫ ψ := by
    change coefficientMap f'.hom X = coefficientMap f.hom X ≫ ψ
    rw [← coefficientMap_comp]
    have hf' : f.hom ≫ a.hom.hom = f'.hom := congrArg Mon.Hom.hom hf
    exact congrArg (fun g ↦ (upperStarFromPoint X).map g) hf'.symm
  let M := tateModule X P.coefficients.l
  let adj := ((Mod.extendRestrictAdjunction φ).comp
    (Mod.extendRestrictAdjunction ψ)).ofNatIsoRight
      ((Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr hφ.symm)
  let e := adj.leftAdjointUniq (Mod.extendRestrictAdjunction φ')
  let t := (Mod.extendRestrictAdjunction ψ).homEquiv _ _ (e.hom.app M)
  have ht : rootInsertion P (divisorRing Λ) hΛ X ≫ t.hom =
      rootInsertion P (divisorRing Λ') hΛ' X := by
    have h := congrArg Mod.Hom.hom
      (adj.unit_leftAdjointUniq_hom_app (Mod.extendRestrictAdjunction φ') M)
    change Mod.extendUnitHom φ M ≫
      ((Mod.extendRestrictAdjunction ψ).homEquiv _ _ (e.hom.app M)).hom =
        Mod.extendUnitHom φ' M
    simp only [adj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.id_obj, Functor.comp_obj,
      Adjunction.comp_unit_app, Mod.comp_hom', Mod.comap_map_hom,
      Iso.trans_hom, Iso.symm_hom, Mod.comapComp_inv_app_hom,
      Mod.comapCongr_hom_app_hom, Category.comp_id, Category.id_comp, Category.assoc,
      Adjunction.homEquiv_unit, Mod.extendRestrictAdjunction_unit_app_hom] at h
    repeat erw [Category.id_comp] at h
    exact h
  have he := (divisorRootMap_existsUnique P hΛ hΛ' a X).unique
    (divisorRootMap_spec P hΛ hΛ' a X) ht
  have hm : Mod.extendHom ψ (divisorRootMap P hΛ hΛ' a X) = e.hom.app M := by
    rw [he]
    exact (Mod.extendHomEquiv ψ _ _).symm_apply_apply _
  rw [hm]
  infer_instance

private theorem divisor_flat_of_local_unit (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hM : ∀ i : 𝒰.I₀,
      Nonempty (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M ≅ 𝟙_ _)) :
    ObjectProperty.flat M := by
  let F := fun i : 𝒰.I₀ ↦ (ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R
  have hweak (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro A B f hf
    have : IsIso ((Mod.forget R).map f) := by
      apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀
      intro i
      have : IsIso ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
        inferInstanceAs (IsIso ((Mod.forget _).map ((F i).map f)))
      exact (NatIso.isIso_map_iff
        (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) (hweak i)) f.hom).1
          inferInstance
    exact isIso_of_reflects_iso f (Mod.forget R)
  have hcomp (i : 𝒰.I₀) : PreservesFiniteLimits (tensorLeft M ⋙ F i) := by
    obtain ⟨e⟩ := hM i
    have hflat : ObjectProperty.flat ((F i).obj M) :=
      ObjectProperty.prop_of_iso ObjectProperty.flat e.symm
        (ObjectProperty.prop_unit ObjectProperty.flat)
    have := hflat.tensorLeft.preservesFiniteLimits
    exact preservesFiniteLimits_of_natIso (Functor.Monoidal.commTensorLeft (F i) M)
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  constructor
  intro J _ _
  constructor
  intro K
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply hF.jointlyReflectsLimit
  intro i
  exact isLimitOfPreserves (tensorLeft M ⋙ F i) (limit.isLimit K)

/-- The actual root-tower line is flat wherever the coefficient prime is invertible.
Source: compatible primitive roots, Step 3
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: on the compatible primitive-root cover the complete integral Tate module
is the regular module. Exact monoidal inverse images detect flatness on that
cover. Ordinary extension of scalars preserves flat modules. -/
theorem divisorLine_flat
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (X : Scheme.{u}) [∀ x : X, Invertible (P.coefficients.l : X.residueField x)] :
    ObjectProperty.flat (line P (divisorRing Λ) hΛ X) := by
  have hInv : IsUnit (P.coefficients.l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (P.coefficients.l : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (P.coefficients.l : X.residueField x)
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial X P.coefficients.l hInv
  have hT : ObjectProperty.flat (tateModule X P.coefficients.l) :=
    divisor_flat_of_local_unit X _ _ 𝒰 h𝒰
  exact (Mod.extendScalars_preservesFlat
    (coefficientMap (integralMap P (divisorRing Λ) hΛ).hom X)).flat_obj hT

/-- The canonical derived root comparison; its source line is locally free, so
this adjunct is an isomorphism even for a nonflat map.
Source: l_1 in Step 3 (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarLine
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :=
  divisorScalarAdjunct a X (divisorRootMap P hΛ hΛ' a X)

/-- Derived scalar extension preserves the specified root-normalized Tate line.
Source: Step 3 (blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the line is flat and its ordinary root adjunct is an isomorphism;
apply the scalar/single comparison for a flat source. -/
theorem divisorScalarLine_isIso
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u})
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)] :
    IsIso (divisorScalarLine P hΛ hΛ' a X) := by
  haveI := divisorRootMap_extend_isIso P hΛ hΛ' a X
  exact divisorScalarAdjunct_isIso a X _ (divisorLine_flat P hΛ X)

/-- Include the canonical scalar/shift comparison in l_T.
Source: the displayed l_T (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarTarget
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :=
  let adj : scalarSixChange a X ⊣
      (Mod.comap (coefficientMap a.hom.hom X)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a.hom.hom X)
  letI := adj.leftAdjointCommShift ℤ
  (Functor.commShiftIso (scalarSixChange a X) (2 : ℤ)).hom.app _ ≫
    (divisorScalarLine P hΛ hΛ' a X) ⟦(2 : ℤ)⟧'

/-- The shifted root comparison is invertible, including for nonflat quotient maps.
Source: Step 3 (blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the canonical scalar/shift comparison and the shift of the root-line
comparison are both isomorphisms. -/
theorem divisorScalarTarget_isIso
    (hΛ : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ))
    (hΛ' : IsAdmissibleCoefficientFor P.coefficients (divisorRing Λ'))
    (a : Λ ⟶ Λ') (X : Scheme.{u})
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)] :
    IsIso (divisorScalarTarget P hΛ hΛ' a X) := by
  haveI := divisorScalarLine_isIso P hΛ hΛ' a X
  unfold divisorScalarTarget
  infer_instance

/-- The supported semilinear unit, with the actual direct-image restriction comparison.
Source: Step 1, the supported coefficient-one map
(blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorSourceUnit (a : Λ ⟶ Λ') {D X : Scheme.{u}} (i : D ⟶ X) :
    source (divisorRing Λ) i ⟶
      (Mod.comap (coefficientMap a.hom.hom X)).obj (source (divisorRing Λ') i) :=
  (CondensedRing.lowerStar Λ.X i).map (Mod.comapUnitHom (coefficientMap a.hom.hom D)) ≫
    (CondensedRing.comapLowerStarIso a.hom.hom i).inv.app (unit (divisorRing Λ') D)

/-- The supported semilinear source map is the direct image of the coefficient map.
Source: supported-one normalization in Step 1
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: restriction of scalars and its direct-image comparison are identities
on underlying sheaves.  The regular-module unit has underlying map the ring map. -/
theorem divisorSourceUnit_hom (a : Λ ⟶ Λ') {D X : Scheme.{u}} (i : D ⟶ X) :
    (divisorSourceUnit a i).hom =
      (ProEtale.lowerStar Ab.{u + 1} i).map (coefficientMap a.hom.hom D) := by
  dsimp only [divisorRing, CommMon.toMon] at *
  unfold divisorSourceUnit
  erw [Mod.comp_hom', CondensedRing.comapLowerStarIso_inv_app_hom,
    Category.comp_id]
  rfl

/-- Supported one is unchanged by identity coefficients.
Source: the identity case in Step 6
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the coefficient map is the identity, and direct image preserves it. -/
theorem divisorSourceUnit_id {D X : Scheme.{u}} (i : D ⟶ X) :
    (divisorSourceUnit (𝟙 Λ) i).hom = 𝟙 _ := by
  dsimp only [divisorRing, CommMon.toMon] at *
  rw [divisorSourceUnit_hom]
  change (ProEtale.lowerStar Ab.{u + 1} i).map (coefficientMap (𝟙 Λ.X) D) = 𝟙 _
  rw [coefficientMap_id]
  exact (ProEtale.lowerStar Ab.{u + 1} i).map_id _

/-- The supported semilinear source maps compose before passing to derived categories.
Source: supported-one composition in Step 6
(blueprint: def-pur-signed-divisor-scalar-comparisons).
Proof: the coefficient maps compose and direct image preserves composition. -/
theorem divisorSourceUnit_comp (a : Λ ⟶ Λ') (a' : Λ' ⟶ Λ'')
    {D X : Scheme.{u}} (i : D ⟶ X) :
    (divisorSourceUnit a i).hom ≫ (divisorSourceUnit a' i).hom =
      (divisorSourceUnit (a ≫ a') i).hom := by
  dsimp only [divisorRing, CommMon.toMon] at *
  rw [divisorSourceUnit_hom, divisorSourceUnit_hom, divisorSourceUnit_hom]
  change (ProEtale.lowerStar Ab.{u + 1} i).map (coefficientMap a.hom.hom D) ≫
      (ProEtale.lowerStar Ab.{u + 1} i).map (coefficientMap a'.hom.hom D) =
    (ProEtale.lowerStar Ab.{u + 1} i).map
      (coefficientMap (a.hom.hom ≫ a'.hom.hom) D)
  rw [coefficientMap_comp, Functor.map_comp]

/-- The supported scalar map, normalized by its actual coefficient-one adjunct.
Source: a_i, Step 1 (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarSource (a : Λ ⟶ Λ') {D X : Scheme.{u}} (i : D ⟶ X) :=
  divisorScalarAdjunct a X (divisorSourceUnit a i)

/-- Exact closed direct image identifies i_*Λ[0] with Ri_*(Λ[0]).
This is the canonical derived-functor localization comparison.
Source: the closed source of a_i (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorClosedIso (Λ : ScalarSixRing.{u}) {D X : Scheme.{u}}
    [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i] :
    (RootCoordinateFace.lower Λ.X i).obj
        ((DerivedCategory.singleFunctor _ 0).obj (unit (divisorRing Λ) D)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (source (divisorRing Λ) i) :=
  letI := CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite Λ.X i
  (CondensedRing.lowerStar Λ.X i).singleFunctorCompRightDerivedFunctorIso.app _

/-- The coefficient identity comparison is the conjugate of the identity restriction.
Source: identity scalars in Step 6 (blueprint: def-pur-signed-divisor-scalar-comparisons). -/
def divisorScalarIdentity (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    scalarSixChange (𝟙 Λ) X ≅ 𝟭 (DerivedCategory (Modules (divisorRing Λ) X)) :=
  (conjugateIsoEquiv (Adjunction.id :
      𝟭 (DerivedCategory (Modules (divisorRing Λ) X)) ⊣ 𝟭 _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 Λ.X) X))).symm
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_id (Λ := Λ.X) X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapId _) ≪≫ Functor.mapDerivedCategoryIdIso _).symm


end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
