/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullModuleKFlat
import all WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
import all WeilConjectures.AlgebraicGeometry.Rational.RationalOrdinaryPullbackComposition
import WeilConjectures.AlgebraicGeometry.Adic.ReductionDerivedChangeCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp
public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-! # Computation of ordinary and derived rational ringed pullback

Derived rational pullback is computed termwise on every complex, and derived scalar extension
on K-flat complexes, by natural computation counits. Maps out of ordinary rational pullbacks
and scalar extensions are detected on unit generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

section ScalarCounit

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- The computation counit of derived scalar extension is natural in the complex. -/
theorem pbcComplexCounit_naturality {P P' : CochainComplex (pbcModules T R) ℤ} (p : P' ⟶ P) :
    (pbcDerivedExtend φ).map (DerivedCategory.Q.map p) ≫ pbcComplexCounit φ P =
      pbcComplexCounit φ P' ≫
        DerivedCategory.Q.map (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map p) :=
  reductionScalarComplexCounit_naturality T φ p

/-- Derived scalar extension is computed termwise on K-flat complexes. -/
theorem pbcComplexCounit_isIso (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology T) (R := R) P) :
    IsIso (pbcComplexCounit φ P) := by
  have := pbcExtensionCounit_isIso φ P hP
  unfold pbcComplexCounit
  infer_instance

/-- Every derived object is the localization of a K-flat complex. -/
theorem pbcDerived_exists_kFlat (K : DerivedCategory (pbcModules T R)) :
    ∃ P : CochainComplex (pbcModules T R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology T) (R := R) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨P, s, hP, -, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

variable {B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : S ⟶ B) (χ : R ⟶ B)
  (w : φ ≫ ψ = χ)

/-- The derived coefficient associator is the ordinary balancing map on computation counits. -/
theorem pbcReductionNormalization_counit (P : CochainComplex (pbcModules T R) ℤ) :
    (pbcReductionNormalization φ ψ χ w (DerivedCategory.Q.obj P)).hom ≫
        pbcComplexCounit χ P =
      (pbcDerivedExtend ψ).map (pbcComplexCounit φ P) ≫
        pbcComplexCounit ψ (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (WeilConjectures.FdIntegralScalarForward.pbcExtendComp φ ψ χ w) (.up ℤ)).hom.app P) := by
  rw [pbcReductionNormalization_hom_eq]
  exact scalarAssociatorNormalization T φ ψ χ w P

/-- The derived coefficient associator is natural. -/
theorem pbcReductionNormalization_naturality {K K' : DerivedCategory (pbcModules T R)}
    (f : K ⟶ K') :
    (pbcDerivedExtend ψ).map ((pbcDerivedExtend φ).map f) ≫
        (pbcReductionNormalization φ ψ χ w K').hom =
      (pbcReductionNormalization φ ψ χ w K).hom ≫ (pbcDerivedExtend χ).map f := by
  rw [pbcReductionNormalization_hom_eq, pbcReductionNormalization_hom_eq]
  exact (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
    (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
    (pbcDerivedRestrictComp φ ψ χ w)).hom.naturality f

end ScalarCounit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The tensor-unit section of ordinary rational pullback on a pulled-back chart. -/
def rationalCoherenceUnit {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (M : pbcModules T (rationalCoefficientSheaf l T E))
    (V : T.ProEt) (m : M.val.obj (op V)) :
    ((rationalPullModule l E g c).obj M).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  pbcTensorSection c
    ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
    (op ((proEtaleBaseChange g).obj V)) 1
    (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)

/-- Pull a rational coefficient section through the ring adjunction unit and structure map. -/
def rationalCoherenceScalar {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
    (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
  c.hom.app (op ((proEtaleBaseChange g).obj V))
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
      (rationalCoefficientSheaf l T E)).hom.app (op V) e)

/-- Scalar multiplication on the rational module at a chart, with explicit section types. -/
def rationalCoherenceSmul (T : Scheme.{u})
    (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
    (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
  e • m

attribute [irreducible] rationalCoherenceUnit rationalCoherenceScalar rationalCoherenceSmul

section PullCounit

variable {S T : Scheme.{u}} (g : S ⟶ T)
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)

/-- The computation counit of derived rational pullback is natural in the complex. -/
theorem rationalPullComplexCounit_naturality
    {P P' : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ} (p : P' ⟶ P) :
    (rationalPullDerived l E g c).map (DerivedCategory.Q.map p) ≫
        rationalPullComplexCounit l E g c P =
      rationalPullComplexCounit l E g c P' ≫
        DerivedCategory.Q.map (((rationalPullModule l E g c).mapHomologicalComplex
          (.up ℤ)).map p) := by
  have h := (proEtaleRingDerivedPullbackFactors g (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)).hom.naturality p
  dsimp only [Functor.comp_map] at h
  dsimp only [rationalPullDerived, rationalPullComplexCounit, Functor.comp_map]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc, pbcComplexCounit_naturality]
  simp only [Category.assoc]
  rfl

/-- Derived rational pullback along a normalized coefficient map is computed termwise on every
complex. -/
theorem rationalPullComplexCounit_isIso (hc : rationalCoefficientRestrictionNormalized l E g c)
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ) :
    IsIso (rationalPullComplexCounit l E g c P) := by
  have : IsIso c := (ordinaryCoefficient_eq l E g c hc).symm ▸ inferInstance
  have hExact := rationalPullExtendExact c
  let := hExact.1
  let := hExact.2
  unfold rationalPullComplexCounit
  rw [← rationalPullScalarFactors_app]
  infer_instance

/-- Ordinary rational pullback preserves K-flat complexes. -/
theorem rationalPullModule_isKFlat
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology T)
      (R := rationalCoefficientSheaf l T E) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology S)
      (R := rationalCoefficientSheaf l S E)
      (((rationalPullModule l E g c).mapHomologicalComplex (.up ℤ)).obj P) :=
  proEtaleRingModulePullback_extend_isKFlat g _ c P hP

/-- The adjunction of ordinary rational pullback: inverse image followed by scalar extension. -/
abbrev rationalPullModuleAdjunction :=
  (proEtaleRingModuleAdjunction g (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)).comp (pbcScalarAdjunction c)

/-- The ordinary pullback adjunction has the generator `1 ⊗ m` as its unit. -/
theorem rationalPullModule_unit (M : pbcModules T (rationalCoefficientSheaf l T E))
    (V : T.ProEt) (m : M.val.obj (op V)) :
    ((rationalPullModuleAdjunction l E g c).unit.app M).val.app (op V) m =
      rationalCoherenceUnit l E g c M V m := by
  change ((pbcScalarAdjunction c).unit.app _).val.app
      (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).unit.app M).val.app (op V) m) = _
  rw [proEtaleRingModuleAdjunction_normalized g (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _),
    WeilConjectures.FdIntegralScalarForward.pbcScalarAdjunction_unit]
  unfold rationalCoherenceUnit
  rfl

/-- Maps out of an ordinary rational pullback are detected on unit generators. -/
theorem rationalPullModule_hom_ext (M : pbcModules T (rationalCoefficientSheaf l T E))
    {N : pbcModules S (rationalCoefficientSheaf l S E)}
    (a b : (rationalPullModule l E g c).obj M ⟶ N)
    (h : ∀ (V : T.ProEt) (m : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange g).obj V)) (rationalCoherenceUnit l E g c M V m) =
        b.val.app (op ((proEtaleBaseChange g).obj V)) (rationalCoherenceUnit l E g c M V m)) :
    a = b := by
  apply ((rationalPullModuleAdjunction l E g c).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app (op ((proEtaleBaseChange g).obj V.unop))
      (((rationalPullModuleAdjunction l E g c).unit.app M).val.app V m) =
    b.val.app (op ((proEtaleBaseChange g).obj V.unop))
      (((rationalPullModuleAdjunction l E g c).unit.app M).val.app V m)
  rw [rationalPullModule_unit]
  exact h V.unop m

/-- Ordinary rational pullback sends unit generators to unit generators. -/
theorem rationalPullModule_map_unit {M M' : pbcModules T (rationalCoefficientSheaf l T E)}
    (f : M ⟶ M') (V : T.ProEt) (m : M.val.obj (op V)) :
    ((rationalPullModule l E g c).map f).val.app (op ((proEtaleBaseChange g).obj V))
        (rationalCoherenceUnit l E g c M V m) =
      rationalCoherenceUnit l E g c M' V (f.val.app (op V) m) := by
  have h := congrArg (fun q ↦ q.val.app (op V) m)
    ((rationalPullModuleAdjunction l E g c).unit.naturality f)
  change ((rationalPullModuleAdjunction l E g c).unit.app M').val.app (op V)
      (f.val.app (op V) m) =
    ((rationalPullModule l E g c).map f).val.app (op ((proEtaleBaseChange g).obj V))
      (((rationalPullModuleAdjunction l E g c).unit.app M).val.app (op V) m) at h
  rw [rationalPullModule_unit, rationalPullModule_unit] at h
  exact h.symm

end PullCounit

section Tensor

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- Unit tensors are compatible with restriction. -/
theorem pbcTensorSection_restrict (M : pbcModules T R) {U U' : T.ProEtᵒᵖ} (r : U ⟶ U')
    (x : M.val.obj U) :
    ((pbcExtend φ).obj M).val.map r (pbcTensorSection φ M U 1 x) =
      pbcTensorSection φ M U' 1 (M.val.map r x) := by
  rw [← WeilConjectures.FdIntegralScalarForward.pbcScalarAdjunction_unit,
    ← WeilConjectures.FdIntegralScalarForward.pbcScalarAdjunction_unit]
  exact (PresheafOfModules.naturality_apply ((pbcScalarAdjunction φ).unit.app M).val r x).symm

end Tensor

end AlgebraicGeometry.Scheme
