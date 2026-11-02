/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The consecutive-quotient Tor sheaf of a constant perfect complex

For a perfect complex `C` over the valuation ring `A`, the degree-`q` cohomology of the
`n+1`-st reduction of its constant realization is the constant sheaf of the module
`M = H^q(C ⊗ A/π^{n+2})`, and the consecutive-quotient Tor sheaf of a constant sheaf is
the constant sheaf of the module-level Tor. A torsion summand `N₀` of `H^q(C)` is a retract
of `M`, which gives the surjection onto `N₀/πN₀`.

Source: Bhatt--Scholze, Proposition 6.6.11; step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

section Module

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ)

/-- The module-level consecutive-quotient Tor: the degree `-1` homology of a projective
resolution of an `A/I^{n+2}`-module, reduced to `A/I^{n+1}`. -/
def levelTor (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) :
    ModuleCat.{u + 1} (A ⧸ I ^ (n + 1)) :=
  (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.factorPowSucc I (n + 1))).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResolution M).cochainComplex).homology (-1)


/-- If `I^m` kills `N₀`, the unit `N₀ → A/I^m ⊗ N₀` has a retraction. -/
theorem exists_unit_retraction (m : ℕ) (N₀ : ModuleCat.{u + 1} A)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ μ : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk (I ^ m))).obj N₀) ⟶ N₀,
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ m))).unit.app N₀ ≫ μ = 𝟙 N₀ := by
  let f := Ideal.Quotient.mk (I ^ m)
  let L : A ⧸ I ^ m →+* Module.End A N₀ :=
    Ideal.Quotient.lift (I ^ m) (algebraMap A (Module.End A N₀)) (fun a ha ↦ by
      ext x
      simp [hk a ha x])
  let L' : (ModuleCat.restrictScalars f).obj (ModuleCat.of (A ⧸ I ^ m) (A ⧸ I ^ m)) →ₗ[A]
      Module.End A N₀ :=
    { toFun := fun s ↦ L s
      map_add' := fun s t ↦ L.map_add s t
      map_smul' := fun a s ↦ by
        change L (f a * (show A ⧸ I ^ m from s)) = algebraMap A (Module.End A N₀) a * L s
        rw [map_mul]
        rfl }
  let T := TensorProduct.lift L'
  let E := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj N₀
  have key (s : A ⧸ I ^ m) (t : E) : T (s • t) = L s (T t) := by
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul']
      simp only [T, TensorProduct.lift.tmul]
      change L (s * (show A ⧸ I ^ m from s')) x = L s (L s' x)
      rw [map_mul]
      rfl
    | add t₁ t₂ h₁ h₂ =>
      rw [smul_add, map_add, map_add, h₁, h₂, map_add]
  refine ⟨ModuleCat.ofHom (X := (ModuleCat.restrictScalars f).obj E) (Y := N₀)
    { toFun := fun t ↦ T t
      map_add' := fun s t ↦ map_add T s t
      map_smul' := fun a t ↦ key (f a) t }, ?_⟩
  ext x
  change T ((1 : A ⧸ I ^ m) ⊗ₜ x) = x
  simp [T, L', L]

/-- Over a principal ideal domain, the cycles of a complex of finite projective modules are a
direct summand of each term. -/
theorem exists_cycles_retraction [IsDomain A] [IsPrincipalIdealRing A]
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ) :
    ∃ ρ : P.X q ⟶ P.cycles q, P.iCycles q ≫ ρ = 𝟙 _ := by
  let d := (P.d q (q + 1)).hom
  have := (hP (q + 1)).1
  have := (hP (q + 1)).2
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  let τ : P.X q ⟶ P.X q := ModuleCat.ofHom (LinearMap.id - σ.comp d.rangeRestrict)
  have hdσ (y : LinearMap.range d) : d (σ y) = y := by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  have hτ : τ ≫ P.d q (q + 1) = 0 := by
    ext x
    change d (x - σ (d.rangeRestrict x)) = 0
    rw [map_sub, hdσ]
    simp
  refine ⟨P.liftCycles τ (q + 1) (by simp) hτ, ?_⟩
  rw [← cancel_mono (P.iCycles q), Category.assoc, HomologicalComplex.liftCycles_i,
    Category.id_comp]
  ext x
  change P.iCycles q x - σ (d.rangeRestrict (P.iCycles q x)) = P.iCycles q x
  have h0 : d.rangeRestrict (P.iCycles q x) = 0 := by
    apply Subtype.ext
    change (P.iCycles q ≫ P.d q (q + 1)) x = 0
    simp
  rw [h0, map_zero, sub_zero]


/-- Universal coefficients over a principal ideal domain, split form: a direct summand `N₀`
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)`, for a bounded complex of
finite projective modules `P`. -/
theorem exists_homology_reduction_retraction [IsDomain A] [IsPrincipalIdealRing A] (m : ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ)
    (F N₀ : ModuleCat.{u + 1} A) (ε : P.homology q ≅ F ⊞ N₀)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q))
      (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q) →ₗ[A]
          N₀), ∀ x, r (s x) = x := by
  let f := Ideal.Quotient.mk (I ^ m)
  let Ext := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f
  let Res := ModuleCat.restrictScalars.{u + 1} f
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f
  have : Ext.Additive := adj.left_adjoint_additive
  have : Res.Additive := adj.right_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} Res := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits Res := PreservesLimitsOfSize.preservesFiniteLimits Res
  have : PreservesColimitsOfSize.{0, 0} Res :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Res := PreservesColimitsOfSize.preservesFiniteColimits Res
  let Pb := (Ext.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨ρ, hρ⟩ := exists_cycles_retraction P hP q
  obtain ⟨μ, hμ⟩ := exists_unit_retraction I m N₀ hk
  let ψ : P.X q ⟶ N₀ := ρ ≫ P.homologyπ q ≫ ε.hom ≫ biprod.snd
  let u : P ⟶ (Res.mapHomologicalComplex (.up ℤ)).obj Pb :=
    { f i := adj.unit.app (P.X i)
      comm' i j _ := (adj.unit.naturality (P.d i j)) }
  let g : Pb ⟶ (HomologicalComplex.single _ (.up ℤ) q).obj (Ext.obj N₀) :=
    HomologicalComplex.mkHomToSingle (Ext.map ψ) (by
      intro i _
      change Ext.map (P.d i q) ≫ Ext.map ψ = 0
      rw [← Ext.map_comp]
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp, Ext.map_zero])
  let g' : (Res.mapHomologicalComplex (.up ℤ)).obj Pb ⟶
      (HomologicalComplex.single _ (.up ℤ) q).obj (Res.obj (Ext.obj N₀)) :=
    (Res.mapHomologicalComplex (.up ℤ)).map g ≫
    (HomologicalComplex.singleMapHomologicalComplex Res (.up ℤ) q).hom.app (Ext.obj N₀)
  let eH := (Res.mapHomologicalComplexHomologyIso (.up ℤ) q).app Pb
  let s : N₀ ⟶ Res.obj (Pb.homology q) :=
    biprod.inr ≫ ε.inv ≫ HomologicalComplex.homologyMap u q ≫ eH.hom
  let r : Res.obj (Pb.homology q) ⟶ N₀ := eH.inv ≫ HomologicalComplex.homologyMap g' q ≫
    (HomologicalComplex.singleObjHomologySelfIso _ q _).hom ≫ μ
  have hug : u ≫ g' = HomologicalComplex.mkHomToSingle (ψ ≫ adj.unit.app N₀) (by
      intro i _
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp]) := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mkHomToSingle_f, Functor.map_comp,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.map_inv_hom_id_assoc, Functor.comp_obj, u, g', g]
    exact adj.unit_naturality_assoc ψ _
  have hπ : HomologicalComplex.homologyMap (u ≫ g') q ≫
      (HomologicalComplex.singleObjHomologySelfIso _ q _).hom =
        ε.hom ≫ biprod.snd ≫ adj.unit.app N₀ := by
    rw [← cancel_epi (P.homologyπ q), hug, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc,
      HomologicalComplex.mkHomToSingle_f]
    simp [ψ, reassoc_of% hρ]
  have key : s ≫ r = 𝟙 N₀ := by
    simp only [s, r, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← HomologicalComplex.homologyMap_comp_assoc, reassoc_of% hπ, ε.inv_hom_id_assoc,
      biprod.inr_snd_assoc, hμ]
  exact ⟨s.hom, r.hom, fun x ↦ congrArg (fun φ ↦ φ.hom x) key⟩

/-- The module-level consecutive-quotient Tor of a module containing a retract `N₀` killed
by `π^{n+1}` surjects onto `N₀/πN₀`. -/
theorem exists_levelTor_epi [IsDomain A] (π : A) (hπ : π ≠ 0) (hI : I = Ideal.span {π})
    (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) (N₀ : ModuleCat.{u + 1} A)
    (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M)
    (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M →ₗ[A] N₀)
    (hrs : ∀ x, r (s x) = x) (hk : ∀ x : N₀, π ^ (n + 1) • x = 0) :
    ∃ t : levelTor I n M ⟶ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ (n + 1)))).obj
          (cokernel (ModuleCat.ofHom (π • LinearMap.id : N₀ →ₗ[A] N₀))), Epi t := by
  sorry

end Module

section Sheaf

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

omit [CommRing A] in
/-- The constant module sheaf functor is exact. -/
theorem adicLisseConstantModules_exact (B : Type (u + 1)) [CommRing B] :
    PreservesFiniteLimits (adicLisseConstantModules T B) ∧
      PreservesFiniteColimits (adicLisseConstantModules T B) :=
  CompletedConstantReduction.constant_exact T B

/-- The cohomology of a finite reduction of the constant realization of a perfect complex is
the constant sheaf of the cohomology of the reduced complex. -/
theorem nonempty_reduction_homology_iso (q : ℤ)
    (C : completedConstantDerived (ModuleCat.{u + 1} A))
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ) (_ha : P.IsStrictlyGE a)
    (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i))
    (e : C ≅ (completedConstantQ (ModuleCat.{u + 1} A)).obj P) (n : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T d n).obj ((integralConstantDerived T d).obj C)) ≅
      (pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
        ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj
          ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).mapHomologicalComplex (.up ℤ)).obj
              P).homology q))) := by
  classical
  let := hb
  let F := adicLisseConstantModules T A
  have : F.Additive := CompletedConstantReduction.constant_additive T A
  let c := CompletedConstantReduction.base T d.ideal ≫ (pbcCompletedComparison T d).hom
  let C₀ := (CompletedConstantReduction.constantComplex T A).obj P
  have : IsIso (pbcComplexCounit c C₀) := by
    have := pbcExtensionCounit_isIso c C₀ (constant_kflat T P b (fun q ↦ (hP q).1))
    dsimp only [pbcComplexCounit]
    infer_instance
  let e₁ : (integralConstantDerived T d).obj C ≅
      (pbcDerivedExtend c).obj (DerivedCategory.Q.obj C₀) :=
    (integralConstantDerived T d).mapIso e ≪≫
      (integralRealizationFactors T d).app P ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (ordinaryConstantModel T d) (.up ℤ)).app P) ≪≫
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ pbcExtend c)) (.up ℤ)).app P)).symm ≪≫
      (asIso (pbcComplexCounit c C₀)).symm
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  let p := pbcAdicProjection T d n
  let j := pbcLevelConstantComparison T d n
  let qq := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let β := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom qq)
  have hcp : c ≫ p = β ≫ j.hom := by
    dsimp [c, p, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    have hb₀ := (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 n
    change CompletedConstantReduction.base T d.ideal ≫ _ = _ at hb₀
    rw [hb₀]
    rfl
  have hcpj : c ≫ p ≫ j.inv = β := by
    rw [← Category.assoc, hcp, Category.assoc, j.hom_inv_id, Category.comp_id]
  let C₁ := DerivedCategory.Q.obj C₀
  let eglobal := (restrictIsoAsExtend j).app _ ≪≫
    (pbcDerivedExtend j.inv).mapIso (pbcReductionNormalization c p (c ≫ p) rfl C₁) ≪≫
    pbcReductionNormalization (c ≫ p) j.inv β hcpj C₁ ≪≫
    constantTensorIso T qq P b (fun i ↦ (hP i).1)
  let Fn := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))
  have : Fn.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fn := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fn := (CompletedConstantReduction.constant_exact T _).2
  let P' := ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} qq).mapHomologicalComplex
    (.up ℤ)).obj P
  let X := (pbcCompletedReduction T d n).obj ((integralConstantDerived T d).obj C)
  let eX : (pbcDerivedRestrict j.hom).obj X ≅ DerivedCategory.Q.obj (Fn.mapHomologicalComplex
      (.up ℤ) |>.obj P') :=
    (pbcDerivedRestrict j.hom).mapIso ((pbcDerivedExtend p).mapIso e₁) ≪≫ eglobal
  let eq := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j)
  let eH : (pbcRestrict j.hom).obj ((DerivedCategory.homologyFunctor _ q).obj X) ≅
      Fn.obj (P'.homology q) :=
    ((pbcRestrict j.hom).mapDerivedCategoryHomologyFunctorIso q).app X ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eX ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (Fn.mapHomologicalComplexHomologyIso (.up ℤ) q).app P'
  exact ⟨eq.unitIso.app _ ≪≫ (pbcRestrict j.inv).mapIso eH⟩

/-- The consecutive-quotient Tor sheaf of a constant sheaf is the constant sheaf of the
module-level Tor. -/
theorem nonempty_tor_constant_iso (n : ℕ) (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1 + 1))) :
    Nonempty ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((pbcRestrict (pbcLevelConstantComparison T d (n + 1)).inv).obj
              ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1 + 1))).obj M)))) ≅
      (pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
        ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj (levelTor d.ideal n M))) := by
  classical
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).left_adjoint_additive
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))
  let j₁ := pbcLevelConstantComparison T d (n + 1)
  let j := pbcLevelConstantComparison T d n
  let quot := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let β := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  have hβ : (adicLisseRingSystem T d.ideal).map (homOfLE (Nat.le_succ n)).op = β :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  have hq : quot ≫ j.inv = j₁.inv ≫ β := by
    have h := pbcConstantSystemComparison_naturality T d (homOfLE (Nat.le_succ n)).op
    rw [hβ] at h
    change β ≫ j.hom = j₁.hom ≫ quot at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, j.hom_inv_id,
      Category.comp_id]
  let Fm := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1 + 1))
  have : Fm.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fm := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fm := (CompletedConstantReduction.constant_exact T _).2
  let Fn := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))
  have : Fn.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fn := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fn := (CompletedConstantReduction.constant_exact T _).2
  let R := projectiveResolution M
  have hR (i : ℤ) : Module.Projective (A ⧸ d.ideal ^ (n + 1 + 1)) (R.cochainComplex.X i) :=
    (IsProjective.iff_projective _).2 (inferInstanceAs (Projective (R.cochainComplex.X i)))
  let eq₁ := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j₁)
  let eq := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j)
  let X := (DerivedCategory.singleFunctor _ 0).obj ((pbcRestrict j₁.inv).obj (Fm.obj M))
  let eS : (DerivedCategory.singleFunctor _ 0).obj M ≅
      DerivedCategory.Q.obj R.cochainComplex :=
    (asIso (DerivedCategory.Q.map R.π')).symm
  let e₁ : (pbcDerivedRestrict j₁.hom).obj X ≅
      DerivedCategory.Q.obj (Fm.mapHomologicalComplex (.up ℤ) |>.obj R.cochainComplex) :=
    ((pbcRestrict j₁.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (eq₁.counitIso.app _) ≪≫
      ((Fm.mapDerivedCategorySingleFunctor 0).app M).symm ≪≫
      Fm.mapDerivedCategory.mapIso eS ≪≫ Fm.mapDerivedCategoryFactors.app _
  let Z := (pbcDerivedExtend quot).obj X
  let eZ : (pbcDerivedRestrict j.hom).obj Z ≅ DerivedCategory.Q.obj
      (Fn.mapHomologicalComplex (.up ℤ) |>.obj (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).mapHomologicalComplex (.up ℤ)).obj
          R.cochainComplex)) :=
    (restrictIsoAsExtend j).app Z ≪≫
      pbcReductionNormalization quot j.inv (j₁.inv ≫ β) hq X ≪≫
      (pbcReductionNormalization j₁.inv β (j₁.inv ≫ β) rfl X).symm ≪≫
      (pbcDerivedExtend β).mapIso (((restrictIsoAsExtend j₁).app X).symm ≪≫ e₁) ≪≫
      constantTensorIso T (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) R.cochainComplex 0 hR
  let eH : (pbcRestrict j.hom).obj ((DerivedCategory.homologyFunctor _ (-1)).obj Z) ≅
      Fn.obj (levelTor d.ideal n M) :=
    ((pbcRestrict j.hom).mapDerivedCategoryHomologyFunctorIso (-1)).app Z ≪≫
      (DerivedCategory.homologyFunctor _ (-1)).mapIso eZ ≪≫
      (DerivedCategory.homologyFunctorFactors _ (-1)).app _ ≪≫
      (Fn.mapHomologicalComplexHomologyIso (.up ℤ) (-1)).app _
  exact ⟨eq.unitIso.app _ ≪≫ (pbcRestrict j.inv).mapIso eH⟩

/-- Restricting the constant sheaf of `A/I^{n+1} ⊗ X` to the completed coefficients gives
the completed realization of `X`, when `I^{n+1}` kills `X`. -/
theorem nonempty_restrict_level_constant_iso (n : ℕ) (X : ModuleCat.{u + 1} A)
    (hX : ∀ a ∈ d.ideal ^ (n + 1), ∀ x : X, a • x = 0) :
    Nonempty ((pbcRestrict (pbcAdicProjection T d n)).obj
        ((pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
          ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj
            ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
              (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj X))) ≅
      (integralConstantModule T d).obj X) := by
  sorry

end Sheaf

end AlgebraicGeometry.Scheme
