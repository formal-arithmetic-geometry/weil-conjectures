/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.PointFiberTensorSystem
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
public import Mathlib.Topology.Algebra.Ring.Compact
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativePointTensor.NativePointScalarNormalization

/-! # Native condensed point fibres preserve derived tensor

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
compact-support specialization to Spec k, finite reduction and scalar extension
(blueprint: lem-sf-point-fibre-derived-tensor).

All maps use the ordinary unbounded module-derived categories. The tensor comparison
is the existing normalized section cup; the coherence assertions are restricted to
bounded constructible inputs of finite Tor amplitude. Scalar comparisons are normalized
on flat-term K-flat representatives, including the sheafification unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local instance] Mod.extendScalarsMonoidal
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor

/-- Exactly the four native coefficient forms, with every positive uniformizer exponent.
Source: relative product theorem, compact-support specialization at Spec k
(blueprint: lem-sf-point-fibre-derived-tensor). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      (n : ℕ),
    Λ = PointTensorReduction.finiteCoefficient ell E π n) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, Λ = latticeIntegralRing ell E) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, Λ = scalarSixFieldRing ell E) ∨
  Λ = latticeClosureRing ell

/-- The actual integral quotient map is specified on every profinite section. This
property determines the morphism uniquely and does not replace it by an arbitrary map.
Index n means the positive exponent n+1, including exponent one.
Source: relative product theorem, integral reduction clause
(blueprint: lem-sf-point-fibre-derived-tensor). -/
def IsIntegralReduction (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E) (n : ℕ)
    (a : latticeIntegralRing.{u} ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n) :
    Prop :=
  ∀ (S : Profinite.{u}) (x : (latticeIntegralRing.{u} ell E).X.obj.obj (op S)) (s : S),
    ((a.hom.hom.hom.app (op S)) x).down s =
      Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) (x.down s)

/-- The coefficient maps in the statement, including equal finite levels and equal
finite subextensions. Integral reduction is pinned sectionwise by its quotient formula.
Source: relative product theorem, finite-reduction and scalar-extension clause
(blueprint: lem-sf-point-fibre-derived-tensor). -/
inductive IsScalarMap (ell : ℕ) [Fact ell.Prime] :
    {Λ Λ' : ScalarSixRing.{u}} → (Λ ⟶ Λ') → Prop
  | finite (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      {m n : ℕ} (h : n ≤ m) :
      IsScalarMap ell (PointTensorReduction.finiteCoefficientMap ell E π h)
  | reduction (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      (n : ℕ) (a : latticeIntegralRing ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n)
      (ha : IsIntegralReduction ell E π n a) : IsScalarMap ell a
  | localization (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsScalarMap ell (scalarSixIntegralToField ell E)
  | integral {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
      IsScalarMap ell (latticeIntegralMap ell h)
  | field {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
      IsScalarMap ell
        (⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩ :
          scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell E')
  | closure (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsScalarMap ell
        (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
          scalarSixFieldRing ell E ⟶ latticeClosureRing ell)

variable (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]

/-- Coherence of the fixed section cup. Invertibility makes its inverse unique;
these equations also express naturality, associativity, signed symmetry and both
unit laws for that inverse. Tensor products in these equations are ambient tensors.
Source: relative product theorem, tensor coherence at Spec k
(blueprint: lem-sf-point-fibre-derived-tensor). -/
structure TensorCoherence : Prop where
  invertible (M N : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    IsIso (TraceCupPoint.tensor Λ.X k M N)
  unit_invertible : IsIso (TraceCupPoint.pointFiberUnit (Λ := Λ) k)
  naturality {M M' N N' : CondensedGeometricPoint.Complexes Λ.X k}
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hM' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M')
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hN' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N')
    (f : M ⟶ M') (g : N ⟶ N') :
    ((TraceCupPoint.fiber Λ.X k).map f ⊗ₘ (TraceCupPoint.fiber Λ.X k).map g) ≫
        TraceCupPoint.tensor Λ.X k M' N' =
      TraceCupPoint.tensor Λ.X k M N ≫ (TraceCupPoint.fiber Λ.X k).map (f ⊗ₘ g)
  associativity (M N P : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hP : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) P) :
    (TraceCupPoint.tensor Λ.X k M N ▷ (TraceCupPoint.fiber Λ.X k).obj P) ≫
        TraceCupPoint.tensor Λ.X k (M ⊗ N) P ≫
        (TraceCupPoint.fiber Λ.X k).map (α_ M N P).hom =
      (α_ ((TraceCupPoint.fiber Λ.X k).obj M) ((TraceCupPoint.fiber Λ.X k).obj N)
        ((TraceCupPoint.fiber Λ.X k).obj P)).hom ≫
        ((TraceCupPoint.fiber Λ.X k).obj M ◁ TraceCupPoint.tensor Λ.X k N P) ≫
        TraceCupPoint.tensor Λ.X k M (N ⊗ P)
  symmetry (M N : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    TraceCupPoint.tensor Λ.X k M N ≫
        (TraceCupPoint.fiber Λ.X k).map
          ((TraceCupPoint.siteBraiding Λ.X (Spec (.of k))).braiding M N).hom =
      ((TraceCupPoint.scalarBraiding Λ.X).braiding
        ((TraceCupPoint.fiber Λ.X k).obj M) ((TraceCupPoint.fiber Λ.X k).obj N)).hom ≫
        TraceCupPoint.tensor Λ.X k N M
  left_unit (M : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M) :
    (TraceCupPoint.pointFiberUnit (Λ := Λ) k ▷ (TraceCupPoint.fiber Λ.X k).obj M) ≫
        TraceCupPoint.tensor Λ.X k (𝟙_ _) M ≫
        (TraceCupPoint.fiber Λ.X k).map (λ_ M).hom =
      (λ_ ((TraceCupPoint.fiber Λ.X k).obj M)).hom
  right_unit (M : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M) :
    ((TraceCupPoint.fiber Λ.X k).obj M ◁ TraceCupPoint.pointFiberUnit (Λ := Λ) k) ≫
        TraceCupPoint.tensor Λ.X k M (𝟙_ _) ≫
        (TraceCupPoint.fiber Λ.X k).map (ρ_ M).hom =
      (ρ_ ((TraceCupPoint.fiber Λ.X k).obj M)).hom

variable {Λ} {Λ' : ScalarSixRing.{u}}

private theorem native_chain_braiding (K L : CochainComplex B ℤ) :
    d.chain K L ≫
        (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom =
      (β_ _ _).hom ≫ d.chain L K := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, d.chain_summand, Category.assoc, ← G.map_comp]
  erw [CochainComplex.Monoidal.ι_braiding_hom, G.map_zsmul, G.map_comp,
    Preadditive.comp_zsmul]
  conv_rhs =>
    rw [← Category.assoc]
    change (HomologicalComplex.ιTensorObj
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n hpq ≫ _) ≫ _
    erw [CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [d.chain_summand]
  congr 1
  exact congrArg (fun t ↦ t ≫ G.map
    (HomologicalComplex.ιTensorObj L K q p n (by change p + q = n at hpq; omega)))
    (hd (K.X p) (L.X q))

private theorem native_derived_braiding (M N : DerivedCategory B) :
    d.derived.μ M N ≫ G.mapDerivedCategory.map
        ((DerivedCategory.braidedCategory' B).braiding M N).hom =
      ((DerivedCategory.braidedCategory' (ModuleCat.{r} S)).braiding
        (G.mapDerivedCategory.obj M) (G.mapDerivedCategory.obj N)).hom ≫
          d.derived.μ N M := by
  letI := DerivedCategory.braidedCategory' B
  letI := DerivedCategory.braidedCategory' (ModuleCat.{r} S)
  letI := d.derived
  letI : (DerivedCategory.Q (C := B)).LaxBraided :=
    RingedDerivedNative.localizationLaxBraided
  letI : (DerivedCategory.Q (C := ModuleCat.{r} S)).LaxBraided :=
    RingedDerivedNative.localizationLaxBraided
  change Functor.LaxMonoidal.μ G.mapDerivedCategory M N ≫
      G.mapDerivedCategory.map (β_ M N).hom =
    (β_ (G.mapDerivedCategory.obj M) (G.mapDerivedCategory.obj N)).hom ≫
      Functor.LaxMonoidal.μ G.mapDerivedCategory N M
  have hb (K L : CochainComplex B ℤ)
      (hK : (HomotopyCategory.quasiIso B (.up ℤ)).kFlat
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) :
      d.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
          G.mapDerivedCategory.map (β_ _ _).hom =
        (β_ _ _).hom ≫ d.derived.μ (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj K) := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q L K) :=
      RingedDerivedNative.localization_isIso_mu L K (Or.inr hK)
    apply (cancel_mono (G.mapDerivedCategory.map
      (Functor.LaxMonoidal.μ DerivedCategory.Q L K) ≫
        G.mapDerivedCategoryFactors.hom.app (L ⊗ K))).1
    simp only [Category.assoc]
    rw [← G.mapDerivedCategory.map_comp_assoc, ← Functor.LaxBraided.braided,
      G.mapDerivedCategory.map_comp, Category.assoc]
    have hnat := G.mapDerivedCategoryFactors.hom.naturality (β_ K L).hom
    dsimp only [Functor.comp_map] at hnat
    rw [hnat]
    rw [reassoc_of% (d.tensor_normalization K L), d.tensor_normalization]
    rw [← DerivedCategory.Q.map_comp, native_chain_braiding G d hd]
    rw [DerivedCategory.Q.map_comp, Functor.LaxBraided.braided_assoc,
      BraidedCategory.braiding_naturality_assoc]
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  let eK : DerivedCategory.Q.obj K ≅ M :=
    ((DerivedCategory.quotientCompQhIso B).app K).symm ≪≫ eP
  let L := DerivedCategory.Q.objPreimage N
  let eL := DerivedCategory.Q.objObjPreimageIso N
  apply (cancel_epi (G.mapDerivedCategory.map eK.hom ⊗ₘ
    G.mapDerivedCategory.map eL.hom)).1
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← G.mapDerivedCategory.map_comp,
    BraidedCategory.braiding_naturality, G.mapDerivedCategory.map_comp,
    ← Category.assoc, hb K L hP, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural, BraidedCategory.braiding_naturality_assoc]

private theorem tensorData_pure (Λ : ScalarSixRing.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ.X (Spec (.of k))))
    (x : (condensedRingCoefficientSections Λ.X (Spec (.of k))).obj M)
    (y : (condensedRingCoefficientSections Λ.X (Spec (.of k))).obj N) :
    ((TraceCupPoint.tensorData Λ.X k).ordinary.μ M N).hom
      (x ⊗ₜ[MonObj.Γ Λ.X] y) = (λ_ _).inv ≫ (x ⊗ₘ y) := by
  unfold TraceCupPoint.tensorData
  exact (TraceCupPoint.tensorData_existsUnique Λ.X k).choose_spec.1 M N x y

private theorem native_ordinary_unit (Λ : ScalarSixRing.{u})
    (k : Type u) [Field k] [IsAlgClosed k] :
    IsIso (TraceCupPoint.tensorData Λ.X k).ordinary.ε := by
  let m := (TraceCupPoint.tensorData Λ.X k).ordinary
  have hm := tensorData_pure Λ k
  let G := condensedRingCoefficientSections Λ.X (Spec (.of k))
  let B := Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj Λ.X (Spec (.of k)))
  let I : B := 𝟙_ B
  letI := m
  have hunit : m.ε.hom 1 = (𝟙 I : G.obj I) := by
    have h := congrArg (fun f ↦ f.hom ((1 : MonObj.Γ Λ.X) ⊗ₜ[MonObj.Γ Λ.X] (𝟙 I : G.obj I)))
      (Functor.LaxMonoidal.left_unitality G I).symm
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul] at h
    change ((m.μ I I).hom ((m.ε.hom 1) ⊗ₜ[MonObj.Γ Λ.X] (𝟙 I))) ≫ (λ_ I).hom = 𝟙 I at h
    rw [hm] at h
    change (λ_ (𝟙_ B)).inv ≫
      ((m.ε.hom 1 : (𝟙_ B) ⟶ (𝟙_ B)) ⊗ₘ 𝟙 (𝟙_ B)) ≫ (λ_ (𝟙_ B)).hom = 𝟙 I at h
    rw [MonoidalCategory.tensorHom_id, unitors_equal, unitors_inv_equal,
      rightUnitor_naturality, Iso.inv_hom_id_assoc] at h
    exact h
  have hb : Function.Bijective (condensedRingScalarSections Λ.X (Spec (.of k))) := by
    letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint (Spec (.of k)))
    exact InternalAbelianSheafModule.globalMapFunctor_bijective
      (upperStarFromPoint (Spec (.of k))) (Functor.FullyFaithful.ofFullyFaithful _) Λ.X
  have he : (fun a ↦ m.ε.hom a) =
      fun a ↦ Mod.regularEndRingHom (condensedRingScalarSections Λ.X (Spec (.of k)) a) := by
    funext a
    calc
      m.ε.hom a = m.ε.hom (a • (1 : MonObj.Γ Λ.X)) := by rw [smul_eq_mul, _root_.mul_one]
      _ = a • m.ε.hom 1 := map_smul _ _ _
      _ = _ := by
        rw [hunit]
        change _ ≫ 𝟙 I = _
        rw [Category.comp_id]
        rfl
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a ↦ m.ε.hom a)
  rw [he]
  exact Mod.regularEndRingHom_bijective.comp hb

private theorem native_unit_isIso (Λ : ScalarSixRing.{u})
    (k : Type u) [Field k] [IsAlgClosed k] :
    IsIso (TraceCupPoint.pointFiberUnit (Λ := Λ) k) := by
  let G := condensedRingCoefficientSections Λ.X (Spec (.of k))
  let d := TraceCupPoint.tensorData Λ.X k
  letI := d.ordinary
  letI : IsIso d.ordinary.ε := native_ordinary_unit Λ k
  let B := Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj Λ.X (Spec (.of k)))
  let e : 𝟙_ (CochainComplex (ModuleCat.{u + 1} (MonObj.Γ Λ.X)) ℤ) ≅
      (G.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex B ℤ)) :=
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso (asIso d.ordinary.ε) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app (𝟙_ B)).symm
  have hchain : d.chainUnit = e.hom := by
    apply HomologicalComplex.from_single_hom_ext
    rw [d.chainUnit_zero]
    change _ = (((HomologicalComplex.single _ (.up ℤ) 0).map d.ordinary.ε) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (𝟙_ B)).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    dsimp only [G, B]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  haveI : IsIso d.chainUnit := by rw [hchain]; infer_instance
  haveI : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C :=
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of k)))))) :=
    RingedDerivedNative.localization_isIso_ε
  haveI : IsIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Q (C := ModuleCat.{u + 1} (MonObj.Γ Λ.X)))) :=
    RingedDerivedNative.localization_isIso_ε
  have hcomp : IsIso (d.derived.ε ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _)) := by
    rw [d.unit_normalization]
    infer_instance
  letI := d.derived
  haveI : IsIso d.derived.ε := IsIso.of_isIso_comp_right _
    (G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _))
  unfold TraceCupPoint.pointFiberUnit
  infer_instance

private theorem native_ordinary_braiding (Λ : ScalarSixRing.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ.X (Spec (.of k)))) :
    (TraceCupPoint.tensorData Λ.X k).ordinary.μ M N ≫
        (condensedRingCoefficientSections Λ.X (Spec (.of k))).map (β_ M N).hom =
      (β_ _ _).hom ≫ (TraceCupPoint.tensorData Λ.X k).ordinary.μ N M := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (𝟙_ _ ⟶ M) at x
  change (𝟙_ _ ⟶ N) at y
  change ((TraceCupPoint.tensorData Λ.X k).ordinary.μ M N).hom
      (x ⊗ₜ[MonObj.Γ Λ.X] y) ≫ (β_ M N).hom =
    ((TraceCupPoint.tensorData Λ.X k).ordinary.μ N M).hom
      (y ⊗ₜ[MonObj.Γ Λ.X] x)
  rw [tensorData_pure, tensorData_pure]
  change (λ_ _).inv ≫ (x ⊗ₘ y) ≫ (β_ M N).hom = (λ_ _).inv ≫ (y ⊗ₘ x)
  rw [BraidedCategory.braiding_naturality]
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← unitors_inv_equal]

private abbrev native_lax (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k] :
    (TraceCupPoint.fiber Λ.X k).LaxMonoidal := by
  letI := (TraceCupPoint.tensorData Λ.X k).derived
  exact Functor.LaxMonoidal.transport (TraceCupPoint.exactComparison Λ.X k).symm

private theorem native_μ (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (M N : CondensedGeometricPoint.Complexes Λ.X k) :
    letI := native_lax Λ k
    Functor.LaxMonoidal.μ (TraceCupPoint.fiber Λ.X k) M N =
      TraceCupPoint.tensor Λ.X k M N := by
  unfold TraceCupPoint.tensor TraceCupPoint.exactTensor
  rfl

private theorem native_ε (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k] :
    letI := native_lax Λ k
    Functor.LaxMonoidal.ε (TraceCupPoint.fiber Λ.X k) =
      TraceCupPoint.pointFiberUnit (Λ := Λ) k := rfl

private theorem native_reduction (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) :
    ∃ a : latticeIntegralRing.{u} ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n,
      ∀ (S : Profinite.{u}) (x : (latticeIntegralRing.{u} ell E).X.obj.obj (op S)) (s : S),
        ((a.hom.hom.hom.app (op S)) x).down s =
          Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) (x.down s) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  letI := PadicAlgCl.compactSpace_integers ell E.1
  let R := PadicAlgCl.integers ell E
  let A := R ⧸ (Ideal.span {π}) ^ (n + 1)
  haveI : DiscreteTopology A := by
    apply QuotientAddGroup.discreteTopology
    change IsOpen (X := R) ↑((Ideal.span {π}) ^ (n + 1))
    rw [hπ]
    exact IsLocalRing.isOpen_maximalIdeal_pow R (n + 1)
  have hc : @Continuous R A inferInstance ⊥ (Ideal.Quotient.mk _) := by
    rw [← DiscreteTopology.eq_bot (α := A)]
    exact continuous_quot_mk
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  refine ⟨CommMon.homMk (Mon.Hom.mk
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk _) hc))), ?_⟩
  intro S x s
  rfl

/-- The native section cup is invertible on Dctf, with its unique natural inverse,
coefficient evaluation unit, associativity, Koszul symmetry and unitor constraints.
The normalized scalar square holds for every listed finite reduction, integral
reduction, rationalization, finite-field inclusion and finite-subextension inclusion
into the actual finite-subextension-valued closure coefficient ring.

Source: latest blueprint sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
compact-support specialization and finite-reduction/scalar-extension clauses
(blueprint: lem-sf-point-fibre-derived-tensor).

Proof: (1) lem-sf-condensed-geometric-point-perfect and the specified scalar realization
of def-weil-finite-coefficient-point identify each bounded constructible finite-Tor
object with the realization of its fibre, taking the coefficient unit to its scalars.
(2) Apply lem-sf-condensed-point-ambient-tensor-comparison to M and the scalar fibre
of N. Its balanced comparison and the realization counit identify its inverse with
the normalized section cup. Naturality, associativity, the Koszul interchange and
unit constraints descend from the same flat-term K-flat total-tensor formulas.
(3) lem-sf-condensed-point-derived-scalar-comparison supplies the finite quotient
squares, including equal levels, without flatness of a quotient map.
(4) lem-sf-point-fibre-integral-scalar-coherence supplies integral reductions with
the specified sectionwise quotient and their representative tensor and unit squares.
(5) lem-sf-point-fibre-rational-scalar-coherence supplies localization and finite
extension squares. lem-sf-point-fibre-qbar-scalar-coherence supplies all finite
subextension maps into the closure; its filtered compatibility retains the actual
finite-subextension coefficient sheaf. Their representative normalizations identify
these comparisons with those above, giving the simultaneous coefficient-change claim.
-/
theorem point_fibre_derived_tensor (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p) :
    (∀ (Λ : ScalarSixRing.{u}), IsCoefficient ell Λ → TensorCoherence Λ D.k) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E),
      Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E) →
      ∀ n : ℕ, ∃ a : latticeIntegralRing ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n,
        IsIntegralReduction ell E π n a) ∧
    (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ'),
      IsScalarMap ell a → Nonempty (ScalarCompatibility D.k a)) := by
  refine ⟨fun Λ _ ↦ native_tensor_coherence Λ D.k, ?_, ?_⟩
  · intro E π hπ n
    exact native_reduction ell E π hπ n
  · intro Λ Λ' a ha
    obtain ⟨c⟩ := native_scalar_normalization D ell _hell a ha
    obtain ⟨ht, hu⟩ := native_scalar_coherence D ell _hell a ha c
    exact ⟨{
      comparison := c.comparison
      ordinary := c.ordinary
      ordinary_apply := c.ordinary_apply
      representative := c.representative
      tensor_square := ht
      unit_square := hu }⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor
