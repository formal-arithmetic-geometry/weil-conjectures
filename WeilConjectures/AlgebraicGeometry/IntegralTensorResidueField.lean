/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Field.Defs
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel.ConstantPullback

/-!
# Bounded constructible tensor over the first residue field

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md,
“The stratum”, from “Every F_E,S-module is flat” through the truncation argument
(blueprint: lem-sfb-integral-tensor-residue-field).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem fieldSheaf_flat (B : Type (u + 1)) [Field B] (X : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    ObjectProperty.flat F := by
  have hf := GrothendieckTopology.flat_presheafToSheaf_obj
    (ModuleCat.{u + 1} B) (Scheme.ProEt.topology X) F.obj
    (fun U ↦ (ModuleCat.flat_iff_flat _).mpr inferInstance)
  exact ObjectProperty.prop_of_iso _
    ((asIso (sheafificationAdjunction (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} B)).counit).app F) hf

private theorem finiteLocal_pullback (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (hF : IsFiniteLocallyConstant B F) :
    IsFiniteLocallyConstant B ((upperStar _ f).obj F) := by
  obtain ⟨I, W, g, hg, h⟩ := hF
  let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X := ⟨⟨I, W, g⟩, hg⟩
  let D := C.pullback₁ f
  refine ⟨D.I₀, D.X, D.f, D.mem₀, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := h i
  exact ⟨P, hP, ⟨(upperStarCompIso _ (pullback.condition (f := f) (g := g i))).app F ≪≫
    (upperStar _ (pullback.snd f (g i))).mapIso e ≪≫
    (constantSheafCompUpperStarMkIdIso _ (pullback.snd f (g i))).app P⟩⟩

private theorem finiteLocal_tensor (B : Type (u + 1)) [CommRing B] [Finite B]
    {X : Scheme.{u}} (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (hF : IsFiniteLocallyConstant B F) (hG : IsFiniteLocallyConstant B G) :
    IsFiniteLocallyConstant B (F ⊗ G) := by
  obtain ⟨I, W, g, hg, h⟩ := hF
  obtain ⟨I', W', g', hg', h'⟩ := hG
  let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X := ⟨⟨I, W, g⟩, hg⟩
  let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X := ⟨⟨I', W', g'⟩, hg'⟩
  let U := C.bind (fun i ↦ D.pullback₁ (C.f i))
  refine ⟨U.I₀, U.X, U.f, U.mem₀, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h i.1
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := h' i.2
  have : Finite P := hP
  have : Finite Q := hQ
  have : Module.Finite B P := Module.Finite.of_finite
  have : Module.Finite B Q := Module.Finite.of_finite
  have : Finite (P ⊗ Q : ModuleCat.{u + 1} B) := by
    change Finite (TensorProduct B P Q)
    exact Module.finite_of_finite B
  let a := pullback.fst (g i.1) (g' i.2)
  let b := pullback.snd (g i.1) (g' i.2)
  let ep : (upperStar _ (U.f i)).obj F ≅
      (constantSheaf (Scheme.ProEt.topology (U.X i)) (ModuleCat.{u + 1} B)).obj P :=
    (upperStarComp _ a (g i.1)).app F ≪≫ (upperStar _ a).mapIso eP ≪≫
      (constantSheafCompUpperStarMkIdIso _ a).app P
  let eq : (upperStar _ (U.f i)).obj G ≅
      (constantSheaf (Scheme.ProEt.topology (U.X i)) (ModuleCat.{u + 1} B)).obj Q :=
    (upperStarCongr _ (pullback.condition (f := g i.1) (g := g' i.2))).app G ≪≫
      (upperStarComp _ b (g' i.2)).app G ≪≫ (upperStar _ b).mapIso eQ ≪≫
      (constantSheafCompUpperStarMkIdIso _ b).app Q
  exact ⟨P ⊗ Q, inferInstance, ⟨(Functor.Monoidal.μIso (upperStar _ (U.f i)) F G).symm ≪≫
    tensorIso ep eq ≪≫ Functor.Monoidal.μIso (constantSheaf _ _) P Q⟩⟩

private theorem constructible_tensor (B : Type (u + 1)) [CommRing B] [Finite B]
    {X : Scheme.{u}} (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (hF : IsConstructible B F) (hG : IsConstructible B G) :
    IsConstructible B (F ⊗ G) := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨T, hT⟩ := hG
  refine ⟨S.inter T, fun k ↦ ?_⟩
  let i := (finProdFinEquiv.symm k).1
  let j := (finProdFinEquiv.symm k).2
  let a := pullback.fst (S.immersion i) (T.immersion j)
  let b := pullback.snd (S.immersion i) (T.immersion j)
  have h1 := isFiniteLocallyConstant_of_iso ((upperStarComp _ a (S.immersion i)).app F).symm
    (finiteLocal_pullback B a _ (hS i))
  have h2 := isFiniteLocallyConstant_of_iso
    ((upperStarComp _ b (T.immersion j)).app G).symm
    (finiteLocal_pullback B b _ (hT j))
  have h2' := isFiniteLocallyConstant_of_iso
    ((upperStarCongr _ (pullback.condition (f := S.immersion i)
      (g := T.immersion j))).app G).symm h2
  exact isFiniteLocallyConstant_of_iso
    (Functor.Monoidal.μIso (upperStar _ ((S.inter T).immersion k)) F G)
    (finiteLocal_tensor B _ _ h1 h2')

private theorem ordinary_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

private theorem fixedField_tensor
    (B : Type (u + 1)) [Field B] [Finite B]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hK : DerivedCategory.TStructure.t.bounded K ∧
      ∀ n, IsConstructible B ((DerivedCategory.homologyFunctor _ n).obj K))
    (hL : DerivedCategory.TStructure.t.bounded L ∧
      ∀ n, IsConstructible B ((DerivedCategory.homologyFunctor _ n).obj L)) :
    DerivedCategory.TStructure.t.bounded (K ⊗ L) ∧
      ∀ n, IsConstructible B ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)
  let P : ObjectProperty C := IsConstructible B
  have : P.IsClosedUnderIsomorphisms := ⟨fun i h ↦ isConstructible_of_iso i h⟩
  let Z := (HasZeroObject.zero
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).choose
  have hz : IsZero Z := (HasZeroObject.zero (C :=
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).choose_spec
  have : Scheme.IsConstructibleSheaf Z := Scheme.IsConstructibleSheaf.of_isZero hz
  have : P.ContainsZero := ⟨(comparisonUpperStar _ X).obj Z,
    Functor.map_isZero _ hz, isConstructible_comparisonUpperStar_obj Z⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hlim)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X _ _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hlim)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X _ _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions :=
    ⟨fun hS h1 h3 ↦ Scheme.CoefficientSerre.fixed_extension X _ _ hS h1 h3⟩
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (cohomology_in_weak_serre_subcategory P).1
  let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  have : Q.IsClosedUnderIsomorphisms := inferInstance
  have hs (F : C) (hF : P F) : Q ((DerivedCategory.singleFunctor C 0).obj F) := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst hn
      exact P.prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app F).symm hF
    · apply P.prop_of_isZero
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 n h
      · exact DerivedCategory.isZero_of_isLE _ 0 n h
  have hss (F G : C) (hF : P F) (hG : P G) :
      Q ((DerivedCategory.singleFunctor C 0).obj F ⊗
        (DerivedCategory.singleFunctor C 0).obj G) := by
    let e : (DerivedCategory.singleFunctor C 0).obj F ⊗
        (DerivedCategory.singleFunctor C 0).obj G ≅
        (DerivedCategory.singleFunctor C 0).obj (F ⊗ G) :=
      tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app F)
          ((DerivedCategory.singleFunctorIsoCompQ C 0).app G) ≪≫
        DerivedCategory.QObjTensorQObjIsoOfKFlatLeft _ _
          ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 (fieldSheaf_flat B X F)) ≪≫
        DerivedCategory.Q.mapIso
          ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) F).app _ ≪≫
            (HomologicalComplex.singleMapHomologicalComplex
              (tensorLeft F) (.up ℤ) 0).app G) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app (F ⊗ G)).symm
    exact Q.prop_of_iso e.symm (hs _ (constructible_tensor B F G hF hG))
  have hsingle (F : C) (hF : P F) :
      Q ((DerivedCategory.singleFunctor C 0).obj F ⊗ L) := by
    exact DerivedCategory.prop_of_bounded
      (Q.inverseImage (tensorLeft ((DerivedCategory.singleFunctor C 0).obj F))) P
      (fun G hG ↦ hss F G hF hG) L hL.1 hL.2
  exact DerivedCategory.prop_of_bounded (Q.inverseImage (tensorRight L)) P
    hsingle K hK.1 hK.2

private theorem finiteField_tensor
    (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A] (hA : IsField A) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)))
    (hK : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X K)
    (hL : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X L) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X
      (K ⊗ L) := by
  classical
  -- Retain the original ring operations in the statement and specialize only inside this proof.
  let : Field A := hA.toField
  let e := (FiniteDiscreteOrdinary.encoding_exists A X).some
  let F := e.fixedDerived.functor
  obtain ⟨hF⟩ := (FiniteDiscreteOrdinary.encoding_tensor_tor A X e).1
  let := hF
  let Q : ObjectProperty (DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
    DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty
      (IsConstructible (ULift.{u + 1} A))
  have hc (T) : constantModelBoundedConstructible
      (Profinite.continuousCoefficientRingObj A) X T ↔ Q (F.obj T) := by
    rw [(FiniteDiscreteOrdinary.encoding_constructibility A X e).2 T]
    apply and_congr Iff.rfl
    exact forall_congr' fun n ↦ ordinary_iff A X _
  have ht := fixedField_tensor (ULift.{u + 1} A) X (F.obj K) (F.obj L)
    ((hc K).mp hK) ((hc L).mp hL)
  apply (hc (K ⊗ L)).mpr
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructible (ULift.{u + 1} A) (X := X)) :=
    ⟨fun i h ↦ isConstructible_of_iso i h⟩
  exact Q.prop_of_iso (Functor.Monoidal.μIso F K L) ht

/-- Bounded constructible complexes over the pulled-back continuous condensed first
residue field are closed under the ordinary derived tensor over that residue field.

Source: det-lem-int-tensor-product.proof.md, “The stratum”, final argument.
(blueprint: lem-sfb-integral-tensor-residue-field).

Proof: the finite discrete residue ring is the finite field F_E; its continuous
condensed realization pulled to S is the constant field sheaf. Every module sheaf
over a constant field is flat: tensor is sheafification of sectionwise tensor over
the field, and both operations are exact. Consequently derived tensor is exact in
each variable with the usual sum of cohomological bounds. For constructible sheaves
F and G, intersect their finite locally closed stratifications and refine their
trivializing covers by fibre products. On each chart, finitely presented field
modules are finite free, so their models F_E^r and F_E^s tensor to F_E^(r*s).
Thus the tensor is constructible. The bounded truncation triangles, successively in
both variables, and triangulatedness of constructible cohomology extend this result
to bounded complexes. Empty strata and rank zero give zero tensor; no nonzero rank,
nonempty scheme, constant global rank or characteristic assumption is needed. -/
theorem integralTensorResidueField
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (M N : AdicCompletion.FiniteDerived l E S 0)
    (hM : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S M)
    (hN : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S N) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S (M ⊗ N) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := DerivedNakayama.quotientDiscrete l E 1
  let := Padic.finite_coefficientExtensionRing l E 1 le_rfl
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    simpa only [Padic.coefficientExtensionIdeal, pow_one, hgen] using hmax
  have hfield : IsField (Padic.coefficientExtensionRing l E 1) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  exact finiteField_tensor (Padic.coefficientExtensionRing l E 1) hfield S M N hM hN

end AlgebraicGeometry.ProEtale
