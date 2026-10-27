/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.RingTheory.CotangentFlatBaseChange
public import Sheaf.RingTheory.PolynomialAugmentationCotangent
public import Sheaf.RingTheory.KoszulDerivedQuotient
import Sheaf.CategoryTheory.CochainUniversalCounitTransport
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived

/-!
# Tor independence of the polynomial square of a Koszul quotient

Source: Stacks Project, Cotangent Complex, Tag 08SJ, first paragraph of the proof.
(blueprint: lem-trf-koszul-polynomial-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

/-- The polynomial square sending each variable to the corresponding relation.
Source: Stacks, Tag 08SJ (blueprint: lem-trf-koszul-polynomial-square). -/
def koszulPolynomialSquare (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R) :
    PolynomialAugmentationCotangent.augmentationArrow r ⟶
      Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range f)))) :=
  Arrow.homMk (CommRingCat.ofHom (RingTheory.KoszulDerivedQuotient.polynomialMap f))
    (CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span (Set.range f))).comp
      ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom))) (by
      apply CommRingCat.hom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [RingTheory.KoszulDerivedQuotient.polynomialMap,
          PolynomialAugmentationCotangent.augmentationArrow]
      · intro i
        simp [RingTheory.KoszulDerivedQuotient.polynomialMap,
          PolynomialAugmentationCotangent.augmentationArrow])

private def zeroSectionEquiv (r : ℕ) :
    RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r ⧸
      RingTheory.KoszulDerivedQuotient.variableIdeal r ≃+* ULift.{u} ℤ := by
  let P := RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r
  let J := RingTheory.KoszulDerivedQuotient.variableIdeal.{u} r
  let ε : P →+* ULift.{u} ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id _) (fun _ ↦ 0)
  let g : P ⧸ J →+* ULift.{u} ℤ := Ideal.Quotient.lift J ε (by
    change J ≤ RingHom.ker ε
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ε (MvPolynomial.X i) = 0
    exact MvPolynomial.eval₂Hom_X' _ _ i)
  let h : ULift.{u} ℤ →+* P ⧸ J := (Ideal.Quotient.mk J).comp MvPolynomial.C
  have hg : g.comp h = RingHom.id _ := by
    apply RingHom.ext
    intro a
    change g (Ideal.Quotient.mk J (MvPolynomial.C a)) = a
    erw [Ideal.Quotient.lift_mk]
    simp [ε]
  have hh : h.comp g = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change h (g (Ideal.Quotient.mk J (MvPolynomial.C a))) = _
      erw [Ideal.Quotient.lift_mk]
      simp only [ε, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      rfl
    · intro i
      change h (g (Ideal.Quotient.mk J (MvPolynomial.X i))) = _
      erw [Ideal.Quotient.lift_mk]
      simp only [ε, MvPolynomial.eval₂Hom_X', map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_range_self i))).symm
  exact RingEquiv.ofRingHom g h hg hh

private def mixedScalarIso {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    (((ModuleCat.mixedTensor
      (RingTheory.KoszulDerivedQuotient.polynomialMap f)).flip.map₂CochainComplex).flip.obj
        (RingTheory.KoszulDerivedQuotient.ringComplex R)) ≅
      (ModuleCat.extendScalars
        (RingTheory.KoszulDerivedQuotient.polynomialMap f)).mapHomologicalComplex (.up ℤ) := by
  let φ := RingTheory.KoszulDerivedQuotient.polynomialMap f
  let e : (ModuleCat.mixedTensor φ).obj (ModuleCat.of R R) ≅ ModuleCat.extendScalars φ :=
    Functor.isoWhiskerLeft (ModuleCat.extendScalars φ)
      (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} R)) ≪≫
        Functor.rightUnitor _
  exact CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor φ).flip (ModuleCat.of R R) ≪≫
    NatIso.mapHomologicalComplex e (.up ℤ)

private def zeroSectionModuleIso (r : ℕ) :
    RingTheory.KoszulDerivedQuotient.zeroSection.{u} r ≅
      (ModuleCat.restrictScalars
        (PolynomialAugmentationCotangent.augmentationArrow r).hom.hom).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) := by
  let e := zeroSectionEquiv.{u} r
  let g : RingTheory.KoszulDerivedQuotient.zeroSection.{u} r ≃ₗ[
      RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r]
      (ModuleCat.restrictScalars
        (PolynomialAugmentationCotangent.augmentationArrow r).hom.hom).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) :=
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        change e (Ideal.Quotient.mk _ a * x) =
          (MvPolynomial.eval₂Hom (RingHom.id (ULift.{u} ℤ))
            (fun _ : Fin r ↦ 0) a) * e x
        rw [e.map_mul]
        rfl }
  exact g.toModuleIso

private theorem polynomial_extension_is_single
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    Nonempty ((baseChangeExtension (koszulPolynomialSquare R f).left).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((ModuleCat.restrictScalars
          (PolynomialAugmentationCotangent.augmentationArrow r).hom.hom).obj
          (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span (Set.range f)))).obj
          (ModuleCat.of (R ⧸ Ideal.span (Set.range f))
            (R ⧸ Ideal.span (Set.range f))))) := by
  let A := RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r
  let φ := RingTheory.KoszulDerivedQuotient.polynomialMap f
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    inferInstanceAs (HasDerivedCategory (ModuleCat.{u} (CommRingCat.of A)))
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
    inferInstanceAs (HasDerivedCategory (ModuleCat.{u} (CommRingCat.of R)))
  let : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let (N : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight N))
  let F := ModuleCat.extendScalars φ
  let : F.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  let := ModuleCat.extendScalars_preservesKFlatQuasiIso φ
  let L := baseChangeExtension (CommRingCat.ofHom φ)
  let ε := CategoryTheory.derivedCochainCounit F L F.leftDerivedFunctorCounit
  have : L.IsRightKanExtension F.leftDerivedFunctorCounit := by
    change F.leftDerivedFunctor.IsRightKanExtension F.leftDerivedFunctorCounit
    exact Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))
  have : L.IsRightKanExtension ε :=
    (cochainUniversalCounitTransport F L F.leftDerivedFunctorCounit).1
  obtain ⟨Lm, εm, hm, _, _⟩ :=
    DerivedCategory.exists_mixedTensor_pointwise_leftDerived φ
      (RingTheory.KoszulDerivedQuotient.ringComplex R)
  let := hm
  have : Lm.IsRightKanExtension εm :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
  let k := Functor.rightKanExtensionUniqueOfIso Lm εm
    (Functor.isoWhiskerRight (mixedScalarIso f) DerivedCategory.Q) L ε
  have := RingTheory.KoszulDerivedQuotient.isIso_comparison f hreg Lm εm
  let t := (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).mapIso
    (zeroSectionModuleIso r)
  refine ⟨L.mapIso (DerivedCategory.Q.mapIso t.symm) ≪≫ (k.app _).symm ≪≫
    asIso (RingTheory.KoszulDerivedQuotient.comparison f Lm εm)⟩

private theorem quotient_endomorphism_isIso (R : Type u) [CommRing R] (I : Ideal R)
    (g : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (R ⧸ I)) ⟶
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (R ⧸ I))) (hg : ∃ x, g x = (1 : R ⧸ I)) : IsIso g := by
  let g' : (R ⧸ I) → (R ⧸ I) := fun x ↦ g x
  change ∃ x : R ⧸ I, g' x = 1 at hg
  have hmul (a b : R ⧸ I) : g' (a * b) = a * g' b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact g.hom.map_smul a b
  obtain ⟨x, hx⟩ := hg
  have hunit : x * g' 1 = 1 := by rw [← hmul, mul_one, hx]
  have hinv (y : R ⧸ I) : x * g' y = y := by
    have hy : g' y = y * g' 1 := by simpa using hmul y 1
    rw [hy, mul_left_comm, hunit, mul_one]
  apply (ConcreteCategory.isIso_iff_bijective g).2
  change Function.Bijective g'
  constructor
  · intro y z hyz
    exact (hinv y).symm.trans ((congrArg (fun t ↦ x * t) hyz).trans (hinv z))
  · intro y
    refine ⟨y * x, ?_⟩
    rw [hmul, hx, mul_one]

/-- The canonical multiplication for the polynomial square is invertible.
Source: Stacks Project, Cotangent Complex, Tag 08SJ, first paragraph of proof
(blueprint: lem-trf-koszul-polynomial-square).

Proof: Resolve the zero section Z of P = Z[x_i] by the free Koszul complex on
its variables. The canonical multiplication after extension to R is its
augmentation to R/(f). By the Koszul base-change isomorphism the source is the
Koszul complex on f, whose positive homology vanishes by the hypothesis and
whose zeroth homology is R/(f). Thus its augmentation is a quasi-isomorphism.
Identify the zero section P/(x_i) with Z by polynomial evaluation, and mixed
tensor with ordinary scalar extension by the tensor-unit constraint. Uniqueness
of universal derived functors then gives an isomorphism e from the derived
extension of Z[0] to B[0]. To check the canonical multiplication μ, write e⁻¹μ
as single(k), using full faithfulness of the single functor. The adjunct of e
comes from a module map a:Z→Res(B). Adjunction naturality implies k∘a equals the
square's module map, so k(a(1))=1. Every R-linear endomorphism of B=R/I is
multiplication by k(1); this equation makes it invertible. Hence μ is invertible.
The empty sequence and zero ring require no change in the construction. -/
theorem isIso_koszulPolynomialSquare
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    IsIso (derivedSquareMultiplication (koszulPolynomialSquare R f)) := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
    inferInstanceAs (HasDerivedCategory (ModuleCat.{u} (CommRingCat.of R)))
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u} (RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r)) :=
    inferInstanceAs (HasDerivedCategory (ModuleCat.{u}
      (CommRingCat.of (RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r))))
  let q := koszulPolynomialSquare R f
  let U := ModuleCat.restrictScalars q.left.hom
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)
  let T := DerivedCategory.singleFunctor
    (ModuleCat.{u} (RingTheory.KoszulDerivedQuotient.PolynomialRing.{u} r)) (0 : ℤ)
  let Z := (ModuleCat.restrictScalars
    (PolynomialAugmentationCotangent.augmentationArrow r).hom.hom).obj
      (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
  let B := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span (Set.range f)))).obj
    (ModuleCat.of (R ⧸ Ideal.span (Set.range f)) (R ⧸ Ideal.span (Set.range f)))
  let adj := baseChangeAdjunction q.left
  obtain ⟨e⟩ := polynomial_extension_is_single R f hreg
  let μ := derivedSquareMultiplication q
  let k : B ⟶ B := S.preimage (e.inv ≫ μ)
  let j := U.mapDerivedCategorySingleFunctor 0
  let a : Z ⟶ U.obj B := T.preimage
    (adj.homEquiv _ _ e.hom ≫ j.hom.app B)
  have hk : e.hom ≫ S.map k = μ := by simp [k]
  have ha : a ≫ U.map k = squareModuleMap q := by
    apply T.map_injective
    rw [T.map_comp]
    rw [show T.map a = adj.homEquiv _ _ e.hom ≫ j.hom.app B from T.map_preimage _]
    have hj : j.hom.app B ≫ T.map (U.map k) =
        U.mapDerivedCategory.map (S.map k) ≫ j.hom.app B :=
      (j.hom.naturality k).symm
    erw [Category.assoc, hj, ← Category.assoc]
    have hn : adj.homEquiv _ _ e.hom ≫ U.mapDerivedCategory.map (S.map k) =
        adj.homEquiv _ _ (e.hom ≫ S.map k) :=
      (adj.homEquiv_naturality_right e.hom (S.map k)).symm
    erw [hn, hk]
    dsimp only [μ, derivedSquareMultiplication]
    erw [Equiv.apply_symm_apply]
    change (T.map (squareModuleMap q) ≫ j.inv.app B) ≫ j.hom.app B =
      T.map (squareModuleMap q)
    erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hv : k (a (1 : ULift.{u} ℤ)) = (1 : R ⧸ Ideal.span (Set.range f)) := by
    have h := congrArg (fun t ↦ t (1 : ULift.{u} ℤ)) ha
    change k (a (1 : ULift.{u} ℤ)) = q.right.hom (1 : ULift.{u} ℤ) at h
    simpa only [map_one] using h
  have : IsIso k := quotient_endomorphism_isIso R (Ideal.span (Set.range f)) k
    ⟨a (1 : ULift.{u} ℤ), hv⟩
  change IsIso μ
  rw [← hk]
  infer_instance

end Algebra.CotangentResolution
