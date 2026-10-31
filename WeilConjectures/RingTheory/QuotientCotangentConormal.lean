/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.RingTheory.NaiveCotangentComparison
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The conormal cohomology of a quotient

Source: Stacks Project, Cotangent Complex, lemma-surjection and
lemma-relation-with-naive-cotangent-complex.
(blueprint: lem-trf-quotient-cotangent-conormal-homology).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Simplicial

namespace Algebra.CotangentResolution

private def identityPresentation (R : Type u) [CommRing R] (I : Ideal R) :
    Naive.Presentation (Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))) where
  ring := CommRingCat.of R
  base := 𝟙 _
  augmentation := CommRingCat.ofHom (Ideal.Quotient.mk I)
  triangle := Category.id_comp _
  surjective := Ideal.Quotient.mk_surjective

private theorem identityPresentation_polynomial (R : Type u) [CommRing R] (I : Ideal R) :
    Naive.IsLocalizedPolynomial (identityPresentation R I) := by
  dsimp only [Naive.IsLocalizedPolynomial, identityPresentation, Arrow.mk_left, Arrow.mk_right]
  let e := MvPolynomial.isEmptyRingEquiv R PEmpty.{u + 1}
  refine ⟨PEmpty, CommRingCat.ofHom e.toRingHom, ⊥, ?_, ?_⟩
  · intro a
    exact (MvPolynomial.isEmptyAlgEquiv R PEmpty).commutes a
  · change letI := e.toRingHom.toAlgebra; IsLocalization ⊥ R
    let := e.toRingHom.toAlgebra
    exact IsLocalization.of_le_isUnit_of_bijective (by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : x = 1 := by simpa using hx
      simp [hx1]) e.bijective

private def identityConormalIso (R : Type u) [CommRing R] (I : Ideal R) :
    Naive.conormal (identityPresentation R I) ≅ ModuleCat.of (R ⧸ I) I.Cotangent := by
  letI := (Ideal.Quotient.mk I).toAlgebra
  letI := (RingHom.id R).toAlgebra
  let P : Algebra.Extension R (R ⧸ I) :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R R (R ⧸ I)) Ideal.Quotient.mk_surjective
  have hker : P.ker = I := Ideal.mk_ker
  let e := Ideal.Cotangent.equivOfEq P.ker I hker
  let g : P.Cotangent ≃ₗ[R ⧸ I] I.Cotangent :=
    { toEquiv := P.cotangentEquivCotangentKer.toEquiv.trans e.toEquiv
      map_add' := fun x y ↦ by
        change e (x + y).val = e x.val + e y.val
        rw [Algebra.Extension.Cotangent.val_add, map_add]
      map_smul' := fun b x ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        change e ((Ideal.Quotient.mk I a • x).val) = Ideal.Quotient.mk I a • e x.val
        have ht := Algebra.Extension.Cotangent.val_smul' (P := P) a x
        change (Ideal.Quotient.mk I a • x).val = a • x.val at ht
        rw [ht, map_smul]
        rfl }
  exact g.toModuleIso

private theorem identityConormalIso_kernelClass (R : Type u) [CommRing R]
    (I : Ideal R) (a : I) :
    (identityConormalIso R I).hom
      (Naive.kernelClass (identityPresentation R I)
        ⟨(a : R), Ideal.Quotient.eq_zero_iff_mem.mpr a.property⟩) = I.toCotangent a := by
  change Ideal.Cotangent.equivOfEq _ I _ (Ideal.toCotangent _ ⟨(a : R), _⟩) = _
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  congr 1

private theorem identityDifferentials_zero (R : Type u) [CommRing R] (I : Ideal R) :
    Limits.IsZero (Naive.differentials (identityPresentation R I)) := by
  change Limits.IsZero ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
    (CommRingCat.KaehlerDifferential (𝟙 (CommRingCat.of R))))
  let := (RingHom.id R).toAlgebra
  have : Subsingleton (KaehlerDifferential R R) :=
    KaehlerDifferential.subsingleton_of_surjective R R Function.surjective_id
  apply (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map_isZero
  change Limits.IsZero (ModuleCat.of R (KaehlerDifferential R R))
  exact ModuleCat.isZero_of_subsingleton _

private theorem identity_naive_homology
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R)
    (D : Naive.Comparison C) :
    let P := identityPresentation R I
    let hP := identityPresentation_polynomial R I
    ∃ (a : Naive.PresentationMap (𝟙 _) (Naive.standardPresentation C _) P),
      IsIso (HomologicalComplex.homologyMap (D.projection P hP a) (-1)) := by
  dsimp only
  let P := identityPresentation R I
  let hP := identityPresentation_polynomial R I
  obtain ⟨a⟩ := D.lift_exists P hP
  refine ⟨a, ?_⟩
  let K := differentialComplex (C.differentials
    (C.standard (Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I)))))
  have hπ : IsIso ((DerivedCategory.homologyFunctor _ (-1)).map
      (DerivedCategory.Q.map (K.πTruncGE (-1)))) := by
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ (-1)) _).2
      (by
        change IsIso (HomologicalComplex.homologyMap (K.πTruncGE (-1)) (-1))
        exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance)
  have hc : IsIso ((DerivedCategory.homologyFunctor _ (-1)).map
      (D.comparison P hP)) := by
    rw [← D.factorization P hP, Functor.map_comp]
    infer_instance
  rw [D.comparison_formula P hP a] at hc
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ (-1)) _).1 hc

private def identityNaiveHomologyIso (R : Type u) [CommRing R] (I : Ideal R) :
    (Naive.complex (identityPresentation R I)).homology (-1) ≅
      ModuleCat.of (R ⧸ I) I.Cotangent := by
  let P := identityPresentation R I
  let K := Naive.complex P
  have hdout : K.d (-1) 0 = 0 := by
    have hz : Limits.IsZero (K.X 0) :=
      (identityDifferentials_zero R I).of_iso (Naive.differentialsIso P)
    exact hz.eq_of_tgt _ _
  have hdin : K.d (-2) (-1) = 0 := by
    change Naive.boundary P (-2) = 0
    simp [Naive.boundary]
  exact (K.isoHomologyπ (-2) (-1) (by simp) hdin).symm ≪≫
    K.iCyclesIso (-1) 0 (by simp) hdout ≪≫
    Naive.conormalIso P ≪≫ identityConormalIso R I

private theorem ringHom_apply_of_heq {A B A' B' : CommRingCat.{u}}
    (hA : A = A') (hB : B = B') (g : A ⟶ B) (g' : A' ⟶ B') (h : HEq g g')
    (x : A') :
    g (_root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u)) hA.symm) x) =
      (eqToHom hB.symm) (g' x) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem standardFace_one_C (q : Arrow CommRingCat.{u}) (a : q.left) :
    standardFace q 0 (1 : Fin 2) (MvPolynomial.X (MvPolynomial.C a)) =
      MvPolynomial.X (q.hom a) := by
  dsimp [standardFace]
  erw [MvPolynomial.eval₂Hom_X']
  dsimp [standardAugmentation]
  erw [MvPolynomial.eval₂Hom_C]

private theorem standard_relation_faces
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R) (a : I) :
    let q := Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let P := C.standard q
    let x := _root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
      ((C.standard_spec q).1 1).symm)
      (MvPolynomial.X (MvPolynomial.C (a : R)) -
        MvPolynomial.X (MvPolynomial.C (0 : R)))
    P.algebra.δ (0 : Fin 2) x = P.base.app (Opposite.op ⦋0⦌) (a : R) ∧
      P.algebra.δ (1 : Fin 2) x = 0 := by
  dsimp only
  let q := Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let P := C.standard q
  let h0 := (C.standard_spec q).1 0
  let h1 := (C.standard_spec q).1 1
  have hface (i : Fin 2) := ringHom_apply_of_heq h1 h0 (P.algebra.δ i)
    (standardFace q 0 i) ((C.standard_spec q).2.2.2.1 0 i)
    (MvPolynomial.X (MvPolynomial.C (a : R)) -
      MvPolynomial.X (MvPolynomial.C (0 : R)))
  have hbase := ringHom_apply_of_heq rfl h0 (P.base.app (Opposite.op ⦋0⦌))
    (standardBase q 0) ((C.standard_spec q).2.1 0) (a : R)
  have ha : Ideal.Quotient.mk I (a : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr a.property
  change P.base.app (Opposite.op ⦋0⦌) (a : R) =
    (eqToHom h0.symm) (standardBase q 0 (a : R)) at hbase
  constructor
  · erw [hface, hbase]
    congr 1
    dsimp [standardFace, standardBase]
    erw [map_sub, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simp
    rfl
  · erw [hface]
    have hzero : standardFace q 0 (1 : Fin 2)
        (MvPolynomial.X (MvPolynomial.C (a : R)) -
          MvPolynomial.X (MvPolynomial.C (0 : R))) = 0 := by
      erw [map_sub, standardFace_one_C, standardFace_one_C]
      change MvPolynomial.X (Ideal.Quotient.mk I (a : R)) -
        MvPolynomial.X (Ideal.Quotient.mk I (0 : R)) = 0
      rw [ha, map_zero, sub_self]
    rw [hzero]
    exact map_zero (eqToHom h0.symm).hom

private theorem differentialGenerator_base {q : Arrow CommRingCat.{u}}
    (P : Augmentation q) (n : ℕ) (b : q.right) (a : q.left) :
    differentialGenerator P n b (P.base.app (Opposite.op ⦋n⦌) a) = 0 := by
  dsimp [differentialGenerator]
  have hd := (CommRingCat.KaehlerDifferential.D (P.base.app (Opposite.op ⦋n⦌))).d_map a
  exact (congrArg (fun t ↦
    TensorProduct.tmul (P.algebra.obj (Opposite.op ⦋n⦌))
      (M := (ModuleCat.restrictScalars (P.augmentation.app (Opposite.op ⦋n⦌)).hom).obj
        (ModuleCat.of q.right q.right)) b t) hd).trans
    (TensorProduct.tmul_zero _ _)

private theorem complexGenerator_boundary_one {q : Arrow CommRingCat.{u}}
    {P : Augmentation q} (D : DifferentialModel P) (b : q.right)
    (x : P.algebra.obj (Opposite.op ⦋1⦌)) :
    (differentialComplex D).d (-1) 0 (complexGenerator D 1 b x) =
      complexGenerator D 0 b (P.algebra.δ (0 : Fin 2) x) -
        complexGenerator D 0 b (P.algebra.δ (1 : Fin 2) x) := by
  let K := (AlgebraicTopology.alternatingFaceMapComplex _).obj D.module
  let e := ComplexShape.embeddingDownNat
  change (K.extend e).d (-1) 0
    ((K.extendXIso e (i := 1) rfl).inv ((D.termIso 1).inv
      (differentialGenerator P 1 b x))) = _
  erw [K.extend_d_eq e (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl]
  dsimp only [K, e]
  simp only [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  have hsum : AlgebraicTopology.AlternatingFaceMapComplex.objD D.module 0 =
      D.module.δ (0 : Fin 2) - D.module.δ (1 : Fin 2) := by
    simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two,
      sub_eq_add_neg]
  rw [hsum]
  have hf (i : Fin 2) :
      D.module.δ i ((D.termIso 1).inv (differentialGenerator P 1 b x)) =
        (D.termIso 0).inv (differentialGenerator P 0 b (P.algebra.δ i x)) := by
    apply (ConcreteCategory.bijective_of_isIso (D.termIso 0).hom).1
    exact (D.operator 0 1 (SimplexCategory.δ i) b x).trans
      (by simp only [Iso.inv_hom_id_apply]; rfl)
  change (K.extendXIso e (i := 0) rfl).inv
    (D.module.δ 0 ((D.termIso 1).inv (differentialGenerator P 1 b x)) -
      D.module.δ 1 ((D.termIso 1).inv (differentialGenerator P 1 b x))) = _
  rw [hf, hf, map_sub]
  rfl

private theorem standard_relation_cycle
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R) (a : I) :
    let q := Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let P := C.standard q
    let x := _root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
      ((C.standard_spec q).1 1).symm)
      (MvPolynomial.X (MvPolynomial.C (a : R)) -
        MvPolynomial.X (MvPolynomial.C (0 : R)))
    (differentialComplex (C.differentials P)).d (-1) 0
      (complexGenerator (C.differentials P) 1 1 x) = 0 := by
  dsimp only
  rw [complexGenerator_boundary_one]
  obtain ⟨h0, h1⟩ := standard_relation_faces C R I a
  erw [h0, h1]
  have hzero : differentialGenerator
      (C.standard (Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I)))) 0 1 0 = 0 := by
    simp [differentialGenerator, CommRingCat.KaehlerDifferential.d,
      ModuleCat.Derivation.d]
  simp only [complexGenerator, differentialGenerator_base, hzero, map_zero, sub_self]

/-- The degree minus one cohomology of any quotient is its conormal module,
with the standard relation normalization. No regularity hypothesis is needed.
Source: Stacks Project, Cotangent Complex, lemma-surjection, and the comparison
map preceding it (blueprint: lem-trf-quotient-cotangent-conormal-homology).

Proof: Apply the naive comparison to the presentation R -> R/I with presentation
ring R and base map the identity, a polynomial algebra on the empty set.
Its module of relative differentials is zero. Its conormal is I/I², since the
kernel of the quotient map is I. Thus the comparison identifies the good
truncation with the single conormal module in degree minus one, and induces the
asserted homology isomorphism. The two faces of [C(a)] - [0] are C(a) and zero;
their relative differentials vanish, so the displayed vector is a cycle.
The degree minus one formula for the naive projection sends this cycle to the
class of the difference of the faces, namely a mod I². Naturality of homology
under localization gives the stated formula on the concrete standard complex.
This argument includes I = 0, I = R, and the zero ring. -/
theorem quotient_conormal_homology
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R) :
    let q := Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let K := differentialComplex (C.differentials (C.standard q))
    ∃ h : K.homology (-1) ≅ ModuleCat.of (R ⧸ I) I.Cotangent,
      ∀ a : I, ∃ z : K.cycles (-1),
        K.iCycles (-1) z =
          complexGenerator (C.differentials (C.standard q)) 1 1
            (_root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
              ((C.standard_spec q).1 1).symm)
              (MvPolynomial.X (MvPolynomial.C (a : R)) -
                MvPolynomial.X (MvPolynomial.C (0 : R)))) ∧
        h.hom (K.homologyπ (-1) z) = I.toCotangent a := by
  dsimp only
  let q := Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let K := differentialComplex (C.differentials (C.standard q))
  let P := identityPresentation R I
  let hP := identityPresentation_polynomial R I
  obtain ⟨D⟩ := Naive.exists_comparison C
  obtain ⟨aP, haP⟩ := identity_naive_homology C R I D
  have := haP
  let p := D.projection P hP aP
  let h : K.homology (-1) ≅ ModuleCat.of (R ⧸ I) I.Cotangent :=
    asIso (HomologicalComplex.homologyMap p (-1)) ≪≫ identityNaiveHomologyIso R I
  refine ⟨h, ?_⟩
  intro a
  let x := _root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
    ((C.standard_spec q).1 1).symm)
    (MvPolynomial.X (MvPolynomial.C (a : R)) -
      MvPolynomial.X (MvPolynomial.C (0 : R)))
  let v := complexGenerator (C.differentials (C.standard q)) 1 1 x
  have hv : K.d (-1) 0 v = 0 := standard_relation_cycle C R I a
  have hv' : (K.sc (-1)).g v = 0 := by
    change K.d (-1) ((ComplexShape.up ℤ).next (-1)) v = 0
    rw [show (ComplexShape.up ℤ).next (-1) = 0 by simp [ComplexShape.next_eq']]
    exact hv
  let z : K.cycles (-1) := (K.sc (-1)).cyclesMk v hv'
  have hz : K.iCycles (-1) z = v := (K.sc (-1)).i_cyclesMk v hv'
  refine ⟨z, hz, ?_⟩
  have hfaces := standard_relation_faces C R I a
  have hclass : (Naive.conormalIso P).hom (p.f (-1) v) = Naive.kernelClass P
      ⟨(a : R), Ideal.Quotient.eq_zero_iff_mem.mpr a.property⟩ := by
    have hdiff : aP.map ((C.standard q).algebra.δ (0 : Fin 2) x -
        (C.standard q).algebra.δ (1 : Fin 2) x) = (a : R) := by
      rw [hfaces.1, hfaces.2, sub_zero]
      have hb := congrArg (fun g ↦ g (a : R)) aP.base
      exact hb
    have hpzero : P.augmentation
        (aP.map ((C.standard q).algebra.δ (0 : Fin 2) x -
          (C.standard q).algebra.δ (1 : Fin 2) x)) = 0 := by
      rw [hdiff]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property
    have hp := D.projection_neg_one P hP aP 1 x hpzero
    rw [one_smul] at hp
    exact hp.trans (congrArg (Naive.kernelClass P) (Subtype.ext hdiff))
  have hident : (Naive.complex P).homologyπ (-1) ≫
      (identityNaiveHomologyIso R I).hom =
      (Naive.complex P).iCycles (-1) ≫ (Naive.conormalIso P).hom ≫
        (identityConormalIso R I).hom := by
    dsimp only [identityNaiveHomologyIso, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, HomologicalComplex.isoHomologyπ_hom_inv_id, Category.id_comp]
    rfl
  have hnat : K.homologyπ (-1) ≫ h.hom =
      K.iCycles (-1) ≫ p.f (-1) ≫ (Naive.conormalIso P).hom ≫
        (identityConormalIso R I).hom := by
    dsimp only [h, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
      hident, ← Category.assoc, ← Category.assoc, HomologicalComplex.cyclesMap_i]
    simp only [Category.assoc]
  change (K.homologyπ (-1) ≫ h.hom) z = _
  rw [hnat]
  simp only [ConcreteCategory.comp_apply]
  rw [hz, hclass]
  exact identityConormalIso_kernelClass R I a

end Algebra.CotangentResolution
