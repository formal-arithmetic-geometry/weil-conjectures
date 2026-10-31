/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Coinduced total Hom complexes and K-injective targets

Source: Stacks Project, dualizing.tex, Tags 0A70 and 0A71, and derived.tex,
Tag 070H (blueprint: lem-trf-coinduction-total-hom-model).

Restriction and coinduction below are the termwise prolongations of Mathlib's
`restrictScalars` and `coextendScalars`. No second coinduction construction is introduced.
The one-object identity-cover ringed site is expressed in its ordinary-module presentation.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CochainComplex CochainComplex.HomComplex Opposite

namespace ModuleCat

section

set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev U {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A) :=
  (restrictScalars φ).mapHomologicalComplex (.up ℤ)

private noncomputable abbrev J {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A) :=
  (coextendScalars φ).mapHomologicalComplex (.up ℤ)

private noncomputable def transpose {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (restrictScalars φ).obj ((moduleHomComplex E ((J φ).obj I)).X n) ⟶
      (moduleHomComplex ((U φ).obj E) I).X n :=
  ModuleCat.ofHom
    (X := (restrictScalars φ).obj ((moduleHomComplex E ((J φ).obj I)).X n))
    { toFun := fun z ↦ Cochain.mk fun p q hpq ↦
        RestrictionCoextensionAdj.HomEquiv.toRestriction φ (z.v p q hpq)
      map_add' := by
        intro z w
        apply Cochain.ext
        intro p q hpq
        ext x
        rfl
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro p q hpq
        ext x
        change CoextendScalars.equiv φ (I.X q) (φ r • z.v p q hpq x) (1 : A) =
          r • CoextendScalars.equiv φ (I.X q) (z.v p q hpq x) (1 : A)
        rw [CoextendScalars.smul_apply, one_mul]
        have h := (CoextendScalars.equiv φ (I.X q) (z.v p q hpq x)).map_smul r
          (show (restrictScalars φ).obj (of A A) from (1 : A))
        change CoextendScalars.equiv φ (I.X q) (z.v p q hpq x)
          (φ r * (1 : A)) = r • CoextendScalars.equiv φ (I.X q)
            (z.v p q hpq x) (1 : A) at h
        simpa only [mul_one] using h }

private noncomputable def untranspose {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (moduleHomComplex ((U φ).obj E) I).X n ⟶
      (restrictScalars φ).obj ((moduleHomComplex E ((J φ).obj I)).X n) :=
  ModuleCat.ofHom
    (Y := (restrictScalars φ).obj ((moduleHomComplex E ((J φ).obj I)).X n))
    { toFun := fun z ↦ Cochain.mk fun p q hpq ↦
        RestrictionCoextensionAdj.HomEquiv.fromRestriction φ (z.v p q hpq)
      map_add' := by
        intro z w
        apply Cochain.ext
        intro p q hpq
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply CoextendScalars.ext
        ext a
        rfl
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro p q hpq
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply CoextendScalars.ext
        ext a
        change A at a
        change r • (z.v p q hpq) (a • x) =
          (φ r • RestrictionCoextensionAdj.HomEquiv.fromRestriction φ
            (z.v p q hpq) x) a
        rw [CoextendScalars.smul_apply]
        change r • (z.v p q hpq) (a • x) = (z.v p q hpq) (((show A from a) * φ r) • x)
        rw [mul_comm a, mul_smul]
        exact ((z.v p q hpq).hom.map_smul r (a • x)).symm }

private lemma transpose_untranspose {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    untranspose φ E I n ≫ transpose φ E I n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change E.X p at x
  change (z.v p q hpq) ((1 : A) • (show E.X p from x)) = (z.v p q hpq) x
  rw [one_smul]

private lemma untranspose_transpose {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    transpose φ E I n ≫ untranspose φ E I n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply CoextendScalars.ext
  ext a
  change CoextendScalars.equiv φ (I.X q) (z.v p q hpq (a • x)) (1 : A) =
    CoextendScalars.equiv φ (I.X q) (z.v p q hpq x) a
  rw [map_smul, CoextendScalars.smul_apply, one_mul]

private lemma transpose_delta {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n m : ℤ)
    (z : Cochain E ((J φ).obj I) n) :
    transpose φ E I m (δ n m z) = δ n m (transpose φ E I n z) := by
  apply Cochain.ext
  intro p q hpq
  ext x
  simp only [transpose, δ, Cochain.v]
  rfl

private noncomputable def transposeIso {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) :
    (U φ).obj (moduleHomComplex E ((J φ).obj I)) ≅
      moduleHomComplex ((U φ).obj E) I where
  hom :=
    { f := transpose φ E I
      comm' := fun n m _ ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact (transpose_delta φ E I n m z).symm }
  inv :=
    { f := untranspose φ E I
      comm' := fun n m _ ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        have h := ConcreteCategory.congr_hom (transpose_untranspose φ E I n) z
        have h' := ConcreteCategory.congr_hom (transpose_untranspose φ E I m)
          (δ n m z)
        dsimp at h h' ⊢
        apply_fun transpose φ E I m
        · change transpose φ E I m (δ n m (untranspose φ E I n z)) =
            transpose φ E I m (untranspose φ E I m (δ n m z))
          rw [transpose_delta, h, h']
        · intro a b hab
          have ha := ConcreteCategory.congr_hom (untranspose_transpose φ E I m) a
          have hb := ConcreteCategory.congr_hom (untranspose_transpose φ E I m) b
          change untranspose φ E I m (transpose φ E I m a) = a at ha
          change untranspose φ E I m (transpose φ E I m b) = b at hb
          rw [← ha, ← hb, hab] }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact untranspose_transpose φ E I n
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact transpose_untranspose φ E I n

private noncomputable abbrev A0 {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) :=
  (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
    ((restrictScalars φ).obj (ModuleCat.of A A))

private noncomputable def singleZeroIso {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) : (A0 φ).X 0 ≅ (restrictScalars φ).obj (ModuleCat.of A A) :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

private noncomputable def insertSingle {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    ((U φ).obj ((J φ).obj I)).X n ⟶ (moduleHomComplex (A0 φ) I).X n :=
  ModuleCat.ofHom (X := ((U φ).obj ((J φ).obj I)).X n)
    { toFun := fun h ↦ Cochain.single
        ((singleZeroIso φ).hom ≫
          ModuleCat.ofHom (X := (restrictScalars φ).obj (ModuleCat.of A A))
            (CoextendScalars.equiv φ (I.X n) h)) n
      map_add' := by
        intro h k
        apply Cochain.ext
        intro p q hpq
        by_cases hp : p = 0
        · subst p
          have hq : q = n := by lia
          subst hq
          simp only [Cochain.add_v, Cochain.single_v]
          rfl
        · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_src _ _
      map_smul' := by
        intro r h
        apply Cochain.ext
        intro p q hpq
        by_cases hp : p = 0
        · subst p
          have hq : q = n := by lia
          subst hq
          simp only [Cochain.smul_v, Cochain.single_v]
          ext x
          change CoextendScalars.equiv φ (I.X q)
            (φ r • (show (coextendScalars φ).obj (I.X q) from h)) _ =
            r • CoextendScalars.equiv φ (I.X q) h _
          rw [CoextendScalars.smul_apply]
          change CoextendScalars.equiv φ (I.X q) h
            ((show A from (singleZeroIso φ).hom x) * φ r) = _
          rw [mul_comm]
          exact (CoextendScalars.equiv φ (I.X q) h).map_smul r _
        · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_src _ _ }

private noncomputable def evaluateSingle {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (moduleHomComplex (A0 φ) I).X n ⟶ ((U φ).obj ((J φ).obj I)).X n :=
  ModuleCat.ofHom (Y := ((U φ).obj ((J φ).obj I)).X n)
    { toFun := fun z ↦ (CoextendScalars.equiv φ (I.X n)).symm
        (((singleZeroIso φ).inv ≫
          z.v 0 n (zero_add n)).hom)
      map_add' := by
        intro z w
        apply CoextendScalars.ext
        ext a
        rfl
      map_smul' := by
        intro r z
        apply CoextendScalars.ext
        ext a
        change A at a
        change r • (z.v 0 n (zero_add n))
          ((singleZeroIso φ).inv a) =
          (z.v 0 n (zero_add n))
            ((singleZeroIso φ).inv (a * φ r))
        rw [mul_comm a]
        exact (((singleZeroIso φ).inv ≫
          z.v 0 n (zero_add n)).hom.map_smul r a).symm }

private lemma singleEvalInsert {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    insertSingle φ I n ≫ evaluateSingle φ I n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply CoextendScalars.ext
  ext a
  change (((singleZeroIso φ).inv ≫
    (Cochain.single ((singleZeroIso φ).hom ≫ ModuleCat.ofHom
      (X := (restrictScalars φ).obj (ModuleCat.of A A))
      (CoextendScalars.equiv φ (I.X n) h)) n).v 0 n (zero_add n)).hom) a =
        CoextendScalars.equiv φ (I.X n) h a
  rw [Cochain.single_v, Iso.inv_hom_id_assoc]
  rfl

private lemma singleInsertEval {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    evaluateSingle φ I n ≫ insertSingle φ I n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by lia
    subst hq
    change (Cochain.single ((singleZeroIso φ).hom ≫
      ModuleCat.ofHom (X := (restrictScalars φ).obj (ModuleCat.of A A))
        (((singleZeroIso φ).inv ≫ z.v 0 q (zero_add q)).hom)) q).v
          0 q (zero_add q) = z.v 0 q (zero_add q)
    rw [Cochain.single_v]
    exact Iso.hom_inv_id_assoc _ _
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_src _ _

private lemma singleEvalDelta {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n m : ℤ)
    (z : Cochain (A0 φ) I n) :
    evaluateSingle φ I m (δ n m z) =
      (((U φ).obj ((J φ).obj I)).d n m) (evaluateSingle φ I n z) := by
  apply CoextendScalars.ext
  ext a
  change A at a
  by_cases hnm : n + 1 = m
  · change (((singleZeroIso φ).inv ≫
      (δ n m z).v 0 m (zero_add m)).hom) a = _
    rw [δ_v n m hnm z 0 m (zero_add m) n 1 (by lia) (by lia)]
    simp only [A0, singleFunctor_obj_d,
      Limits.zero_comp, smul_zero, add_zero]
    rfl
  · rw [δ_shape n m hnm, map_zero, HomologicalComplex.shape _ n m hnm]
    rfl

private noncomputable def coinductionSingleIso {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) :
    (U φ).obj ((J φ).obj I) ≅ moduleHomComplex (A0 φ) I where
  hom :=
    { f := insertSingle φ I
      comm' := fun n m _ ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        have hinj : Function.Injective (evaluateSingle φ I m) := by
          intro a b hab
          have ha := ConcreteCategory.congr_hom (singleInsertEval φ I m) a
          have hb := ConcreteCategory.congr_hom (singleInsertEval φ I m) b
          change insertSingle φ I m (evaluateSingle φ I m a) = a at ha
          change insertSingle φ I m (evaluateSingle φ I m b) = b at hb
          rw [← ha, ← hb, hab]
        apply hinj
        change evaluateSingle φ I m (δ n m (insertSingle φ I n h)) =
          evaluateSingle φ I m (insertSingle φ I m
            ((((U φ).obj ((J φ).obj I)).d n m) h))
        rw [singleEvalDelta]
        have h1 := ConcreteCategory.congr_hom (singleEvalInsert φ I n) h
        have h2 := ConcreteCategory.congr_hom (singleEvalInsert φ I m)
          ((((U φ).obj ((J φ).obj I)).d n m) h)
        exact congrArg _ h1 |>.trans h2.symm }
  inv :=
    { f := evaluateSingle φ I
      comm' := fun n m _ ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact (singleEvalDelta φ I n m z).symm }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact singleEvalInsert φ I n
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact singleInsertEval φ I n

private noncomputable def homProjection {P : Type u} [CommRing P]
    (L I : CochainComplex (ModuleCat.{u} P) ℤ) (n p q : ℤ) (hpq : p + n = q) :
    (moduleHomComplex L I).X n ⟶ (ihom (L.X p)).obj (I.X q) :=
  ModuleCat.ofHom
    { toFun := fun z ↦ z.v p q hpq
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private noncomputable def toInternalSingle {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (moduleHomComplex (A0 φ) I).X n ⟶ (internalHomObj (A0 φ) I).X n :=
  Limits.Pi.lift fun t : Triplet n ↦ homProjection (A0 φ) I n t.p t.q t.hpq

private noncomputable def fromInternalSingle {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (internalHomObj (A0 φ) I).X n ⟶ (moduleHomComplex (A0 φ) I).X n :=
  ModuleCat.ofHom
    { toFun := fun z ↦ Cochain.mk fun p q hpq ↦ (internalHomπ (A0 φ) I n p q hpq) z
      map_add' := by
        intro z w
        apply Cochain.ext
        intro p q hpq
        exact (internalHomπ (A0 φ) I n p q hpq).hom.map_add z w
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro p q hpq
        exact (internalHomπ (A0 φ) I n p q hpq).hom.map_smul r z }

private lemma toInternalSingle_proj {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ)
    (n p q : ℤ) (hpq : p + n = q) :
    toInternalSingle φ I n ≫ internalHomπ (A0 φ) I n p q hpq =
      homProjection (A0 φ) I n p q hpq := Limits.Pi.lift_π _ _

private noncomputable def singleInternalDegreeIso {P A : Type u}
    [CommRing P] [CommRing A] (φ : P →+* A)
    (I : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) :
    (moduleHomComplex (A0 φ) I).X n ≅ (internalHomObj (A0 φ) I).X n where
  hom := toInternalSingle φ I n
  inv := fromInternalSingle φ I n
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    exact ConcreteCategory.congr_hom (toInternalSingle_proj φ I n p q hpq) z
  inv_hom_id := by
    apply internalHomObj_hom_ext
    intro p q hpq
    rw [Category.assoc, toInternalSingle_proj]
    rfl

private lemma toInternalSingle_comm {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ)
    (n m : ℤ) (hnm : n + 1 = m) :
    toInternalSingle φ I n ≫ (internalHomObj (A0 φ) I).d n m =
      (moduleHomComplex (A0 φ) I).d n m ≫ toInternalSingle φ I m := by
  apply internalHomObj_hom_ext
  intro p q hpq
  rw [Category.assoc, internalHomObj_d_π (A0 φ) I n m p q hpq
    (p + n) (p + 1) rfl (by lia), Category.assoc, toInternalSingle_proj]
  by_cases hp : p = 0
  · subst p
    simp only [Int.negOnePow_zero, one_smul,
      A0, singleFunctor_obj_d, MonoidalClosed.pre_zero_app,
      Limits.comp_zero, sub_zero]
    rw [reassoc_of% (toInternalSingle_proj φ I n 0 (0 + n) rfl)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (z.v 0 (0 + n) rfl ≫ I.d (0 + n) q) x = ((δ n m z).v 0 q hpq) x
    rw [δ_v n m hnm z 0 q hpq (0 + n) 1 (by lia) rfl]
    simp only [A0, singleFunctor_obj_d, Limits.zero_comp, smul_zero, add_zero]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp).eq_of_src _ _

private noncomputable def singleInternalIso {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) (I : CochainComplex (ModuleCat.{u} P) ℤ) :
    moduleHomComplex (A0 φ) I ≅ internalHomObj (A0 φ) I :=
  HomologicalComplex.Hom.isoOfComponents (singleInternalDegreeIso φ I)
    (toInternalSingle_comm φ I)

end

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The explicit transposition and derived adjunction involve several bundled module carriers.
/-- Coinduction transposes the product total Hom complexes in every integer degree,
with the specified action, evaluation/inverse formulas, naturality and homotopies.
It preserves K-injectives and its underlying complex computes ordinary derived Hom
on every K-injective representative. No boundedness or flatness assumption is used.

The two differential identities use Mathlib's `δ`, namely
`d(target) ∘ z - (-1)^n z ∘ d(source)`. The degree minus one identities express
transport of chain homotopies in both directions. The subsequent homotopy clause
also records termwise coinduction of a homotopy between maps of target complexes.

Source: Stacks 0A70, 0A71 and 070H
(blueprint: lem-trf-coinduction-total-hom-model).

Proof:
1. The product Hom definition (def-sc-module-total-hom-complex) for A[0] has
only the p = 0 factor. Thus its degree q is Hom_P(A,I^q). Mathlib coextension
has action (a • h)(b) = h(ba), differential d_I ∘ h and the restricted P-action.
Associativity and distributivity follow from multiplication and linearity;
postcomposition with d_I commutes with this action and squares to zero.
2. On every product factor define T(f)(x) = f(x)(1), S(g)(x)(a) = g(ax).
Linearity follows from P-linearity of g and A-linearity of f. Evaluation at 1
proves TS = id; A-linearity gives ST(f)(x)(a) = f(ax)(1) = f(x)(a).
No finite-support restriction occurs in these products.
3. Applying either formula to d_I f - (-1)^n f d_E gives the same formula
on the transposed cochain, since d_E(ax) = a d_E(x). This proves the chain
isomorphisms and both displayed differential identities in all integer degrees.
4. Precomposing by α and postcomposing by β evaluates to β(f(αx)(1)).
This gives the naturality identity; the inverse identity follows by invertibility.
5. For a chain homotopy h, def-pur-kinjective-complex gives f-g = dh+hd.
Step 3 in degree -1 transposes this equation in either direction. Postcomposition
of each coinduced factor with a homotopy k gives J(k), with the same equation.
6. Restriction preserves kernels, images and their quotient, hence acyclicity
as defined by def-weil-abstract-derived-category, without any flatness assumption.
7. If N is acyclic and I K-injective, T(f):UN → I is null-homotopic.
Transposing its null-homotopy with S gives an A-linear null-homotopy of f.
This is exactly def-pur-kinjective-complex for J(I).
8. On the one-object identity-cover site internal Hom and products are ordinary
module Hom and products. The arbitrary K-injective representative clause of
def-pur-derived-internal-hom identifies Hom_P(A[0],I) with RHom_P(A[0],Y).
Step 1 supplies the claimed underlying complex and its specified A-action. -/
theorem coinduction_total_hom_model
    {P A : Type u} [CommRing P] [CommRing A] (φ : P →+* A) :
    (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) (q : ℤ)
      (h : (((coextendScalars.{u, u, u} φ).mapHomologicalComplex (.up ℤ)).obj I).X q)
      (a b : A),
      CoextendScalars.equiv φ (I.X q) (a • h) b =
        CoextendScalars.equiv φ (I.X q) h (b * a)) ∧
    (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) (p q : ℤ)
      (h : (((coextendScalars.{u, u, u} φ).mapHomologicalComplex (.up ℤ)).obj I).X p)
      (a : A),
      CoextendScalars.equiv φ (I.X q)
          ((((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I).d p q h) a =
        I.d p q (CoextendScalars.equiv φ (I.X p) h a)) ∧
    (∀ I : CochainComplex (ModuleCat.{u} P) ℤ,
      Nonempty
        ((((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
          (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
        moduleHomComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
            ((restrictScalars φ).obj (ModuleCat.of A A))) I)) ∧
    (∃ T : ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (I : CochainComplex (ModuleCat.{u} P) ℤ),
        ((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
          (moduleHomComplex E
            (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
        moduleHomComplex
          (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) I,
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ) (n p q : ℤ) (hpq : p + n = q)
          (z : Cochain E
            (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I) n) (x : E.X p),
        (((T E I).hom.f n z).v p q hpq) x =
          CoextendScalars.equiv φ (I.X q) (z.v p q hpq x) (1 : A)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ) (n p q : ℤ) (hpq : p + n = q)
          (z : Cochain
            (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) I n)
          (x : E.X p) (a : A),
        CoextendScalars.equiv φ (I.X q) (((T E I).inv.f n z).v p q hpq x) a =
          (z.v p q hpq) (a • x)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ) (n m : ℤ)
          (z : Cochain E
            (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I) n),
        (T E I).hom.f m (δ n m z) = δ n m ((T E I).hom.f n z)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ) (n m : ℤ)
          (z : Cochain
            (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) I n),
        (T E I).inv.f m (δ n m z) = δ n m ((T E I).inv.f n z)) ∧
      (∀ (E E' : CochainComplex (ModuleCat.{u} A) ℤ)
          (I I' : CochainComplex (ModuleCat.{u} P) ℤ)
          (α : E ⟶ E') (β : I ⟶ I') (n : ℤ)
          (z : Cochain E'
            (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I) n),
        (T E I').hom.f n
            ((Cochain.ofHom α).comp
              (z.comp (Cochain.ofHom
                (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).map β))
                  (add_zero n)) (zero_add n)) =
          ((Cochain.ofHom
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map α)).comp
            ((T E' I).hom.f n z) (zero_add n)).comp (Cochain.ofHom β) (add_zero n)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ)
          (f g : E ⟶ (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I))
          (h : Homotopy f g),
        δ (-1) 0 ((T E I).hom.f (-1) (Cochain.ofHomotopy h)) =
          (T E I).hom.f 0 (Cochain.ofHom f) - (T E I).hom.f 0 (Cochain.ofHom g)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
          (I : CochainComplex (ModuleCat.{u} P) ℤ)
          (f g : (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) ⟶ I)
          (h : Homotopy f g),
        δ (-1) 0 ((T E I).inv.f (-1) (Cochain.ofHomotopy h)) =
          (T E I).inv.f 0 (Cochain.ofHom f) - (T E I).inv.f 0 (Cochain.ofHom g))) ∧
    (∀ (I I' : CochainComplex (ModuleCat.{u} P) ℤ) (β β' : I ⟶ I')
        (k : Homotopy β β'),
      ∃ H : Homotopy
          (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).map β)
          (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).map β'),
        ∀ (p q : ℤ)
          (h : (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I).X p) (a : A),
          CoextendScalars.equiv φ (I'.X q) (H.hom p q h) a =
            k.hom p q (CoextendScalars.equiv φ (I.X p) h a)) ∧
    (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ),
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) [I.IsKInjective]
        (Y : DerivedCategory (ModuleCat.{u} P)) (_ : DerivedCategory.Q.obj I ≅ Y),
      Nonempty
        (DerivedCategory.Q.obj
          (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
            (((coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
          (ordinaryModuleDerivedInternalHom P).obj
            (op (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
                ((restrictScalars φ).obj (ModuleCat.of A A)))), Y))) := by
  let : (coextendScalars.{u, u, u} φ).Additive := { map_add := by intros; rfl }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intro I
    exact ⟨coinductionSingleIso φ I⟩
  · refine ⟨transposeIso φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intros
      rfl
    · intros
      rfl
    · intros
      exact transpose_delta ..
    · intro E I n m z
      exact (ConcreteCategory.congr_hom ((transposeIso φ E I).inv.comm n m) z).symm
    · intro E E' I I' α β n z
      apply Cochain.ext
      intro p q hpq
      ext x
      change CoextendScalars.equiv φ (I'.X q)
        (((Cochain.ofHom α).comp
          (z.comp (Cochain.ofHom ((J φ).map β)) (add_zero n)) (zero_add n)).v p q hpq x)
          (1 : A) = _
      simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
        Cochain.ofHom_v]
      rfl
    · intro E I f g h
      change δ (-1) 0 (transpose φ E I (-1) _) = _
      rw [← transpose_delta, δ_ofHomotopy]
      exact map_sub (transpose φ E I 0).hom _ _
    · intro E I f g h
      have hd := ConcreteCategory.congr_hom ((transposeIso φ E I).inv.comm (-1) 0)
        (Cochain.ofHomotopy h)
      change δ (-1) 0 (untranspose φ E I (-1) (Cochain.ofHomotopy h)) =
        untranspose φ E I 0 (Cochain.ofHom f) - untranspose φ E I 0 (Cochain.ofHom g)
      change δ (-1) 0 (untranspose φ E I (-1) (Cochain.ofHomotopy h)) =
        untranspose φ E I 0 (δ (-1) 0 (Cochain.ofHomotopy h)) at hd
      rw [hd, δ_ofHomotopy]
      exact map_sub (untranspose φ E I 0).hom _ _
  · intro I I' β β' k
    exact ⟨(coextendScalars φ).mapHomotopy k, fun _ _ _ _ ↦ rfl⟩
  · intro I hI
    let := hI
    refine ⟨fun {N} f hN ↦ ?_⟩
    have hUN : ((U φ).obj N).Acyclic := fun n ↦ (hN n).map (restrictScalars φ)
    let z : Cocycle ((U φ).obj N) I 0 :=
      Cocycle.mk (transpose φ N I 0 (Cochain.ofHom f)) 1 rfl (by
        rw [← transpose_delta, δ_ofHom]
        exact map_zero _)
    let f' := Cocycle.homOf z
    let h := IsKInjective.homotopyZero f' hUN
    refine ⟨(Cochain.equivHomotopy f 0).symm
      ⟨untranspose φ N I (-1) (Cochain.ofHomotopy h), ?_⟩⟩
    have hd := ConcreteCategory.congr_hom ((transposeIso φ N I).inv.comm (-1) 0)
      (Cochain.ofHomotopy h)
    change Cochain.ofHom f = δ (-1) 0
      (untranspose φ N I (-1) (Cochain.ofHomotopy h)) + Cochain.ofHom 0
    change δ (-1) 0 (untranspose φ N I (-1) (Cochain.ofHomotopy h)) =
      untranspose φ N I 0 (δ (-1) 0 (Cochain.ofHomotopy h)) at hd
    rw [Cochain.ofHom_zero, add_zero, hd, δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
    have hf : Cochain.ofHom f' = transpose φ N I 0 (Cochain.ofHom f) :=
      Cocycle.cochain_ofHom_homOf_eq_coe z
    rw [hf]
    exact (ConcreteCategory.congr_hom (untranspose_transpose φ N I 0)
      (Cochain.ofHom f)).symm
  · intro I hI Y eY
    let P' := (HomotopyCategory.quotient (ModuleCat.{u} P) (.up ℤ)).obj (A0 φ)
    let I' := (HomotopyCategory.quotient (ModuleCat.{u} P) (.up ℤ)).obj I
    let a : DerivedCategory.Qh.obj P' ≅ DerivedCategory.Q.obj (A0 φ) :=
      (DerivedCategory.quotientCompQhIso _).app (A0 φ)
    let b : DerivedCategory.Qh.obj I' ≅ DerivedCategory.Q.obj I :=
      (DerivedCategory.quotientCompQhIso _).app I
    let c : DerivedCategory.Q.obj (internalHomObj (A0 φ) I) ≅
        (ihom (DerivedCategory.Qh.obj P')).obj (DerivedCategory.Qh.obj I') :=
      ((DerivedCategory.quotientCompQhIso _).app (internalHomObj (A0 φ) I)).symm ≪≫
        asIso ((DerivedCategory.internalHomQhObjUnit P').app I') ≪≫
        ((DerivedCategory.tensorHomAdjunctionQhObj P').rightAdjointUniq
          (ihom.adjunction (DerivedCategory.Qh.obj P'))).app _
    exact ⟨DerivedCategory.Q.mapIso (coinductionSingleIso φ I ≪≫ singleInternalIso φ I) ≪≫
      c ≪≫ (MonoidalClosed.internalHom.mapIso a.op.symm).app _ ≪≫
      (ihom (DerivedCategory.Q.obj (A0 φ))).mapIso (b ≪≫ eY)⟩

end ModuleCat
