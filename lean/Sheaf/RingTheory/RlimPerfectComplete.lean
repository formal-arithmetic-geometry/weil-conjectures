/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.RingTheory.DerivedCompleteModuleComplex
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.FiniteConeFreeModel
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FiniteFree
import Sheaf.RingTheory.RingPseudoCoherent
import Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete
import Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction
import Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect

/-!
# Perfect inverse-limit reconstruction over a complete ring

Source: Stacks Project, More on Algebra, Tag 09AW, lemma-Rlim-perfect-gives-complete
(blueprint: lem-weil-pbc-rlim-perfect-complete).

The index `n : ℕ` denotes level `n + 1`. Derived scalar extension is specified by its
universal property as the left adjoint to exact restriction of scalars. We allow any
realization of this adjunction; all maps below are its adjoint transposes, so no arbitrary
comparison map is supplied. The derived limit includes its Roos triangle and projections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct

namespace DerivedCategory

/-- Exact restriction from the `(n+1)`st quotient to the complete ring.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicLevelRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory

/-- Exact restriction between consecutive quotient rings.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicStepRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))).mapDerivedCategory

/-- The canonical identification of iterated restriction with direct restriction.
Source: Stacks Project, Tag 09AW; both underived maps send every element to itself.
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicRestrictionComp {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    adicLevelRestriction I n ≅ adicStepRestriction I n ⋙ adicLevelRestriction I (n + 1) :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc I (n + 1))
      (Ideal.Quotient.mk (I ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Restrict a supplied transition in `D(A/I^(n+2))` to `D(A)`.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicTowerTransition {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n)) (n : ℕ) :
    (adicLevelRestriction I (n + 1)).obj (K (n + 1)) ⟶
      (adicLevelRestriction I n).obj (K n) :=
  (adicLevelRestriction I (n + 1)).map (t n) ≫ (adicRestrictionComp I n).inv.app (K n)

/-- The canonical reduction map: transpose the projection of the specified Roos triangle.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicLimitReduction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))) (n : ℕ) :
    (L n).obj C ⟶ K n :=
  ((adj n).homEquiv C (K n)).symm (p ≫ Pi.π _ n)

set_option backward.isDefEq.respectTransparency false in
private theorem pseudoCoherent_of_perfect {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (X : DerivedCategory (ModuleCat.{u} R)) (hX : IsPerfect X) : IsPseudoCoherent X := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hX
  have : P.IsStrictlyLE b := hb
  obtain ⟨F, hFb, hF, f, hf⟩ := exists_finiteFree_model_of_finite_cones R P b
    (fun i hi ↦ (P.exactAt_of_isLE b i hi).isZero_homology.of_iso
      ((homologyFunctorFactors _ i).app P)) (by
      intro F c d hFc hFd hF f n hn
      let T := CochainComplex.mappingCone f
      have : F.IsStrictlyLE d := hFd
      have : T.IsStrictlyLE (max (d - 1) b) := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro i hi
        exact (CochainComplex.mappingCone.isZero_X_iff f i).mpr
          ⟨F.isZero_of_isStrictlyLE d (i + 1) (by omega),
            P.isZero_of_isStrictlyLE b i (by omega)⟩
      have hT (i : ℤ) : Module.Projective R (T.X i) ∧ Module.Finite R (T.X i) := by
        have := (hF (i + 1)).1
        have := (hF (i + 1)).2
        have := (hP i).1
        have := (hP i).2
        let eT := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl) ≪≫
          ModuleCat.biprodIsoProd (F.X (i + 1)) (P.X i)
        exact ⟨Module.Projective.of_equiv eT.toLinearEquiv.symm,
          Module.Finite.equiv eT.toLinearEquiv.symm⟩
      have hex (i : ℤ) (hi : n < i) : T.ExactAt i := by
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact (hn i hi).of_iso ((homologyFunctorFactors _ i).app T).symm
      have hker := (CochainComplex.projective_finite_ker_d_of_exactAt T
        (max (d - 1) b) hT hex n le_rfl).2
      let ec := (T.cyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp)) ≪≫
        (T.sc' (n - 1) n (n + 1)).moduleCatCyclesIso
      have : Module.Finite R ((T.sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.K) :=
        hker
      have : Module.Finite R (T.cycles n) := Module.Finite.equiv ec.toLinearEquiv.symm
      have : Module.Finite R (T.homology n) :=
        Module.Finite.of_surjective (T.homologyπ n).hom
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      let eh : (homologyFunctor (ModuleCat.{u} R) n).obj (Q.obj T) ≅ T.homology n :=
        (homologyFunctorFactors _ n).app T
      exact Module.Finite.equiv eh.toLinearEquiv.symm)
  have : IsIso (Q.map f) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} R) f).mpr hf
  exact ⟨F, b, hFb, hF, ⟨asIso (Q.map f) ≪≫ e.symm⟩⟩

private theorem adic_compatible_lift {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] (x : ∀ n : ℕ, A ⧸ I ^ (n + 1))
    (hx : ∀ n, Ideal.Quotient.factorPowSucc I (n + 1) (x (n + 1)) = x n) :
    ∃! a : A, ∀ n, Ideal.Quotient.mk (I ^ (n + 1)) a = x n := by
  classical
  choose r hr using fun n ↦ Ideal.Quotient.mk_surjective (x n)
  have heq (n : ℕ) : (I ^ n • ⊤ : Submodule A A) = I ^ n := Ideal.mul_top _
  have hxy {m n : ℕ} (h : m ≤ n) :
      Ideal.Quotient.mk (I ^ (m + 1)) (r n) =
        Ideal.Quotient.mk (I ^ (m + 1)) (r m) := by
    have hcompat := Ideal.Quotient.eq_factor_of_eq_factor_succ
      (I := fun n ↦ I ^ (n + 1)) (fun m n h ↦ Ideal.pow_le_pow_right
        (Nat.add_le_add_right h 1)) x (fun n ↦ (hx n).symm) h
    simpa only [← hr, Ideal.Quotient.factor_mk] using hcompat.symm
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      r m ≡ r n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n h
    rw [heq, SModEq.sub_mem]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (Ideal.Quotient.eq.mp (hxy h).symm)
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' r hcauchy
  have hval (n : ℕ) : Ideal.Quotient.mk (I ^ (n + 1)) a = x n := by
    have hn := ha (n + 1)
    rw [heq, SModEq.sub_mem] at hn
    exact (Ideal.Quotient.eq.mpr hn).symm.trans ((hxy (Nat.le_succ n)).trans (hr n))
  refine ⟨a, hval, ?_⟩
  intro b hb
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [heq, SModEq.sub_mem]
  exact Ideal.pow_le_pow_right (Nat.le_succ n)
    (Ideal.Quotient.eq.mp ((hb n).trans (hval n).symm))

private theorem restriction_smul_id_eq_zero {A S : Type u} [CommRing A] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)]
    (q : A →+* S) (a : A) (ha : q a = 0)
    (X : DerivedCategory (ModuleCat.{u} S)) :
    a • 𝟙 ((ModuleCat.restrictScalars q).mapDerivedCategory.obj X) = 0 := by
  let P := Q.objPreimage X
  let e := (ModuleCat.restrictScalars q).mapDerivedCategory.mapIso (Q.objObjPreimageIso X)
  let e' := (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.app P
  have hP : a • 𝟙 (((ModuleCat.restrictScalars q).mapHomologicalComplex (.up ℤ)).obj P) =
      0 := by
    ext i x
    change a • x = 0
    rw [ModuleCat.restrictScalars.smul_def, ha, zero_smul]
  have hQ : a • 𝟙 (Q.obj
      (((ModuleCat.restrictScalars q).mapHomologicalComplex (.up ℤ)).obj P)) = 0 := by
    rw [← Q.map_id, ← Functor.map_smul, hP, Q.map_zero]
  let f := e'.symm ≪≫ e
  apply (cancel_epi f.hom).mp
  calc
    f.hom ≫ (a • 𝟙 ((ModuleCat.restrictScalars q).mapDerivedCategory.obj X)) =
        (a • 𝟙 (Q.obj
          (((ModuleCat.restrictScalars q).mapHomologicalComplex (.up ℤ)).obj P))) ≫
          f.hom := by simp
    _ = 0 := by rw [hQ]; simp
    _ = f.hom ≫ 0 := by simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorExtensionIso {A S : Type u} [CommRing A] [CommRing S]
    (q : A →+* S) :
    tensorRight ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) ≅
      ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars q := by
  let : Algebra A S := q.toAlgebra
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let : Module A ((ModuleCat.extendScalars q).obj M) :=
      inferInstanceAs (Module A ((ModuleCat.restrictScalars q).obj
        ((ModuleCat.extendScalars q).obj M)))
    have : IsScalarTower A S ((ModuleCat.extendScalars q).obj M) :=
      IsScalarTower.of_compHom A S _
    exact ((TensorProduct.comm A M S).trans
      ((ModuleCat.tensorEquivExtendScalars A S M).restrictScalars A)).toModuleIso
  · intro M N f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x s
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fibre_vanishes_of_perfect_reduction
    {A S : Type u} [CommRing A] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)] (q : A →+* S)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (c : ℤ) (hPc : P.IsStrictlyLE c)
    (hP : ∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (B : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    (ha : B.IsStrictlyGE a) (hb : B.IsStrictlyLE b)
    (hB : ∀ i, Module.Projective S (B.X i) ∧ Module.Finite S (B.X i))
    (e : Q.obj (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) ≅
      Q.obj B)
    (F : Type u) [CommRing F] (r : S →+* F) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (Q.obj P ⊗ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (r.comp q)).obj (ModuleCat.of F F)))) := by
  have : P.IsStrictlyLE c := hPc
  have : B.IsStrictlyGE a := ha
  have : B.IsStrictlyLE b := hb
  let E : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  have : E.IsStrictlyLE c := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (ModuleCat.extendScalars q).map_isZero (P.isZero_of_isStrictlyLE c j hj)
  have hEflat (j : ℤ) : Module.Flat S (E.X j) := by
    have := (hP j).1
    let : Algebra A S := q.toAlgebra
    exact Module.Flat.of_linearEquiv (ModuleCat.tensorEquivExtendScalars A S (P.X j)).symm
  have hBflat (j : ℤ) : Module.Flat S (B.X j) := by
    have := (hB j).1
    infer_instance
  obtain ⟨eh⟩ := CochainComplex.nonempty_kFlat_scalarExtension_homology_linearEquiv r E B
    (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat E
      ⟨c, fun j hj ↦ E.isZero_of_isStrictlyLE c j hj⟩ hEflat)
    (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat B
      ⟨b, fun j hj ↦ B.isZero_of_isStrictlyLE b j hj⟩ hBflat) e i
  let B' := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj B
  have hBi : IsZero (B'.homology i) := by
    have hz : IsZero (B'.X i) := by
      apply (ModuleCat.extendScalars r).map_isZero
      rcases hi with hi | hi
      · exact B.isZero_of_isStrictlyGE a i hi
      · exact B.isZero_of_isStrictlyLE b i hi
    exact (B'.sc i).isZero_homology_of_isZero_X₂ hz
  have hEi : IsZero
      ((((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E).homology i) :=
    hBi.of_iso eh.toModuleIso
  let := (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
  let := (ModuleCat.extendRestrictScalarsAdj r).left_adjoint_additive
  let := (ModuleCat.extendRestrictScalarsAdj (r.comp q)).left_adjoint_additive
  let ec := (Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp q r).symm (.up ℤ)).app P
  have hext : IsZero
      ((((ModuleCat.extendScalars (r.comp q)).mapHomologicalComplex (.up ℤ)).obj P).homology i) :=
    hEi.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso ec).symm
  let er := (Functor.mapHomologicalComplexCompIso (Iso.refl
    (ModuleCat.extendScalars (r.comp q) ⋙ ModuleCat.restrictScalars (r.comp q)))
      (.up ℤ)).app P
  let et := (NatIso.mapHomologicalComplex (tensorExtensionIso (r.comp q)) (.up ℤ)).app P
  let et' := et ≪≫ er.symm
  have hten : IsZero
      ((((tensorRight ((ModuleCat.restrictScalars (r.comp q)).obj
        (ModuleCat.of F F))).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
    have hs := (ModuleCat.restrictScalars (r.comp q)).map_isZero hext
    exact hs.of_iso (((HomologicalComplex.homologyFunctor _ _ i).mapIso et') ≪≫
      ModuleCat.restrictScalarsHomologyIso _ _ _)
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P c (fun j ↦ by
    have := (hP j).1
    exact (ModuleCat.flat_iff_flat _).mpr inferInstance)
  exact hten.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (DerivedCategory.QObjTensorSingleFunctorObjIso P hPk _) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem perfect_of_adic_model {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (0 + 1)))]
    (C : DerivedCategory (ModuleCat.{u} A)) (hpc : IsPseudoCoherent C)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (c : ℤ) (hPbound : P.IsStrictlyLE c)
    (hPf : ∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) (β : Q.obj P ≅ C)
    (D : CochainComplex (ModuleCat.{u} (A ⧸ I ^ (0 + 1))) ℤ)
    (a b : ℤ) (ha : D.IsStrictlyGE a) (hb : D.IsStrictlyLE b)
    (hD : ∀ i, Module.Projective (A ⧸ I ^ (0 + 1)) (D.X i) ∧
      Module.Finite (A ⧸ I ^ (0 + 1)) (D.X i))
    (eD : Q.obj
      ((((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex
        (.up ℤ)).obj P)) ≅ Q.obj D) : IsPerfect C := by
  apply (isPerfect_and_tensor_homology_vanish_of_maximal_fibres C hpc
    (min a b) b (min_le_right _ _) ?_).1
  intro m hm i hi
  have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans
    (sInf_le ⟨bot_le, hm⟩)
  let r : (A ⧸ I ^ (0 + 1)) →+* (A ⧸ m) :=
    Ideal.Quotient.factor (by simpa using hIm)
  have hcomp : r.comp (Ideal.Quotient.mk (I ^ (0 + 1))) = Ideal.Quotient.mk m :=
    Ideal.Quotient.factor_comp_mk _
  have hz := fibre_vanishes_of_perfect_reduction
    (Ideal.Quotient.mk (I ^ (0 + 1))) P c hPbound hPf D a b ha hb hD
    eD (A ⧸ m) r i
    (hi.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)
  rw [hcomp] at hz
  exact hz.of_iso ((homologyFunctor _ i).mapIso
    (MonoidalCategory.whiskerRightIso β _)).symm

/-- The part of a finite-free reconstruction needed by the residue-fibre argument. -/
private structure InitialReductionModel {A S : Type u} [CommRing A] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)] (q : A →+* S)
    (C : DerivedCategory (ModuleCat.{u} A)) (K : DerivedCategory (ModuleCat.{u} S)) where
  P : CochainComplex (ModuleCat.{u} A) ℤ
  b : ℤ
  upper : P.IsStrictlyLE b
  finiteFree : ∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)
  β : Q.obj P ≅ C
  reduction : Q.obj (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) ≅ K

-- Project the generic reconstruction before substituting the adic quotient functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reconstruction_initial_model
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n, HasDerivedCategory.{u} (ModuleCat.{u} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{u} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{u} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{u} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPseudoCoherent E ∧
    (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) ∧
    Nonempty (InitialReductionModel (q 0) E (Eₙ 0)) := by
  have h := isPseudoCoherent_inverse_ring_reconstruction.{u, u, u}
    R φ hsurj hnil A q hq hlim L adjφ M adjq χ hχ Eₙ t hred hpc E pE δ hE
  refine ⟨h.1, h.2.1, ?_⟩
  obtain ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ, hmodels⟩ := h.2.2
  exact ⟨⟨P, b, hmodels.2.2.2.2.2.1, hmodels.2.2.2.2.2.2.1, β,
    Q.mapIso (θ 0) ≪≫ βₙ 0⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Perfect compatible reductions reconstruct a perfect, derived complete object, and its
projection-induced reductions are isomorphisms compatible with the transition maps.
Source: Stacks Project, More on Algebra, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete).

Proof:
1. Represent `K 0` by a bounded finite-projective complex. Successively add contractible
   two-term complements, starting at the top degree, to make a bounded-above finite-free
   representative. Each degree changes only twice, so the contracting homotopies assemble.
   Thus `K 0` is pseudo-coherent (`def-pc-ring-pseudo-coherent-complex`).
2. The quotient transitions are surjective with square-zero kernels. Completeness identifies
   their inverse limit with `A`. Apply `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction`
   to obtain compatible finite-free models and a bounded-above finite-free limit model,
   with projection-induced reduction isomorphisms. In particular the limit is pseudo-coherent.
3. Every maximal ideal contains `I` by `lem-weil-pbc-adic-complete-jacobson-radical`.
   Tensor the finite-free models with each residue field. K-flatness
   (`lem-pc-kflat-closure`) and derived change of rings (`lem-pur-derived-change-of-rings`)
   identify this with tensoring the bounded finite-projective model of `K 0`. Its fixed
   interval bounds all these residue-field cohomologies uniformly.
4. Apply `lem-weil-pbc-pseudocoherent-maximal-fibre-perfect` to conclude perfectness.
5. For `f ∈ I`, multiplication by `f^(n+1)` on the restricted `K n` is zero. Apply
   `lem-weil-pbc-nilpotent-torsion-derived-limit-complete` to obtain derived completeness
   in the vanishing sense of `def-weil-point-derived-complete-module-complex`.
6. Projections of the strict inverse-limit model commute with every transition. The
   reduction maps send `x ⊗ a` to `a` times the projection of `x`, so the same equalities
   hold after reduction and passage to the derived category. Adjoint transposition identifies
   these maps with `adicLimitReduction`; iterating the displayed consecutive-level equality
   gives compatibility for all pairs of levels. -/
theorem rlim_perfect_complete {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n))
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (B : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (badj : ∀ n : ℕ, B n ⊣ adicStepRestriction I n)
    (hbase : ∀ n : ℕ, IsIso (((badj n).homEquiv (K (n + 1)) (K n)).symm (t n)))
    (hperfect : IsPerfect (K 0))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)))
    (δ : ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)) ⟶ C⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (adicTowerTransition I K t) C p δ) :
    IsPerfect C ∧ IsDerivedComplete I C ∧
      (∀ n : ℕ, IsIso (adicLimitReduction I K L adj C p n)) ∧
      ∀ n : ℕ,
        (adj (n + 1)).unit.app C ≫
            (adicLevelRestriction I (n + 1)).map (adicLimitReduction I K L adj C p (n + 1)) ≫
            adicTowerTransition I K t n =
          (adj n).unit.app C ≫
            (adicLevelRestriction I n).map (adicLimitReduction I K L adj C p n) := by
  let : HasProduct (fun n : ℕ ↦
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj
        (K n)) := ‹HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))›
  have hpc := pseudoCoherent_of_perfect (K 0) hperfect
  have hnil (n : ℕ) : IsNilpotent
      (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))) := by
    refine ⟨2, ?_⟩
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
    change Ideal.map _ _ = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact Ideal.pow_le_pow_right (by omega)
  have hrecon := reconstruction_initial_model
    (fun n ↦ A ⧸ I ^ (n + 1)) (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))
    (fun n ↦ Ideal.Quotient.factor_surjective _) hnil A
    (fun n ↦ Ideal.Quotient.mk (I ^ (n + 1)))
    (fun n ↦ (Ideal.Quotient.factor_comp_mk _).symm)
    (adic_compatible_lift I) B badj L adj (adicRestrictionComp I)
    (by
      intro n P
      dsimp only [adicRestrictionComp, adicLevelRestriction, adicStepRestriction,
        Iso.trans_hom, NatTrans.comp_app]
      have hc := Functor.mapDerivedCategoryCompIso_fac
        (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) P
      simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at hc
      erw [Q.map_id, Category.comp_id] at hc
      erw [Category.assoc, hc]
      exact Functor.mapDerivedCategoryNatIso_fac _ P)
    K t hbase hpc C p δ hlim
  refine ⟨?_, ?_, hrecon.2.1, ?_⟩
  · obtain ⟨models⟩ := hrecon.2.2
    obtain ⟨D, a, b, ha, hb, hD, ⟨eD⟩⟩ := hperfect
    exact perfect_of_adic_model I C hrecon.1 models.P models.b models.upper
      models.finiteFree models.β D a b ha hb hD
      (models.reduction ≪≫ eD)
  · apply isDerivedComplete_of_isDerivedLimit_of_nilpotent I
      (fun n ↦ (adicLevelRestriction I n).obj (K n)) (adicTowerTransition I K t) ?_
      C ⟨p, δ, hlim⟩
    intro a ha n
    refine ⟨n + 1, by omega, ?_⟩
    exact restriction_smul_id_eq_zero (Ideal.Quotient.mk (I ^ (n + 1)))
      (a ^ (n + 1)) (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha _)) (K n)
  · intro n
    have hp : p ≫ towerTransitionEndomorphism (adicTowerTransition I K t) = 0 :=
      Pretriangulated.comp_distTriang_mor_zero₁₂ _ hlim
    have hn := congrArg (fun f ↦ f ≫ Pi.π _ n) hp
    have hn' : p ≫ Pi.π _ n =
        p ≫ Pi.π _ (n + 1) ≫ adicTowerTransition I K t n := by
      simpa [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
        Category.assoc, sub_eq_zero] using hn
    have hred (m : ℕ) : (adj m).unit.app C ≫
        (adicLevelRestriction I m).map (adicLimitReduction I K L adj C p m) =
        p ≫ Pi.π _ m := by
      exact ((adj m).homEquiv C (K m)).apply_symm_apply (p ≫ Pi.π _ m)
    rw [← Category.assoc, hred, hred]
    simpa only [Category.assoc] using hn'.symm

end DerivedCategory
