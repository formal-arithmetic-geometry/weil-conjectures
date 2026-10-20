/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplex
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Bounded flat models on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 08G1, equivalence (1)-(2)
(blueprint: lem-sp-ringed-site-tor-flat-model).

The tensor is the existing K-flat localization `wfSiteDerivedTensor`. The site object
and morphism universes are independent; the module and coefficient universe contains both.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped ZeroObject

namespace SheafOfModules

/-- Tor amplitude in `[a,b]` is equivalent to a termwise flat representative supported in
exactly that interval on an arbitrary small ringed site. There is no constructibility,
constant-coefficient or enough-points hypothesis.

Source: Stacks Project, Tag 08G1, equivalence (1)-(2)
(blueprint: lem-sp-ringed-site-tor-flat-model).

Proof:
1. For a flat-term K-flat complex T and any module sheaf M, choose a flat-term K-flat
   resolution C -> M[0] by [lem-pc-kflat-resolution]. Its cone is acyclic by
   [lem-pur-quasi-iso-cone-acyclic]. The tensor-cone isomorphism
   [lem-pc-tensor-mapping-cone-iso] and K-flatness [def-pc-kflat-complex] show that
   T tensor C -> T tensor M[0] is a quasi-isomorphism. Signed symmetry comes from
   [lem-pc-sheaf-modules-tensor-closed]. The comparison in
   [lem-weil-pbc-site-derived-tensor-descent] therefore identifies the latter ordinary
   tensor with the derived tensor of QT and M[0]. This does not assume M[0] is K-flat.
2. A bounded flat representative P is K-flat by [lem-pc-bounded-above-flat-kflat-site].
   Step 1 computes its derived tensor with M by the complex with terms P^i tensor M
   [def-pc-tensor-complex-sheaves], which is zero outside [a,b]. This proves (2) -> (1).
3. Conversely, test (1) on the tensor unit R. The unit is flat by tensor closedness,
   and Step 1 identifies K tensor R with K, so K has cohomology only in [a,b].
   The standard t-structure representative characterization
   [def-sbc-standard-tstructure-derived-category] gives L representing K with L^i=0 for i>b.
4. Apply [lem-pc-kflat-bounded-flat-replacement] with the bound b to get F -> L, a
   quasi-isomorphism with flat terms and F^i=0 for i>b. Thus QF is isomorphic to K.
5. F is K-flat by [lem-pc-bounded-above-flat-kflat-site]. Step 1 and (1) give exactness
   of F tensor M[0] in degree a-1 for every M. Symmetry interchanges the factors, with
   no sign from M[0]. The site criterion [lem-weil-pbc-site-flat-opcycles-tor-criterion]
   proves that B = coker(F^(a-1) -> F^a) is flat.
6. Form the good lower truncation P: zero below a, B in degree a, and F^i above a.
   The differential out of B is induced by d_F, since d_F squared is zero
   [def-pc-cochain-complex-modules]. The quotient map F -> P induces an isomorphism
   on cohomology: at a its kernel is ker(d_F^a)/im(d_F^(a-1)); at a+1 the incoming
   image is unchanged because F^a -> B is epic; higher degrees are unchanged, and
   below a both cohomologies vanish. Thus it is a quasi-isomorphism
   [def-weil-abstract-derived-category]. The terms of P are flat (B by Step 5, higher
   terms by Step 4, zero terms by exactness of zero tensor). Since a <= b, P is zero
   outside [a,b] and QP is isomorphic to K, proving (1) -> (2).
-/
theorem torAmplitude_iff_exists_bounded_flat_model
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (K : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (a b : ℤ) (_hab : a ≤ b) :
    (∀ (M : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
        (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((wfSiteDerivedTensor J R).obj (K, (DerivedCategory.singleFunctor _ 0).obj M)))) ↔
    ∃ P : CochainComplex (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ,
      (∀ i : ℤ, IsFlatOnSite (C := C) (J := J) (R := R) (P.X i)) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  classical
  let A := SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  let := (nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := hasFunctorialFlatResolution_kfi R
  have : IsGrothendieckAbelian.{max u v} A :=
    isGrothendieckAbelianOfUniverses.{u, v, max u v, 0} J _
  have : ∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso A (.up ℤ)) := by infer_instance
  have hflat (M : A) : ObjectProperty.flat M ↔ IsFlatOnSite (J := J) (R := R) M := by
    refine ⟨fun h ↦ ?_, flat_to_cat R M⟩
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm h.2
  have hcomp (M : A) : Nonempty
      ((wfSiteDerivedTensor J R).obj (K, (DerivedCategory.singleFunctor A 0).obj M) ≅
        K ⊗ (DerivedCategory.singleFunctor A 0).obj M) := by
    let L := DerivedCategory.Q.objPreimage K
    obtain ⟨P, p, hp, hP, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
    have : QuasiIso p := hp
    let e : DerivedCategory.Q.obj P ≅ K :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    have hk' : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) P := by
      intro Z hZ
      let T := tensorRight P
      have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
        rw [quasiIso_iff]
        intro i
        exact (quasiIsoAt_iff_exactAt _ i
          ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
      have : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
      have ht : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
        HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
      exact fun i ↦ (exactAt_iff_of_quasiIsoAt
        (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (ht i)
    let S := (CochainComplex.singleFunctor A 0).obj M
    obtain ⟨c⟩ := wfSiteDerivedTensor_first J R P S hk' (fun n ↦ (hP n).2)
    let s := (DerivedCategory.singleFunctorIsoCompQ A 0).app M
    let d : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj S ≅
        DerivedCategory.Q.obj (P ⊗ S) :=
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P S hk
    let t : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj S ≅
        K ⊗ (DerivedCategory.singleFunctor A 0).obj M := tensorIso e s.symm
    let r := ((wfSiteDerivedTensor J R).mapIso (Iso.prod e s.symm)).symm
    exact ⟨r ≪≫ c.symm ≪≫ d.symm ≪≫ t⟩
  have hamp :
      (∀ (M : A) (i : ℤ), i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor A i).obj
          ((wfSiteDerivedTensor J R).obj
            (K, (DerivedCategory.singleFunctor A 0).obj M)))) ↔
        DerivedCategory.torAmplitudeIn A a b K := by
    constructor
    · intro h M
      obtain ⟨e⟩ := hcomp M
      exact ⟨(DerivedCategory.isGE_iff _ a).2 (fun i hi ↦
        (h M i (Or.inl hi)).of_iso ((DerivedCategory.homologyFunctor A i).mapIso e).symm),
        (DerivedCategory.isLE_iff _ b).2 (fun i hi ↦
        (h M i (Or.inr hi)).of_iso ((DerivedCategory.homologyFunctor A i).mapIso e).symm)⟩
    · intro h M i hi
      obtain ⟨e⟩ := hcomp M
      apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor A i).mapIso e)
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff _ a).1 (h M).1 i hi
      · exact (DerivedCategory.isLE_iff _ b).1 (h M).2 i hi
  rw [hamp, DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat]
  constructor
  · rintro ⟨P, hge, hle, hP, ⟨e⟩⟩
    refine ⟨P, fun i ↦ (hflat _).1 (hP i), ?_, ⟨e.symm⟩⟩
    intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · rintro ⟨P, hP, hb, ⟨e⟩⟩
    have hge : P.IsStrictlyGE a :=
      (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hb i (Or.inl hi))
    have hle : P.IsStrictlyLE b :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hb i (Or.inr hi))
    exact ⟨P, hge, hle, fun i ↦ (hflat _).2 (hP i), ⟨e.symm⟩⟩

end SheafOfModules
