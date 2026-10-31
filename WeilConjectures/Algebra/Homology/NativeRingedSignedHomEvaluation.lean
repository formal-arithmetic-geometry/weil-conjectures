/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorSignedCancellation
public import WeilConjectures.CategoryTheory.SignedDerivedInternalHomExact
public import WeilConjectures.SixFunctors.EvaluationShiftTransport
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.SignedDerivedInternalHomExact

/-! # Evaluation of the exact signed ringed internal Hom shift

Source: Stacks 0A8X, 08J9 and 08JC. The native tensor and the recorded Hom retain
their actual representative normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.RingedChainShift
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

attribute [local instance 100000] RingedDerivedNative.baseClosed

@[reassoc]
private theorem ι_cast (P L : RingedHomUniverses.Complex.{c, v, r} J R)
    (p q j k : ℤ) (h : j = k) (hj : p + q = j) :
    CochainComplex.ιMapBifunctor P L (curriedTensor _) p q j hj ≫
        ((CochainComplex.mapBifunctor P L (curriedTensor _)).XIsoOfEq h).hom =
      CochainComplex.ιMapBifunctor P L (curriedTensor _) p q k (hj.trans h) := by
  subst k
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

set_option maxHeartbeats 2000000 in
-- Matching total tensor shift components unfolds the fixed sheaf monoidal data.
private theorem chain_shift
    (P I : RingedHomUniverses.Complex.{c, v, r} J R) (n : ℤ) :
    (RingedDerivedNative.chainEquiv.{c, v, r} J R
        ((RingedHomUniverses.complexHom.{c, v, r} J R P I)⟦-n⟧) (P⟦n⟧) I).symm
        ((RingedHomUniverses.rawSourceIso.{c, v, r} J R I n).inv.app (op P)) =
      (CochainComplex.mapBifunctorShift₂Iso
        ((RingedHomUniverses.complexHom.{c, v, r} J R P I)⟦-n⟧) P
          (curriedTensor _) n).hom ≫
        ((CochainComplex.mapBifunctorShift₁Iso
          (RingedHomUniverses.complexHom.{c, v, r} J R P I) P (curriedTensor _) (-n)).hom)⟦n⟧' ≫
          (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).hom.app _ ≫
            (RingedDerivedNative.chainEquiv.{c, v, r} J R
              (RingedHomUniverses.complexHom.{c, v, r} J R P I) P I).symm (𝟙 _) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  simp only [HomologicalComplex.comp_f]
  rw [RingedDerivedNative.chainEquiv_symm_f.{c, v, r} J R]
  rw [RingedHomUniverses.rawSourceIso_formula.{c, v, r} J R]
  simp only [CochainComplex.shiftFunctor_obj_X', RingedHomUniverses.complexHom]
  erw [← RingedDerivedNative.nativeUncurry_eq.{c, v, r} J R,
    MonoidalClosed.uncurry_units_smul]
  rw [Linear.comp_units_smul]
  erw [RingedDerivedNative.nativeUncurry_eq.{c, v, r} J R]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc
    ((RingedHomUniverses.complexHom.{c, v, r} J R P I)⟦-n⟧) P
      (curriedTensor _) n p q k hpq (q + n) (k + n) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id,
    curriedTensor_obj_map, Linear.units_smul_comp,
    CochainComplex.shiftFunctor_map_f', Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc
    (RingedHomUniverses.complexHom.{c, v, r} J R P I) P
      (curriedTensor _) (-n) p (q + n) (k + n) (by omega)
      (p + -n) (k + n + -n) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, curriedTensor_map_app]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f]
  erw [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight]
  simp only [Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
  erw [Category.id_comp, Category.id_comp]
  rw [reassoc_of% (ι_cast.{c, v, r} J R
    (RingedHomUniverses.complexHom.{c, v, r} J R P I) P
    (p + -n) (q + n) (k + n + -n) k (by omega) (by omega))]
  erw [RingedDerivedNative.chainEquiv_symm_f.{c, v, r} J R
    (RingedHomUniverses.complexHom.{c, v, r} J R P I) P I (𝟙 _) (p + -n) (q + n) k (by omega)]
  simp only [HomologicalComplex.id_f, Category.id_comp,
    mul_comm n p]
set_option maxHeartbeats 1000000 in
-- Uncurrying transports between the explicit sheaf Hom and the closed structure.
private theorem chain_smul
    (A P I : RingedHomUniverses.Complex.{c, v, r} J R)
    (f : A ⟶ RingedHomUniverses.complexHom.{c, v, r} J R P I) (u : ℤˣ) :
    (RingedDerivedNative.chainEquiv.{c, v, r} J R A P I).symm (u • f) =
      u • (RingedDerivedNative.chainEquiv.{c, v, r} J R A P I).symm f := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [RingedDerivedNative.chainEquiv_symm_f.{c, v, r} J R]
  erw [RingedHomUniverses.units_smul_f.{c, v, r} J R,
    RingedHomUniverses.units_smul_f.{c, v, r} J R]
  rw [Linear.comp_units_smul, RingedDerivedNative.chainEquiv_symm_f.{c, v, r} J R]
  rw [Linear.units_smul_comp]
  erw [← RingedDerivedNative.nativeUncurry_eq.{c, v, r} J R,
    MonoidalClosed.uncurry_units_smul, Linear.comp_units_smul]
  erw [RingedDerivedNative.nativeUncurry_eq.{c, v, r} J R]

private theorem corrected_chain_shift
    (P I : RingedHomUniverses.Complex.{c, v, r} J R) (n : ℤ) :
    (RingedDerivedNative.chainEquiv.{c, v, r} J R
        ((RingedHomUniverses.complexHom.{c, v, r} J R P I)⟦-n⟧) (P⟦n⟧) I).symm
        ((RingedHomUniverses.correctedSourceIso.{c, v, r} J R I n).inv.app (op P)) =
      (n * (n - 1) / 2).negOnePow •
        ((CochainComplex.mapBifunctorShift₂Iso
          ((RingedHomUniverses.complexHom.{c, v, r} J R P I)⟦-n⟧) P
            (curriedTensor _) n).hom ≫
          ((CochainComplex.mapBifunctorShift₁Iso
            (RingedHomUniverses.complexHom.{c, v, r} J R P I) P
              (curriedTensor _) (-n)).hom)⟦n⟧' ≫
            (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).hom.app _ ≫
              (RingedDerivedNative.chainEquiv.{c, v, r} J R
                (RingedHomUniverses.complexHom.{c, v, r} J R P I) P I).symm (𝟙 _)) := by
  simp only [RingedHomUniverses.correctedSourceIso, Preadditive.smul_iso_inv,
    Int.units_inv_eq_self, NatTrans.app_units_zsmul]
  rw [chain_smul.{c, v, r} J R, chain_shift.{c, v, r} J R]
end CategoryTheory.RingedChainShift

namespace CategoryTheory.RingedSignedShiftUnique
variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D)
private def iso (s : F.CommShift ℤ) (n : ℤ) : shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n :=
  letI := s
  F.commShiftIso n
private theorem iso_zero (s : F.CommShift ℤ) : iso F s 0 = Functor.CommShift.isoZero F ℤ := by
  letI := s
  exact F.commShiftIso_zero ℤ
private theorem iso_add (s : F.CommShift ℤ) (n m : ℤ) :
    iso F s (n + m) = Functor.CommShift.isoAdd (iso F s n) (iso F s m) := by
  letI := s
  exact F.commShiftIso_add n m
private theorem iso_eq (s t : F.CommShift ℤ) (h₁ : iso F s 1 = iso F t 1) (n : ℤ) :
    iso F s n = iso F t n := by
  have hp (k : ℕ) : iso F s (k : ℤ) = iso F t (k : ℤ) := by
    induction k with
    | zero => rw [Nat.cast_zero, iso_zero, iso_zero]
    | succ k hk =>
      rw [Nat.cast_succ, iso_add, iso_add, hk, h₁]
  have hn (k : ℕ) : iso F s (-(k : ℤ)) = iso F t (-(k : ℤ)) := by
    have h : Functor.CommShift.isoAdd (iso F s (-(k : ℤ))) (iso F t (k : ℤ)) =
        Functor.CommShift.isoAdd (iso F t (-(k : ℤ))) (iso F t (k : ℤ)) := by
      rw [← hp k, ← iso_add, hp k, ← iso_add, neg_add_cancel, iso_zero, iso_zero]
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply (shiftFunctor D (k : ℤ)).map_injective
    have hh := congr_app (congrArg Iso.hom h) X
    simp only [Functor.CommShift.isoAdd_hom_app] at hh
    have hh := (cancel_epi (F.map
      ((shiftFunctorAdd C (-(k : ℤ)) (k : ℤ)).hom.app X))).mp hh
    have hh := (cancel_epi ((iso F t (k : ℤ)).hom.app (X⟦-(k : ℤ)⟧))).mp hh
    exact (cancel_mono _).mp hh
  cases n with
  | ofNat k => exact hp k
  | negSucc k => exact hn (k + 1)
private theorem structure_eq (s t : F.CommShift ℤ)
    (h₁ : iso F s 1 = iso F t 1) : s = t := by
  have h : s.commShiftIso = t.commShiftIso := funext (iso_eq F s t h₁)
  cases s
  cases t
  cases h
  rfl
end CategoryTheory.RingedSignedShiftUnique

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedHomUniverses.Modules.{c, v, r} J R)]

/-- Signed exact Hom shifts obey evaluation in the native tensor presentation.
Source: Stacks 0A8X and 08JC; the representative evaluation argument in
blueprint det-prop-scalar-six-tensor-hom.proof.md, Reduction.
(blueprint: lem-sfb-native-ringed-signed-hom-evaluation-Y2).

Proof: choose a K-injective representative I for M. Construct the coherent signed
contravariant Hom shifts as in signedDerivedInternalHom_exact. Coherent shifts
for the integer group are determined by degree one (proved privately above), so
h1 identifies these shifts
with the supplied structure. Resolve K by a flat-term K-flat P, and resolve
Hom(P,I) by a flat-term K-flat A. The native
closed adjunction identifies uncurrying A -> Hom(P,I) with the unsigned ordinary
evaluation x tensor y |-> phi(x)(y). In bidegree (p,q), the Hom source reindexing
for P[-n] multiplies the degree-p Hom component by (-1)^(np). Extracting the
second tensor shift -n gives exactly this coefficient; extracting the first
shift n is unsigned. The shift-composition isomorphism cancels the two shifts.
The correction from the coherent exact Hom shift is (-1)^(n(n+1)/2), as in the
signed-Hom construction. The private chain_shift proves the raw calculation on every tensor summand;
corrected_chain_shift adds the quadratic correction. Then
localize, and cancel the K-flat resolving comparison and the K-injective Hom
comparison. Naturality transports the equality along Q(P) = K and Q(I) = M.
The calculation works for arbitrary integers, including zero and negative
integers, and uses no boundedness. -/
theorem nativeRingedSignedHom_evaluation
    (M : DerivedCategory (RingedHomUniverses.Modules.{c, v, r} J R))
    [sH : (Prod.sectL _ M ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ]
    (h₁ : ∀ K, ((Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso
        (1 : ℤ)).hom.app (op K) =
      -(RingedHomUniverses.sourceShift.{c, v, r, w} J R K (-1)).inv.app M) :
    ∀ (K : DerivedCategory (RingedHomUniverses.Modules.{c, v, r} J R)) (n : ℤ),
      (RingedSignedTensor.nativeTensor.{c, v, r, w} J R).map (Prod.mkHom
        (reindexedDualShift (Prod.sectL _ M ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J R) n K).inv
        (𝟙 (K⟦-n⟧))) ≫
        RingedSignedTensor.nativeEvaluation.{c, v, r, w} J R (K⟦-n⟧) M =
      (n * (n + 1) / 2).negOnePow •
        (RingedSignedTensor.nativeCancellation.{c, v, r, w} J R K
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M)) n ≫
            RingedSignedTensor.nativeEvaluation.{c, v, r, w} J R K M) := by
  sorry

end CategoryTheory
