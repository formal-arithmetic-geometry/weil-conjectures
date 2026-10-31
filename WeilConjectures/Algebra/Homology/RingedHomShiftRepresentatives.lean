/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
import all WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Representatives for the normalized covariant Hom shift

The comparison maps below are composites of existing fixed comparisons.
Source: Stacks 06YS, 079P, 0A8X and 08JC.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory.RingedHomShift

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The fixed ordinary-to-derived Hom comparison followed by change of representatives.
Source: Stacks 0A95 (blueprint: lem-sf-ringed-hom-shift-representatives). -/
def comparison (P I : RingedHomUniverses.Complex.{c, v, u} J R)
    {K M : RingedHomUniverses.D.{c, v, u, w} J R}
    (eK : DerivedCategory.Q.obj P ≅ K) (eM : DerivedCategory.Q.obj I ≅ M) :
    DerivedCategory.Q.obj (RingedHomUniverses.complexHom.{c, v, u} J R P I) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, M) :=
  ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I ≫
    (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (Prod.mkHom eK.inv.op eM.hom)

/-- The shifted target representative, using the localization's recorded shift comparison.
Source: Stacks 079P (blueprint: lem-sf-ringed-hom-shift-representatives). -/
def shiftedIso {I : RingedHomUniverses.Complex.{c, v, u} J R}
    {M : RingedHomUniverses.D.{c, v, u, w} J R}
    (eM : DerivedCategory.Q.obj I ≅ M) (n : ℤ) :
    DerivedCategory.Q.obj (I⟦n⟧) ≅ M⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app I ≪≫ (shiftFunctor _ n).mapIso eM

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem flatShift (A : RingedHomUniverses.Complex.{c, v, u} J R)
    (hA : TensorFlatRepresentative (J := J) (R := R) A) (n : ℤ) :
    TensorFlatRepresentative (J := J) (R := R) (A⟦n⟧) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  refine ⟨?_, fun i ↦ hA.2 (i + n)⟩
  intro F hF
  have ht := hA.1 F hF
  have hs : (CochainComplex.mapBifunctor F A (MonoidalCategory.curriedTensor _)⟦n⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (RingedTensorModules.{c, v, u} J R)).le_shift
      n _ ht
  intro i
  exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso F A
    (MonoidalCategory.curriedTensor _) n).symm

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem flatResolution (B : RingedHomUniverses.Complex.{c, v, u} J R) :
    ∃ (A : RingedHomUniverses.Complex.{c, v, u} J R) (a : A ⟶ B),
      TensorFlatRepresentative (J := J) (R := R) A ∧ QuasiIso a := by
  obtain ⟨A, a, hA, hflat, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients B
  refine ⟨A, a, ⟨hA, ?_⟩, ha⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (A.X i)).symm (hflat i)

/-- Step 3 of the target-shift evaluation plan, including the resolutions needed to test it.
Source: Stacks 06YS, 079P, 0A8X and 08JC
(blueprint: lem-sf-ringed-hom-shift-representatives).

Proof: represent K by a flat-term K-flat P and M by a K-injective I, with the displayed
localization isomorphisms. Resolve Hom(P,I) by a flat-term K-flat map a from A. The normalized
right shift supplies u, the unsigned projection-identity isomorphism from Hom(P,I)[n] to
Hom(P,I[n]). Set b = a[n] followed by u. Shifts preserve flat-term K-flat complexes and
K-injective complexes. Quasi-isomorphisms and the ordinary comparison on K-injectives are
inverted by Q, so Qb followed by comparison is invertible. The RightNormalization equation,
precomposed with Qa[n], Q's shift naturality, and target naturality along eM, give the last
square. No tensor structure or evaluation equation is used here. -/
theorem exists_normalized_representatives
    (K M : RingedHomUniverses.D.{c, v, u, w} J R) (n : ℤ) :
    ∃ (P I A : RingedHomUniverses.Complex.{c, v, u} J R)
      (eK : DerivedCategory.Q.obj P ≅ K) (eM : DerivedCategory.Q.obj I ≅ M)
      (u : (RingedHomUniverses.complexHom.{c, v, u} J R P I)⟦n⟧ ≅
        RingedHomUniverses.complexHom.{c, v, u} J R P (I⟦n⟧))
      (a : A ⟶ RingedHomUniverses.complexHom.{c, v, u} J R P I),
      TensorFlatRepresentative (J := J) (R := R) P ∧
      TensorFlatRepresentative (J := J) (R := R) A ∧
      TensorFlatRepresentative (J := J) (R := R) (A⟦n⟧) ∧
      I.IsKInjective ∧ (I⟦n⟧).IsKInjective ∧
      RingedHomUniverses.RightFormula.{c, v, u} J R P I n u ∧
      IsIso (DerivedCategory.Q.map (a⟦n⟧' ≫ u.hom) ≫
        comparison.{c, v, u, w} J R P (I⟦n⟧) eK (shiftedIso.{c, v, u, w} J R eM n)) ∧
      (DerivedCategory.Q.map (a⟦n⟧' ≫ u.hom) ≫
          comparison.{c, v, u, w} J R P (I⟦n⟧) eK (shiftedIso.{c, v, u, w} J R eM n)) ≫
          ((RingedHomUniverses.hom.{c, v, u, w} J R K).commShiftIso n).hom.app M =
        (DerivedCategory.Q.commShiftIso n).hom.app A ≫
          (DerivedCategory.Q.map a ≫ comparison.{c, v, u, w} J R P I eK eM)⟦n⟧' := by
  classical
  let Q : RingedHomUniverses.Complex.{c, v, u} J R ⥤
      RingedHomUniverses.D.{c, v, u, w} J R := DerivedCategory.Q
  let H := derivedInternalHomOfUniverses.{c, v, u, w} J R
  let : IsGrothendieckAbelian.{max c v u} (RingedHomUniverses.Modules.{c, v, u} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  obtain ⟨P, p, hP, hp⟩ := flatResolution.{c, v, u} J R (Q.objPreimage K)
  have : QuasiIso p := hp
  let eK : Q.obj P ≅ K := asIso (Q.map p) ≪≫ Q.objObjPreimageIso K
  let N := Q.objPreimage M
  let I := (coefficientHomResolution.{u, c, v} J R).obj N
  let η := (ringedSiteHomAugmentation.{c, v, u} J R).app N
  have hI : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ N
  have : I.IsKInjective := hI
  have : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ N).2
  let eM : Q.obj I ≅ M := (asIso (Q.map η)).symm ≪≫ Q.objObjPreimageIso M
  obtain ⟨A, a, hA, ha⟩ :=
    flatResolution.{c, v, u} J R (RingedHomUniverses.complexHom.{c, v, u} J R P I)
  have : QuasiIso a := ha
  obtain ⟨u, hu, hn⟩ :=
    (RingedHomUniverses.rightShift_existsUnique.{c, v, u, w} J R).exists.choose_spec
      K P I eK n
  let eMn := shiftedIso.{c, v, u, w} J R eM n
  have hi : IsIso (ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P (I⟦n⟧)) :=
    RingedHomUniverses.comparison_isIso_of_kInjective.{c, v, u, w} J R P (I⟦n⟧)
  have hm : IsIso (H.map (Prod.mkHom eK.inv.op eMn.hom)) := by
    change IsIso ((H.mapIso (eK.symm.op.prod eMn)).hom)
    infer_instance
  refine ⟨P, I, A, eK, eM, u, a, hP, hA, flatShift.{c, v, u} J R A hA n,
    hI, inferInstance, hu, ?_, ?_⟩
  · dsimp only [comparison]
    rw [Functor.map_comp]
    infer_instance
  · let qI := (Q.commShiftIso n).hom.app I
    let δ := ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P I
    let δn := ringedSiteOrdinaryHomComparison.{c, v, u, w} J R P (I⟦n⟧)
    have hmapn : H.map (Prod.mkHom eK.inv.op eMn.hom) =
        H.map (Prod.mkHom eK.inv.op qI) ≫
          H.map (Prod.mkHom (𝟙 (op K)) (eM.hom⟦n⟧')) := by
      rw [← H.map_comp]
      congr 1
      ext <;> simp [eMn, shiftedIso, qI, Q]
    have hmap : H.map (Prod.mkHom eK.inv.op eM.hom) =
        H.map (Prod.mkHom eK.inv.op (𝟙 (Q.obj I))) ≫
          H.map (Prod.mkHom (𝟙 (op K)) eM.hom) := by
      rw [← H.map_comp]
      congr 1
      ext <;> simp
    have he := Functor.commShiftIso_hom_naturality
      (RingedHomUniverses.hom.{c, v, u, w} J R K) eM.hom n
    change H.map (Prod.mkHom (𝟙 (op K)) (eM.hom⟦n⟧')) ≫ _ =
      _ ≫ (H.map (Prod.mkHom (𝟙 (op K)) eM.hom))⟦n⟧' at he
    change Q.map u.hom ≫ δn ≫ H.map (Prod.mkHom eK.inv.op qI) ≫ _ =
      (Q.commShiftIso n).hom.app _ ≫
        (δ ≫ H.map (Prod.mkHom eK.inv.op (𝟙 (Q.obj I))))⟦n⟧' at hn
    have hqa := (Q.commShiftIso n).hom.naturality a
    change Q.map (a⟦n⟧') ≫ (Q.commShiftIso n).hom.app _ =
      (Q.commShiftIso n).hom.app A ≫ (Q.map a)⟦n⟧' at hqa
    change (Q.map (a⟦n⟧' ≫ u.hom) ≫ δn ≫
        H.map (Prod.mkHom eK.inv.op eMn.hom)) ≫ _ =
      (Q.commShiftIso n).hom.app A ≫
        (Q.map a ≫ δ ≫ H.map (Prod.mkHom eK.inv.op eM.hom))⟦n⟧'
    simp only [Q.map_comp, Category.assoc]
    rw [hmapn]
    simp only [Category.assoc]
    rw [he]
    rw [reassoc_of% hn, reassoc_of% hqa, hmap]
    simp only [Functor.map_comp, Category.assoc]

end CategoryTheory.RingedHomShift
