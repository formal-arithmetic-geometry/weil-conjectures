/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorSignedCancellation
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
import all WeilConjectures.AlgebraicGeometry.CoefficientTensorCurryNormalization
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

/-! # Integer shifts of the normalized native scalar tensor comparison

Source: Stacks 06YY, 07A4, 0A8X and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite WeilConjectures SheafOfModules

namespace CategoryTheory.RingedClosedNormalization
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, r} J R)]

set_option maxHeartbeats 800000 in
-- The two dependent uncurrying equations elaborate fixed representative tensor data.
private theorem representative_uncurry_eq
    (S U : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (TS : CoefficientTensorModels.{r, c, v, w} J R S)
    (TU : CoefficientTensorModels.{r, c, v, w} J R U)
    (P L M : CochainComplex (RingedDerivedNative.Modules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hL : L.IsKFlatIndependentCoefficients)
    (φ : P ⟶ homComplex (R := R) L ((coefficientHomResolution.{r, c, v} J R).obj M)) :
    (TS.iso J R S P L hP hL).hom ≫
        (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).symm
          (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{r, c, v, w} J R L M).inv) =
      (TU.iso J R U P L hP hL).hom ≫
        (U.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).symm
          (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{r, c, v, w} J R L M).inv) := by
  obtain ⟨f, hf, hn⟩ := TS.uncurry_model ⟨P, hP⟩ ⟨L, hL⟩ M φ
  obtain ⟨g, hg, hm⟩ := TU.uncurry_model ⟨P, hP⟩ ⟨L, hL⟩ M φ
  have he : f = g := by
    apply coefficient_total_ext.{r, c, v} J R
    intro p q V x y
    rw [hf p q (p + q) rfl (add_comm q p) V x y,
      hg p q (p + q) rfl (add_comm q p) V x y]
  exact hn.trans (by rw [he]; exact hm.symm)

set_option maxHeartbeats 800000 in
-- Cancellation compares model isomorphisms across the closed-adjunction presentations.
private theorem comparison_model
    (S U : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (TS : CoefficientTensorModels.{r, c, v, w} J R S)
    (TU : CoefficientTensorModels.{r, c, v, w} J R U)
    (P L : CochainComplex (RingedDerivedNative.Modules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hL : L.IsKFlatIndependentCoefficients) :
    (TS.iso J R S P L hP hL).hom ≫
        (CoefficientClosedStructure.comparison S U).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) =
      (TU.iso J R U P L hP hL).hom := by
  let Q : CochainComplex (RingedDerivedNative.Modules.{c, v, r} J R) ℤ ⥤
      DerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, r} J R) := DerivedCategory.Q
  let M := Q.objPreimage (U.tensor.obj (Q.obj P, Q.obj L))
  let e : Q.obj M ≅ U.tensor.obj (Q.obj P, Q.obj L) := Q.objObjPreimageIso _
  let ξ := U.transpose (Q.obj P) (Q.obj L) (Q.obj M) e.inv
  obtain ⟨φ, hφ⟩ := RingedDerivedNative.representativeHom_surjective.{c, v, r, w}
    J R P L M hL ξ
  have h := representative_uncurry_eq.{c, v, r, w} J R S U TS TU P L M hP hL φ
  rw [hφ] at h
  have hS : (S.transpose (Q.obj P) (Q.obj L) (Q.obj M)).symm ξ =
      (CoefficientClosedStructure.comparison S U).hom.app (Q.obj P, Q.obj L) ≫ e.inv := by
    apply (S.transpose _ _ _).injective
    rw [Equiv.apply_symm_apply, CoefficientClosedStructure.comparison_transpose]
  have hU : (U.transpose (Q.obj P) (Q.obj L) (Q.obj M)).symm ξ = e.inv :=
    (U.transpose _ _ _).symm_apply_apply _
  rw [hS, hU] at h
  exact (cancel_mono e.inv).mp (by simpa only [Category.assoc] using h)

private theorem iso_cast_app {X Y : Type*} [Category X] [Category Y]
    {E F G : X ⥤ Y} (e : E ≅ F) (f : E ≅ G) (h : F = G)
    (he : HEq e f) (Z : X) :
    e.hom.app Z ≫ (eqToIso h).hom.app Z = f.hom.app Z := by
  subst G
  cases eq_of_heq he
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

set_option maxHeartbeats 800000 in
-- The model comparison includes the dependent equality of native monoidal presentations.
private theorem native_comparison_model
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (P L : CochainComplex (RingedDerivedNative.Modules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hL : L.IsKFlatIndependentCoefficients) :
    (T.iso J R S P L hP hL).hom ≫
        (RingedSignedTensor.comparison.{c, v, r, w} J R S).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) =
      (RingedDerivedNative.tensorIso.{c, v, r, w} J R P L (Or.inl hP)).hom := by
  obtain ⟨TN, hTN⟩ :=
    (RingedDerivedNative.closedAdjunction.{c, v, r, w} J R).choose_spec.2
  have hc := comparison_model.{c, v, r, w} J R S
    (RingedSignedTensor.nativeClosed.{c, v, r, w} J R) T TN P L hP hL
  let hT : (RingedSignedTensor.nativeClosed.{c, v, r, w} J R).tensor =
      RingedSignedTensor.nativeTensor.{c, v, r, w} J R :=
    congrArg (fun m ↦ @tensor _ _ m)
      (RingedSignedTensor.nativeClosed_monoidal.{c, v, r, w} J R)
  let QK := coefficientKFlatInclusion.{r, c, v} J R ⋙ DerivedCategory.Q.{w}
  let B := QK.prod QK
  have hcast := iso_cast_app TN.comparison (RingedDerivedNative.comparison.{c, v, r, w} J R)
    (congrArg (fun U ↦ B ⋙ U) hT) hTN (⟨P, hP⟩, ⟨L, hL⟩)
  have hn := congrArg Iso.hom (RingedDerivedNative.comparison_app.{c, v, r, w}
    J R ⟨P, hP⟩ ⟨L, hL⟩)
  change (RingedDerivedNative.comparison.{c, v, r, w} J R).hom.app
      (⟨P, hP⟩, ⟨L, hL⟩) =
    (RingedDerivedNative.tensorIso.{c, v, r, w} J R P L (Or.inl hP)).hom at hn
  have hcast' := hcast.trans hn
  dsimp only [RingedSignedTensor.comparison, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc, hc]
  simpa only [eqToIso.hom, eqToHom_app, Functor.comp_obj, Functor.prod_obj,
    CoefficientTensorModels.iso, Iso.app_hom] using hcast'
end CategoryTheory.RingedClosedNormalization

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (A : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The scalar comparison transported to the native tensors by closed adjunctions.
Source: Stacks 07A4 and uniqueness of tensor-Hom adjoints.
(blueprint: lem-sfb-ringed-scalar-tensor-shift-Y2). -/
def ringedNativeScalarComparison (μ : ScalarHomTensorComparison A a) :
    RingedSignedTensor.nativeTensor.{c, v, r, w} J R ⋙ (A.scalar a).derived ≅
      (A.scalar a).derived.prod (A.scalar a).derived ⋙
        RingedSignedTensor.nativeTensor.{c, v, r, w} J S :=
  Functor.isoWhiskerRight (RingedSignedTensor.comparison.{c, v, r, w} J R (A.closed R)).symm
      (A.scalar a).derived ≪≫ μ.iso ≪≫
    Functor.isoWhiskerLeft ((A.scalar a).derived.prod (A.scalar a).derived)
      (RingedSignedTensor.comparison.{c, v, r, w} J S (A.closed S))

/-- Curried form of the same comparison, with the geometric argument first.
Source: Stacks 07A4; currying changes no components.
(blueprint: lem-sfb-ringed-scalar-tensor-shift-Y2). -/
def ringedNativeScalarCurriedComparison (μ : ScalarHomTensorComparison A a) :
    (Functor.postcompose₂.obj (A.scalar a).derived).obj
        (RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J R).flip ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory (scalarModules J S))).obj
          (A.scalar a).derived).obj (A.scalar a).derived).obj
        (RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).flip where
  app K :=
    { app P := (ringedNativeScalarComparison J A a μ).hom.app (P, K)
      naturality P Q f := by
        change (A.scalar a).derived.map
            (((RingedSignedTensor.nativeCurriedTensor J R).map f).app K) ≫ _ =
          _ ≫ ((RingedSignedTensor.nativeCurriedTensor J S).map
            ((A.scalar a).derived.map f)).app ((A.scalar a).derived.obj K)
        simpa only [RingedSignedTensor.nativeTensor, RingedSignedTensor.nativeCurriedTensor,
          Functor.comp_map, Functor.prod_map, Functor.prod_obj, tensor_map, tensorHom_def,
          Functor.map_id, curriedTensor_map_app, MonoidalCategory.whiskerLeft_id,
          Category.comp_id] using
          (ringedNativeScalarComparison J A a μ).hom.naturality (Prod.mkHom f (𝟙 K)) }
  naturality K L f := by
    ext P
    change (A.scalar a).derived.map
        (((RingedSignedTensor.nativeCurriedTensor J R).obj P).map f) ≫ _ =
      _ ≫ ((RingedSignedTensor.nativeCurriedTensor J S).obj
        ((A.scalar a).derived.obj P)).map ((A.scalar a).derived.map f)
    simpa only [RingedSignedTensor.nativeTensor, RingedSignedTensor.nativeCurriedTensor,
      Functor.comp_map, Functor.prod_map, Functor.prod_obj, tensor_map, tensorHom_def,
      Functor.map_id, curriedTensor_obj_map, MonoidalCategory.id_whiskerRight,
      Category.id_comp] using
      (ringedNativeScalarComparison J A a μ).hom.naturality (Prod.mkHom (𝟙 P) f)

/-- The representative-normalized scalar tensor comparison commutes with shifts
in each tensor argument for the counit-normalized scalar shift.
Source: Stacks 06YY and 07A4, with the signed tensor convention of 0FNH.
(blueprint: lem-sfb-ringed-scalar-tensor-shift-Y2).

Proof: first identify the two closed-adjunction comparisons on K-flat pairs.
For K-flat P,Q and a complex M, Hom(Q,I(M)) is K-injective. Hence every derived
map Q(P) -> RHom(Q(Q),Q(M)) is represented by a chain map P -> Hom(Q,I(M)).
The uncurrying models for both closed presentations send this map to the same
unsigned evaluation on local pure tensors. The sheaf tensor and coproduct
universal properties identify the chain maps. Injectivity of transposition and
Yoneda identify the tensor comparisons on these representatives. The private
comparison_model proves this identity for arbitrary coefficient and derived
universes. Fully faithful
restriction along the localization of K-flat pairs determines the natural
comparison everywhere. Thus b has the native version of mu's normalization square.

On complexes, the scalar unit sends x to 1 tensor x and the tensor comparison
sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). In the first slot,
the total tensor shift has no coefficient. In the second slot its coefficient
on first-factor degree p and shift n is (-1)^(pn), on both sides of the scalar
comparison. Scalar extension is additive and so preserves that coefficient.
Check the two chain comparison/shift equations on these local tensor generators,
then use the sheafification and total coproduct universal properties.

The assumed counit equation, composed with quotientCompQhIso, is exactly the
integer shift equation for scalarPairComplexComparison. Paste this equation,
the native localization tensor/shift equations, and the two chain equations into
the representative normalization square of mu. All comparison maps on K-flat
pairs are invertible, including their shifts and their scalar extensions, so
cancel them to obtain the two desired fixed-slot squares on Q(P),Q(Q).
Every derived object has a K-flat representative. Naturality of b and of each
shift isomorphism transports the squares along these representative isomorphisms.
This proves both CommShift assertions for every integer, including zero and
negative integers, without any flatness assumption on the coefficient map. -/
theorem ringedNativeScalarComparison_commShift (μ : ScalarHomTensorComparison A a)
    [ordinaryAdditive : (A.scalar a).extension.Additive]
    [scalarShift : (A.scalar a).derived.CommShift ℤ]
    [scalarAdditive : (A.scalar a).derived.Additive]
    (hcounit : ∀ (n : ℤ) (P : HomotopyCategory (scalarModules J R) (.up ℤ)),
      (A.scalar a).derived.map ((DerivedCategory.Qh.commShiftIso n).hom.app P) ≫
        ((A.scalar a).derived.commShiftIso n).hom.app (DerivedCategory.Qh.obj P) ≫
        ((A.scalar a).counit.app P)⟦n⟧' =
      (A.scalar a).counit.app (P⟦n⟧) ≫ DerivedCategory.Qh.map
        ((((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app P) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app
          (((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).obj P))
    : letI := RingedSignedTensor.nativeTensorShift.{c, v, r, w} J R
      letI := RingedSignedTensor.nativeTensorShift.{c, v, r, w} J S
      letI (K : DerivedCategory (scalarModules J R)) :
          (((Functor.postcompose₂.obj (A.scalar a).derived).obj
            (RingedSignedTensor.nativeCurriedTensor J R).flip).obj K).CommShift ℤ :=
        Functor.CommShift.comp
          ((RingedSignedTensor.nativeCurriedTensor J R).flip.obj K) (A.scalar a).derived
      letI (K : DerivedCategory (scalarModules J R)) :
          (((((Functor.whiskeringLeft₂ (DerivedCategory (scalarModules J S))).obj
            (A.scalar a).derived).obj (A.scalar a).derived).obj
              (RingedSignedTensor.nativeCurriedTensor J S).flip).obj K).CommShift ℤ :=
        Functor.CommShift.comp (A.scalar a).derived
          ((RingedSignedTensor.nativeCurriedTensor J S).flip.obj ((A.scalar a).derived.obj K))
      letI (P : DerivedCategory (scalarModules J R)) :
          (((Functor.postcompose₂.obj (A.scalar a).derived).obj
            (RingedSignedTensor.nativeCurriedTensor J R).flip).flip.obj P).CommShift ℤ :=
        Functor.CommShift.comp
          ((RingedSignedTensor.nativeCurriedTensor J R).obj P) (A.scalar a).derived
      letI (P : DerivedCategory (scalarModules J R)) :
          (((((Functor.whiskeringLeft₂ (DerivedCategory (scalarModules J S))).obj
            (A.scalar a).derived).obj (A.scalar a).derived).obj
              (RingedSignedTensor.nativeCurriedTensor J S).flip).flip.obj P).CommShift ℤ :=
        Functor.CommShift.comp (A.scalar a).derived
          ((RingedSignedTensor.nativeCurriedTensor J S).obj ((A.scalar a).derived.obj P))
      (∀ K, NatTrans.CommShift ((ringedNativeScalarCurriedComparison J A a μ).app K) ℤ) ∧
        (∀ P, NatTrans.CommShift ((ringedNativeScalarCurriedComparison J A a μ).flipApp P) ℤ) := by
  sorry

end CategoryTheory
