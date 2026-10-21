/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.TorModelRestriction
import Sheaf.AlgebraicGeometry.TorModelTensorComparison
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatLowerTruncation
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Paper.EtaleFlatKFlatResolution
import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.EtaleTensorCokernelFlat
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-!
# Tor amplitude and K-flat resolutions

Source: Stacks Project, Tag 0F1M, lemma-bounded-below-tor-amplitude
(blueprint: lem-kun-0f1m).

The scalar restriction below identifies a module over the constant ring sheaf with a
module-valued sheaf, using the sheafification unit on constants. It lets the existing
ringed-site K-flat and flatness predicates use the same representative as the recorded
module-valued derived category. The representative in the theorem is fixed before the
universal quantification over pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uD vD
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open MonoidalCategory

private theorem restriction_homology_isZero_iff
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) (i : ℤ) :
    IsZero ((((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj K).homology i) ↔
      IsZero (K.homology i) := by
  let := torModelRestriction_isEquivalence T Λ
  let e := (K.sc i).mapHomologyIso (torModelRestriction Λ T)
  constructor
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (torModelRestriction Λ T).map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (h.of_iso e.symm).eq_of_src _ _
  · intro h
    exact ((torModelRestriction Λ T).map_isZero h).of_iso e

private theorem restriction_derived_homology_isZero_iff
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) (i : ℤ) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
      (_root_.DerivedCategory.Q.obj
        (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj K))) ↔
      IsZero (K.homology i) := by
  exact ((_root_.DerivedCategory.homologyFunctorFactors _ i).app _).isZero_iff.trans
    (restriction_homology_isZero_iff Λ T K i)

section TensorVanishing

variable (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})

local instance : (T.smallEtaleTopology.W.inverseImage
    (PresheafOfModules.toPresheaf.{u + 1} (torModelRing Λ T).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_independentCoefficients (torModelCoefficientRing Λ T)

local instance : MonoidalCategory (SheafOfModules.{u + 1} (torModelRing Λ T)) :=
  SheafOfModules.monoidalCategory (torModelCoefficientRing Λ T)

local instance : (curriedTensor
    (SheafOfModules.{u + 1} (torModelRing Λ T))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (torModelCoefficientRing Λ T)

local instance (M : SheafOfModules.{u + 1} (torModelRing Λ T)) :
    ((curriedTensor _).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (torModelCoefficientRing Λ T) M

local instance : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u + 1} (torModelRing Λ T)) := by
  change HasColimitsOfSize.{0, 0} (SheafOfModules.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)))
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1, u + 1, u + 2} _

local instance (K L : CochainComplex
    (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) :
    CochainComplex.HasMapBifunctor K L (curriedTensor _) := by
  intro n
  exact HasColimitsOfShape.has_colimit _

private theorem tor_vanishing_iff
    (K : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := torModelCoefficientRing Λ T) K)
    (E : DerivedCategoryModule Λ T)
    (e : _root_.DerivedCategory.Q.obj
      (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj K) ≅ E)
    (a : ℤ) :
    DerivedCategory.hasTorAmplitudeGE Λ T a E ↔
      ∀ (M : SheafOfModules.{u + 1} (torModelRing Λ T)) (i : ℤ), i < a →
        IsZero ((CochainComplex.mapBifunctor K
          ((CochainComplex.singleFunctor _ 0).obj M) (curriedTensor _)).homology i) := by
  let := torModelRestriction_isEquivalence T Λ
  constructor
  · intro h M i hi
    obtain ⟨c⟩ := torModel_tensor_single_comparison Λ T K hK M
    let t := ((derivedTensor (ModuleCat.{u + 1} Λ) T).mapIso e).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((torModelRestriction Λ T).obj M))
    have hz := (h ((torModelRestriction Λ T).obj M) i hi).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso (c ≪≫ t))
    exact (restriction_derived_homology_isZero_iff Λ T _ i).1 hz
  · intro h M i hi
    let M' := (torModelRestriction Λ T).objPreimage M
    let eM := (torModelRestriction Λ T).objObjPreimageIso M
    obtain ⟨c⟩ := torModel_tensor_single_comparison Λ T K hK M'
    let t := ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
      (_root_.DerivedCategory.Q.obj
        (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj K))).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eM)
    let t' := ((derivedTensor (ModuleCat.{u + 1} Λ) T).mapIso e).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
    have hz := (restriction_derived_homology_isZero_iff Λ T _ i).2 (h M' i hi)
    exact hz.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso (c ≪≫ t ≪≫ t')).symm

private theorem isGE_of_tensor_vanishing
    (K : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) (a : ℤ)
    (h : ∀ (M : SheafOfModules.{u + 1} (torModelRing Λ T)) (i : ℤ), i < a →
      IsZero ((CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor _ 0).obj M) (curriedTensor _)).homology i)) :
    K.IsGE a := by
  let C := SheafOfModules.{u + 1} (torModelRing Λ T)
  let e := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) (𝟙_ C) K ≪≫
    (NatIso.mapHomologicalComplex (rightUnitorNatIso C) (.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso C (.up ℤ)).app K
  apply (K.isGE_iff a).2
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (h (𝟙_ C) i hi).of_iso
    ((HomologicalComplex.homologyFunctor C (.up ℤ) i).mapIso e).symm

private theorem flatOnSite_of_iso
    {M N : SheafOfModules.{u + 1} (torModelRing Λ T)} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) N := by
  have hM' : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (torModelCoefficientRing Λ T) M) hM
  have hN' : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (torModelCoefficientRing Λ T) N).symm hN'

private theorem flatOnSite_of_isZero
    {M : SheafOfModules.{u + 1} (torModelRing Λ T)} (hM : IsZero M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) M := by
  let := SheafOfModules.tensorPreadditive (torModelCoefficientRing Λ T)
  have h := (ObjectProperty.flat_of_isZero hM).2
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (torModelCoefficientRing Λ T) M).symm h


/-- Tor amplitude in `[a, infinity)` is equivalent to a K-flat, flat-term representative
vanishing below `a`. This one representative remains K-flat and flat-term after every
module pullback along a morphism of ringed topoi.
Source: Stacks Tag 0F1M, lemma-bounded-below-tor-amplitude, and Tag 0G7E
(blueprint: lem-kun-0f1m).

Proof:
1. A K-flat representative computes derived tensor with every sheaf in degree zero
(def-kun-derived-tensor). Its terms below a vanish, so the cohomology of each tensor
vanishes below a, the condition of def-kun-tor-amplitude.
2. Conversely take a K-flat flat-term resolution K of a representative of E using
lem-kun-flat-resolution-existence, in the larger universe of def-weil-size-convention.
The amplitude assumption says H^n(K tensor M)=0 for n<a and every module sheaf M.
Testing with the unit gives H^n(K)=0 below a.
3. By lem-kun-tor-cokernel-flat, N=coker(K^(a-1) -> K^a) is flat.
4. The good lower truncation P has N at a, K^i above a, and zero below a
(Mathlib good truncation). Its quotient map q:K -> P is a quasi-isomorphism: at a its
cohomology is ker(d^a)/im(d^(a-1)), at a+1 the incoming image is unchanged, and above
that the complexes coincide. Below a both cohomologies vanish. Thus P represents E.
5. The kernel L of q has K^i below a, im(d^(a-1)) at a, and zero above a. The
flat-quotient tensor exactness argument makes the image flat, since K^a and N are
flat. Thus L is bounded above with flat terms, and the independent-coefficient
bounded-above flat criterion makes it K-flat.
6. The lower-truncation theorem formalizes this kernel argument. Tensor the
short exact sequence 0 -> L -> K -> P -> 0 with any acyclic complex A. Flatness of
P makes it exact in each bidegree; exact coproducts of sheaves make the total
sequence short exact. Its first two terms are acyclic by K-flatness, and the long
exact homology sequence makes the third acyclic. Hence P is K-flat.
7. Apply lem-weil-pbc-ringed-topos-kflat-pullback to this fixed P, simultaneously
for every ringed-topos morphism. No exactness of module pullback or flatness of
the coefficient homomorphism is assumed. -/
theorem DerivedCategory.hasTorAmplitudeGE_iff_exists_kFlat_flat_model
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) (E : DerivedCategoryModule Λ T)
    (a : ℤ) :
    DerivedCategory.hasTorAmplitudeGE Λ T a E ↔
      ∃ P : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := torModelCoefficientRing Λ T) P ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) (P.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (P.X i)) ∧
        Nonempty (_root_.DerivedCategory.Q.obj
          (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj P) ≅ E) ∧
        (∀ {D : Type uD} [Category.{vD} D] [EssentiallySmall.{u + 1} D]
          (J : GrothendieckTopology D) (RI S : Sheaf J CommRingCat.{u + 1})
          (uInv : Sheaf T.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
          (uPush : Sheaf J (Type (u + 1)) ⥤ Sheaf T.smallEtaleTopology (Type (u + 1)))
          (_adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
          (I : SheafOfModules.AlgebraicInverseImage uInv (torModelCoefficientRing Λ T) RI)
          (c : RI ⟶ S)
          (uStar : SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
            SheafOfModules.{u + 1}
              ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
          (hobj : ∀ M : SheafOfModules.{u + 1} (torModelRing Λ T),
            uStar.obj M = SheafOfModules.changeOfRings c (I.modules.obj M))
          (_hmap : ∀ {M N : SheafOfModules.{u + 1} (torModelRing Λ T)} (f : M ⟶ N),
            uStar.map f = eqToHom (hobj M) ≫
              SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
              eqToHom (hobj N).symm) [uStar.Additive],
          CochainComplex.IsKFlatIndependentCoefficients (R := S)
            ((uStar.mapHomologicalComplex (.up ℤ)).obj P) ∧
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{uD, vD, u + 1, u + 1} (J := J) (R := S)
            (((uStar.mapHomologicalComplex (.up ℤ)).obj P).X i)) := by
  let : (torModelRestriction Λ T).Additive := torModelRestriction_additive Λ T
  let := torModelRestriction_isEquivalence T Λ
  let := SheafOfModules.isMonoidal_W_independentCoefficients (torModelCoefficientRing Λ T)
  let := SheafOfModules.monoidalCategory (torModelCoefficientRing Λ T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (torModelCoefficientRing Λ T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (torModelCoefficientRing Λ T)
  let eF := (torModelRestriction Λ T).asEquivalence.mapHomologicalComplex (.up ℤ)
  let F := eF.functor
  let : F.IsEquivalence := eF.isEquivalence_functor
  constructor
  · intro hE
    let G := F.objPreimage (_root_.DerivedCategory.Q.objPreimage E)
    obtain ⟨K, f, hK, hflat, hf⟩ := Scheme.exists_etale_flat_isKFlat_resolution T Λ G
    have : QuasiIso f := hf
    have : QuasiIso (F.map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology f (torModelRestriction Λ T)
    let eK := asIso (_root_.DerivedCategory.Q.map (F.map f)) ≪≫
      _root_.DerivedCategory.Q.mapIso (F.objObjPreimageIso _) ≪≫
      _root_.DerivedCategory.Q.objObjPreimageIso E
    have hv := (tor_vanishing_iff Λ T K hK E eK a).1 hE
    have hop := isFlat_opcycles_of_tensor_cohomology_vanishing Λ T K hflat a hv
    let := isGE_of_tensor_vanishing Λ T K a hv
    let P := K.truncGE a
    have hPflat (i : ℤ) :
        SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) (P.X i) := by
      obtain hi | hi | hi := lt_trichotomy i a
      · exact flatOnSite_of_isZero Λ T (P.isZero_of_isStrictlyGE a i hi)
      · subst i
        exact flatOnSite_of_iso Λ T (K.truncGEXIsoOpcycles a).symm hop
      · exact flatOnSite_of_iso Λ T (K.truncGEXIso a i hi).symm (hflat i)
    have hP := CochainComplex.isKFlatIndependentCoefficients_truncGE
      (torModelCoefficientRing Λ T) K a hK hflat hop
    refine ⟨P, hP, hPflat, ?_, ?_, ?_⟩
    · intro i hi
      exact P.isZero_of_isStrictlyGE a i hi
    · have : QuasiIso (F.map (K.πTruncGE a)) :=
        HomologicalComplex.quasiIso_map_of_preservesHomology
          (K.πTruncGE a) (torModelRestriction Λ T)
      exact ⟨(asIso (_root_.DerivedCategory.Q.map (F.map (K.πTruncGE a)))).symm ≪≫ eK⟩
    · intro D _ _ J RI S uInv uPush adj _ I c uStar hobj hmap _
      exact SheafOfModules.isKFlat_ringedToposPullback uInv uPush adj I c
        uStar hobj hmap P hP hPflat
  · rintro ⟨P, hP, _, hzero, ⟨e⟩, _⟩
    apply (tor_vanishing_iff Λ T P hP E e a).2
    intro M i hi
    let B := CochainComplex.mapBifunctor P
      ((CochainComplex.singleFunctor _ 0).obj M) (curriedTensor _)
    have hz : IsZero (B.X i) := by
      let e' := (HomologicalComplex.eval _ (.up ℤ) i).mapIso
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P)
      exact ((tensorRight M).map_isZero (hzero i hi)).of_iso e'
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomologicalComplex.ExactAt.of_isZero hz

end TensorVanishing
end AlgebraicGeometry.Etale
