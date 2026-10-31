/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.IntrinsicResolutionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-! # Restriction of an intrinsic K-flat tensor test

Source: blueprint `thm-pur-general-admissibility.proof.md`, Step 4;
Stacks Project, Tag 07A4, pullback of tensor products.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private noncomputable def realizationPullback (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    ProEtale.finiteCoefficientIntrinsicRealization X A ⋙
        proEtaleConstantRingPullback A j ≅
      ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        ProEtale.finiteCoefficientIntrinsicRealization U A :=
  Functor.isoWhiskerLeft _ (openSquarePullbackModel A j) ≪≫
    (sfIntrinsicModuleEquivalence X A).funInvIdAssoc
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        ProEtale.finiteCoefficientIntrinsicRealization U A)

private noncomputable def realizationDerivedPullback (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    (ProEtale.finiteCoefficientIntrinsicRealization X A).mapDerivedCategory ⋙
        proEtaleConstantRingDerivedPullback A j ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (ProEtale.finiteCoefficientIntrinsicRealization U A).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (realizationPullback A j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

private theorem torOfIso {X : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

/-- A Tor bound after open restriction annihilates the restriction of each global
K-flat tensor-test cohomology sheaf. The test module is arbitrary, with no etale-origin
or constructibility condition. This is a comparison of tensor presentations, before
using any covering family.
Source: blueprint `thm-pur-general-admissibility.proof.md`, Step 4;
Stacks Project, Tag 07A4 (blueprint: lem-pur-open-tensor-test-vanishing).

Proof: the inverse image of the constant ring is canonically the constant ring on U.
The corresponding module inverse image is exact. Pull back the K-flat resolution and
the module in degree zero; flat exact inverse image preserves K-flatness and quasi-
isomorphisms. The canonical tensor comparison identifies this pulled-back tensor with
the tensor of the pulled-back factors. Apply the local Tor bound to this resolution
and the inverse image of the arbitrary module M. Exactness identifies its cohomology
with inverse image of the global cohomology. Transfer vanishing through these two
identifications. Equivalently compute both tensors using the resolving-class tensor
and its K-flat presentation. No covering or exceptional inverse image enters. -/
theorem purityOpenTensorTestVanishing
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (hK : HasProEtaleTorAmplitude U A
      ((proEtaleConstantRingDerivedPullback A j).obj K) a b)
    (L Q : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj L ≅ K))
    (f : Q ⟶ L) (hf : QuasiIso f)
    (hQ : CochainComplex.IsAcyclicTensorKFlat (R := proEtaleConstantRing X A) Q)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((proEtaleConstantRingPullback A j).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        (derivedTensor X A L
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) Q f hf hQ))) := by
  classical
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let EX := sfIntrinsicModuleEquivalence X A
  let EU := sfIntrinsicModuleEquivalence U A
  let K' := EX.mapDerivedCategory.inverse.obj K
  let eK : (ProEtale.finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
      K' ≅ K := EX.mapDerivedCategory.counitIso.app K
  let N := EX.inverse.obj M
  let eM : (ProEtale.finiteCoefficientIntrinsicRealization X A).obj N ≅ M :=
    EX.counitIso.app M
  let F := ProEtale.upperStar B j
  let eU : (ProEtale.finiteCoefficientIntrinsicRealization U A).mapDerivedCategory.obj
      (F.mapDerivedCategory.obj K') ≅
      (proEtaleConstantRingDerivedPullback A j).obj K :=
    ((realizationDerivedPullback A j).app K').symm ≪≫
      (proEtaleConstantRingDerivedPullback A j).mapIso eK
  have hu := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A U a b hK.1 (F.mapDerivedCategory.obj K')).mp (torOfIso eU.symm hK)
  have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((ProEtale.derivedTensor B U).obj (F.mapDerivedCategory.obj K')).obj
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj N)))) := by
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).mp (hu (F.obj N)).1 q hq
    · exact (DerivedCategory.isLE_iff _ b).mp (hu (F.obj N)).2 q hq
  let S := (DerivedCategory.singleFunctor _ 0).obj N
  let T := ((ProEtale.derivedTensor B X).obj K').obj S
  let eT : F.mapDerivedCategory.obj T ≅
      ((ProEtale.derivedTensor B U).obj (F.mapDerivedCategory.obj K')).obj
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj N)) :=
    asIso ((F.mapDerivedCategoryTensorComparison.app K').app S) ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (Iso.refl _)
        ((F.mapDerivedCategorySingleFunctor 0).app N)
  obtain ⟨eL⟩ := e
  obtain ⟨eh⟩ := ProEtale.intrinsic_resolution_tensor_homology_iso A X K' L Q
    (eL ≪≫ eK.symm) f hf hQ N M eM q
  let eg := (proEtaleConstantRingPullback A j).mapIso eh ≪≫
    (realizationPullback A j).app _ ≪≫
    (ProEtale.finiteCoefficientIntrinsicRealization U A).mapIso
      (((F.mapDerivedCategoryHomologyFunctorIso q).app T) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso eT)
  exact ((ProEtale.finiteCoefficientIntrinsicRealization U A).map_isZero hz).of_iso eg

end WeilConjectures
