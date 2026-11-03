/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StratifiedScalarPerfectGeneration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StratifiedScalarPerfectGeneration
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison

/-! # Rational constructible generation by scalar-perfect pieces -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private def pointFreeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (r : ℕ) :
    (upperStarFromPointMod Λ X).obj (Mod.finiteFree Λ r) ≅
      Mod.finiteFree (condensedRingObj Λ X) r :=
  (upperStarFromPointMod Λ X).mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp))

private theorem lisse_single_perfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (M : supportModules Λ S)
    (hM : IsLisseCoefficientModule Λ M) :
    IsLocallyConstantPerfectComplex Λ S ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨er⟩⟩ := hU i
  let R := Mod.finiteFree Λ r
  let F := (CochainComplex.singleFunctor _ 0).obj R
  let G := upperStarFromPointMod Λ (U.X i)
  refine ⟨F, ⟨0, 0, fun n hn ↦ ?_⟩, ?_, inferInstance, ⟨?_⟩⟩
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 R n (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : F.X 0 ≅ R := HomologicalComplex.singleObjXSelf (.up ℤ) 0 R
      exact ⟨r, e.hom, e.inv, e.hom_inv_id⟩
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 R n hn
      exact ⟨0, 0, 0, hz.eq_of_src _ _⟩
  · exact ((upperStar Λ (U.f i)).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (er ≪≫ (pointFreeIso Λ (U.X i) r).symm) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).symm.app R ≪≫ G.mapDerivedCategoryFactors.app F

private theorem lisse_extension_mem
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (Q : ObjectProperty (DerivedCategory (supportModules Λ X)))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i]
      (P : DerivedCategory (supportModules Λ S)),
      IsLocallyConstantPerfectComplex Λ S P →
      Q (((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (lowerStar Λ i).rightDerivedFunctor).obj P))
    (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (M : supportModules Λ S) (hM : IsLisseCoefficientModule Λ M) :
    Q ((DerivedCategory.singleFunctor _ 0).obj
      ((coefficientHeartLocallyClosedExtension Λ a ha).obj M)) := by
  have : IsImmersion a := ha
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact a := noetherian_qc a
  have : IsOpenImmersion a.toImage := inferInstance
  have : IsNoetherian a.image := isNoetherian_of_locallyOfFiniteType a.imageι
  have : PreservesFiniteColimits (lowerStar Λ a.imageι) := closed_exact Λ a.imageι
  let F := openImmersionLowerShriek Λ a.toImage
  let G := lowerStar Λ a.imageι
  have hp := hQ S a.image a.toImage a.imageι
    ((DerivedCategory.singleFunctor _ 0).obj M) (lisse_single_perfect Λ S M hM)
  exact Q.prop_of_iso
    (G.rightDerivedFunctor.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      G.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj M)) hp

private def shiftedConeRelation
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (U V W : C) : Prop :=
  ∃ (n : ℤ) (f : U ⟶ V) (g : V ⟶ (shiftFunctor _ n).obj W)
    (t : (shiftFunctor _ n).obj W ⟶ (shiftFunctor _ (1 : ℤ)).obj U),
    Pretriangulated.Triangle.mk f g t ∈ distTriang _

private theorem witness_mem
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hG : ∀ W, G W → Q W) (K : C)
    (hw : constructionWitness G shiftedConeRelation K) : Q K := by
  apply constructionWitness_induction (G := G) (R := shiftedConeRelation)
    (P := Q) (K := K) (hK := hw) hG
  intro U V W h hU hV
  obtain ⟨q, f, g, t, hT⟩ := h
  exact (ObjectProperty.prop_shift_iff_of_isStableUnderShift Q W q).mp
    (Q.ext_of_isTriangulatedClosed₃ (Pretriangulated.Triangle.mk f g t) hT hU hV)

private def lisseGenerator
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty (DerivedCategory (supportModules Λ X)) := fun W ↦
  ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (M : supportModules Λ S) (n : ℤ), IsLisseCoefficientModule Λ M ∧
      Nonempty (W ≅ (shiftFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((coefficientHeartLocallyClosedExtension Λ a ha).obj M)))

private theorem rational_witness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ R = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (supportModules (coefficientHeartRingObj R) X))
    (hK : constantModelBoundedConstructible (coefficientHeartRingObj R) X K) :
    constructionWitness (lisseGenerator (coefficientHeartRingObj R) X) shiftedConeRelation K :=
  (coefficientHeart_generation ℓ R hR X K).mp hK

/-- For rational admissible coefficients, bounded constructible complexes are generated
using only finite cones and shifts of locally closed scalar-perfect extensions.
Source: blueprint internal-Hom stability proof, rational case of paragraph 1;
coefficient-heart generation proof
(blueprint: lem-sfb-rational-locally-closed-perfect-generation).

Proof: apply the explicit coefficient-heart generation sequence. A lisse module is
locally finite free. Put its rank-r free point module in degree zero; regular-module
pullback comparison identifies its realization with the given local trivialization.
The exact open and closed extension functors commute with the degree-zero embedding.
Thus each shifted lisse extension in the sequence belongs to Q by its generator
hypothesis. Strong induction on the sequence puts every cone in Q; shift stability
removes the displayed shift on its third vertex. The last term is K. Rank zero,
zero complexes and the empty scheme are handled by the same sequence. -/
theorem rational_locallyClosedPerfect_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ R = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (supportModules (coefficientHeartRingObj R) X))
    (hK : constantModelBoundedConstructible (coefficientHeartRingObj R) X K)
    (Q : ObjectProperty (DerivedCategory (supportModules (coefficientHeartRingObj R) X)))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i]
      (P : DerivedCategory (supportModules (coefficientHeartRingObj R) S)),
      IsLocallyConstantPerfectComplex (coefficientHeartRingObj R) S P →
      Q (((openImmersionLowerShriek (coefficientHeartRingObj R) j).mapDerivedCategory ⋙
        (lowerStar (coefficientHeartRingObj R) i).rightDerivedFunctor).obj P)) : Q K := by
  apply witness_mem (lisseGenerator (coefficientHeartRingObj R) X) Q _ K
    (rational_witness ℓ R hR X K hK)
  rintro W ⟨S, a, ha, M, q, hM, ⟨e⟩⟩
  exact Q.prop_of_iso e.symm
    (Q.le_shift q _ (lisse_extension_mem (coefficientHeartRingObj R) X Q hQ S a ha M hM))

end AlgebraicGeometry.ProEtale.CondensedRing
