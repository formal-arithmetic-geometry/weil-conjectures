/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-! # Admissible models for the finite-coefficient projection comparison

Source: Stacks Project, Tags 09AL, 08G1, 06YQ, 03DJ and 06YU; the finite-coefficient
transport paragraph of the current blueprint `thm-sf-pf-proetale.proof.md`
(blueprint: lem-sf-proetale-pf-admissible-models).

All objects use ordinary fixed-ring module sheaves on the original small sites.
The model assertions retain the literal termwise functors and the signed total tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- For fixed etale antecedents, every cohomological support interval admits the
simultaneous bounded models needed for the proper comparison. The `letI` declarations
in this definition only install the existing sheaf tensor, with its original data.
Source: Stacks Tags 08G1, 06YQ, 03DJ and 06YU; blueprint finite-coefficient transport
paragraph (blueprint: lem-sf-proetale-pf-admissible-models). -/
def pfAdmissibleModelAssertions (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K0 : Etale.DerivedCategoryModule A X) (L0 : Etale.DerivedCategoryModule A Y)
    (a b : ℤ) : Prop :=
  letI := Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.monoidalCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.symmetricCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  letI := Sheaf.symmetricCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  let M0 := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K0
  let RL0 := (Etale.upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory.obj L0
  let Q0 := ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M0).obj RL0
  ∀ u0 v0 : ℤ, u0 ≤ v0 →
    (∀ i : ℤ, (i < u0 ∨ v0 < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K0)) →
    ∃ (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      Nonempty ((_root_.DerivedCategory.Q.obj C) ≅ K0) ∧
      (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (C.X i)) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj P) ≅ L0) ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
      (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      let RP := ((Etale.upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex
        (.up ℤ)).obj P
      let JC := ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj C
      let T := CochainComplex.mapBifunctor JC RP (curriedTensor _)
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat RP ∧
      Nonempty ((_root_.DerivedCategory.Q.obj RP) ≅ RL0) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj JC) ≅ M0) ∧
      (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (JC.X i)) ∧
      Nonempty ((_root_.DerivedCategory.Q.obj T) ≅ Q0) ∧
      (∀ m : ℤ, (m < u0 + a ∨ v0 + b < m) → IsZero (T.X m)) ∧
      _root_.DerivedCategory.TStructure.t.plus M0 ∧
      _root_.DerivedCategory.TStructure.t.plus Q0 ∧
      QuasiCompact r ∧ QuasiSeparated r

/-- Assemble the literal bounded models using flat resolutions and exact localization. -/
private theorem admissible_models_of_tor (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (r : Z ⟶ Y) [IsProper r]
    (K0 : Etale.DerivedCategoryModule A X) (L0 : Etale.DerivedCategoryModule A Y)
    (a b : ℤ) (hL : Etale.DerivedCategory.hasTorAmplitudeIn A Y a b L0) :
    pfAdmissibleModelAssertions A j r K0 L0 a b := by
  let := Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let := Sheaf.monoidalCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  let := Sheaf.symmetricCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let := Sheaf.symmetricCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  intro u0 v0 _huv hK
  have : K0.IsGE u0 := (_root_.DerivedCategory.isGE_iff _ _).2
    (fun i hi ↦ hK i (.inl hi))
  have : K0.IsLE v0 := (_root_.DerivedCategory.isLE_iff _ _).2
    (fun i hi ↦ hK i (.inr hi))
  obtain ⟨C, _, _, ⟨eC⟩⟩ := K0.exists_iso_Q_obj_of_isGE_of_isLE u0 v0
  obtain ⟨P, _, _, hPf, ⟨eP⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hL)
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P a b hPf
  let R := Etale.upperStar (ModuleCat.{u + 1} A) r
  let J := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let RP := (R.mapHomologicalComplex (.up ℤ)).obj P
  let JC := (J.mapHomologicalComplex (.up ℤ)).obj C
  have hRPf (i : ℤ) : ObjectProperty.flat (RP.X i) :=
    Functor.PreservesFlat.flat_obj (F := R) (hPf i)
  have hRPk := CochainComplex.kFlat_of_bounded_of_flat RP a b hRPf
  let eRP : _root_.DerivedCategory.Q.obj RP ≅ R.mapDerivedCategory.obj L0 :=
    (R.mapDerivedCategoryFactors.app P).symm ≪≫ R.mapDerivedCategory.mapIso eP
  let eJC : _root_.DerivedCategory.Q.obj JC ≅ J.mapDerivedCategory.obj K0 :=
    (J.mapDerivedCategoryFactors.app C).symm ≪≫ J.mapDerivedCategory.mapIso eC.symm
  let T := CochainComplex.mapBifunctor JC RP (curriedTensor _)
  have hTge : T.IsStrictlyGE (u0 + a) :=
    CochainComplex.isStrictlyGE_tensorObj JC RP u0 a
  have hTle : T.IsStrictlyLE (v0 + b) :=
    CochainComplex.isStrictlyLE_tensorObj JC RP v0 b
  let eT : _root_.DerivedCategory.Q.obj T ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj
        (J.mapDerivedCategory.obj K0)).obj (R.mapDerivedCategory.obj L0) :=
    (_root_.DerivedCategory.QObjTensorQObjIsoOfKFlatRight JC RP hRPk).symm ≪≫
      tensorIso eJC eRP
  refine ⟨C, P, ⟨eC.symm⟩, ?_, ⟨eP⟩, ?_, ?_, hPk, hRPk,
    ⟨eRP⟩, ⟨eJC⟩, ?_, ⟨eT⟩, ?_, ?_, ?_, inferInstance, inferInstance⟩
  · intro i hi
    rcases hi with hi | hi
    · exact C.isZero_of_isStrictlyGE u0 i hi
    · exact C.isZero_of_isStrictlyLE v0 i hi
  · intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · exact fun i ↦ (hPf i).2
  · intro i hi
    rcases hi with hi | hi
    · exact CochainComplex.isZero_of_isStrictlyGE JC u0 i hi
    · exact CochainComplex.isZero_of_isStrictlyLE JC v0 i hi
  · intro i hi
    rcases hi with hi | hi
    · exact T.isZero_of_isStrictlyGE (u0 + a) i hi
    · exact T.isZero_of_isStrictlyLE (v0 + b) i hi
  · exact ⟨u0, _root_.DerivedCategory.TStructure.t.isGE_of_iso eJC u0⟩
  · exact ⟨u0 + a, _root_.DerivedCategory.TStructure.t.isGE_of_iso eT (u0 + a)⟩

/-- Keep the specified comparison isomorphism when reflecting a Tor interval. -/
private theorem origin_tor (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A))) (a b : ℤ)
    (hK : Scheme.HasFixedCoefficientProEtaleTorAmplitude X A K.obj a b)
    (e : Scheme.FixedEtaleOriginWitness X A K) :
    Etale.DerivedCategory.hasTorAmplitudeIn A X a b e.complex.obj := by
  apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
  apply (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b e.complex.obj).1
  exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.iso.symm hK.2

/-- Descend the cohomology sheaves and then the bounded complex, retaining its iso. -/
private theorem bounded_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A)))
    (hb : _root_.DerivedCategory.TStructure.t.bounded K.obj)
    (hc : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj)) :
    ∃ e : Scheme.FixedEtaleOriginWitness X A K,
      Etale.DerivedCategory.isBoundedConstructible A X e.complex.obj := by
  have hH (q : ℤ) : IsConstructible A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj) := by
    obtain ⟨S, _, _, hS⟩ := hc q
    exact ⟨S, fun i ↦ Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)⟩
  obtain ⟨Ke, hKe, ⟨α⟩⟩ := DerivedCategory.boundedConstructible_of_homology A hb
    (fun i ↦ exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hH i))
  refine ⟨⟨⟨Ke, hKe.1.1⟩, α⟩, fun i ↦
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hKe.2 i), ?_⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hKe.1
  refine ⟨min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff Ke a).1 ha i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff Ke b).1 hb i hi

end AlgebraicGeometry.ProEtale
