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

/-- The recorded positive-level coefficient ring, lifted to the common site universe.
Source: blueprint finite-coefficient transport paragraph; Stacks Tag 09AL
(blueprint: lem-sf-proetale-pf-admissible-models). -/
abbrev pfModelCoefficients (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) : Type (u + 1) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E n)

/-- The recorded positive-level coefficient ring is finite.
Source: Stacks Tag 09AL (blueprint: lem-sf-proetale-pf-admissible-models). -/
instance pfModelCoefficients_finite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (pfModelCoefficients l E n) :=
  haveI := Padic.finite_coefficientExtensionRing l E n n.pos
  inferInstance

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

/-- Origin existence with the original Tor intervals, and the same model assertions
for every supplied pair of bounded constructible origins and specified isomorphisms.
Source: Stacks Tags 09AL and 08G1; blueprint finite-coefficient transport paragraph
(blueprint: lem-sf-proetale-pf-admissible-models). -/
def pfAdmissibleOriginAssertions (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} A))) (c0 d0 a b : ℤ) : Prop :=
  (∃ (eK : Scheme.FixedEtaleOriginWitness X A K) (eL : Scheme.FixedEtaleOriginWitness Y A L),
    Etale.DerivedCategory.isBoundedConstructible A X eK.complex.obj ∧
    Etale.DerivedCategory.isBoundedConstructible A Y eL.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A X c0 d0 eK.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A Y a b eL.complex.obj) ∧
  ∀ (eK : Scheme.FixedEtaleOriginWitness X A K) (eL : Scheme.FixedEtaleOriginWitness Y A L),
    Etale.DerivedCategory.isBoundedConstructible A X eK.complex.obj →
    Etale.DerivedCategory.isBoundedConstructible A Y eL.complex.obj →
    Etale.DerivedCategory.hasTorAmplitudeIn A X c0 d0 eK.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A Y a b eL.complex.obj ∧
    pfAdmissibleModelAssertions A j r eK.complex.obj eL.complex.obj a b

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
  have : CochainComplex.IsStrictlyLE JC v0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact J.map_isZero (C.isZero_of_isStrictlyLE v0 i hi)
  have : CochainComplex.IsStrictlyLE RP b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact R.map_isZero (P.isZero_of_isStrictlyLE b i hi)
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
    refine ⟨S, fun i ↦ ?_⟩
    obtain ⟨ι, W, g, hg, hM⟩ := Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)
    refine ⟨ι, W, g, hg, fun k ↦ ?_⟩
    obtain ⟨M, _, hMe⟩ := hM k
    exact ⟨M, Module.Finite.of_finite, hMe⟩
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

/-- Bounded constructible pro-etale inputs of the prescribed Tor intervals have
etale origins with the same intervals, and every specified pair has admissible models.
Source: Stacks Tags 09AL, 08G1, 06YQ, 03DJ and 06YU; blueprint finite-coefficient
transport paragraph (blueprint: lem-sf-proetale-pf-admissible-models).

Proof plan:
1. On each intrinsic constructible stratum use finite lisse models, then the
fixed-module constructible-origin and bounded-constructible-origin comparison theorems.
Convert the etale constructibility predicate using the recorded comparison lemma.
The lower bounds package the origins as the specified D+ witnesses.
2. For every supplied witness, transport the pro-etale Tor test through its iso;
comparison reflects exactly the same interval on the etale antecedent.
3. The bounded-representative theorem applied to the cohomological support [u0,v0]
gives C with strict support there, including the zero and singleton cases.
4. The generic Tor-amplitude flat-model theorem gives P with flat terms and strict
support [a,b]. A bounded-above flat complex is K-flat.
5. Literal termwise inverse image preserves flat terms and zero terms; it is again
bounded-above flat and K-flat. Exact-functor localization identifies its Q image with RL0.
6. Exact open extension preserves the support of C. Its localization factorization
identifies Q(JC) with M0, so M0 is bounded below.
7. The right-factor K-flat tensor comparison identifies Q(Tot(JC tensor RP)) with Q0.
A nonzero summand in degree m has u0 <= i <= v0, a <= h <= b and i+h=m,
so the signed total tensor vanishes outside [u0+a,v0+b]. Thus Q0 is bounded below.
8. Properness of r gives quasi-compactness; its separated diagonal is quasi-compact,
giving quasi-separatedness. These are the required bounded-below comparison inputs.
-/
theorem proEtale_pf_admissible_models (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r] (_hjr : j ≫ r = f)
    (K : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (pfModelCoefficients l E n))))
    (L : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (pfModelCoefficients l E n))))
    (_hKb : _root_.DerivedCategory.TStructure.t.bounded K.obj)
    (_hLb : _root_.DerivedCategory.TStructure.t.bounded L.obj)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X
      (pfModelCoefficients l E n) ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf Y
      (pfModelCoefficients l E n) ((_root_.DerivedCategory.homologyFunctor _ i).obj L.obj))
    (c0 d0 a b : ℤ) (_hcd : c0 ≤ d0) (_hab : a ≤ b)
    (_hKTor : Scheme.HasFixedCoefficientProEtaleTorAmplitude X
      (pfModelCoefficients l E n) K.obj c0 d0)
    (_hLTor : Scheme.HasFixedCoefficientProEtaleTorAmplitude Y
      (pfModelCoefficients l E n) L.obj a b) :
    pfAdmissibleOriginAssertions (pfModelCoefficients l E n) j r K L c0 d0 a b := by
  obtain ⟨eK, heK⟩ := bounded_origin (pfModelCoefficients l E n) X K _hKb _hKc
  obtain ⟨eL, heL⟩ := bounded_origin (pfModelCoefficients l E n) Y L _hLb _hLc
  have hKT := origin_tor (pfModelCoefficients l E n) X K c0 d0 _hKTor
  have hLT := origin_tor (pfModelCoefficients l E n) Y L a b _hLTor
  refine ⟨⟨eK, eL, heK, heL, hKT eK, hLT eL⟩, ?_⟩
  intro eK eL _ _
  exact ⟨hKT eK, hLT eL,
    admissible_models_of_tor (pfModelCoefficients l E n) j r _ _ a b (hLT eL)⟩

end AlgebraicGeometry.ProEtale
