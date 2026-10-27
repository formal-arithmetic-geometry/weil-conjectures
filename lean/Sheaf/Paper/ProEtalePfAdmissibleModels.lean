/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse

/-! # Etale origins and admissible compactification models

Source: Stacks Project Tags 08G1, 09AL, 06YQ, 0G7E, 06YY and 06YU;
blueprint main-20261015, thm-sf-pf-proetale, finite-coefficient transport paragraph
(blueprint: lem-sf-proetale-pf-admissible-models).

## Main definitions and statement

* `pfModelCoefficients`: the positive-level coefficient quotient, lifted in universe.
* `pfAdmissibleModelAssertions`: the canonical complex models and their bounds.
* `pfAdmissibleOriginAssertions`: existence and the assertions for all supplied witnesses.
* `proEtale_pf_admissible_models`: the combined compactification input theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The actual positive-level coefficient quotient in the common sheaf universe.
Source: blueprint finite coefficient convention
(blueprint: lem-sf-proetale-pf-admissible-models). -/
abbrev pfModelCoefficients (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Type (u + 1) := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)

/-- Finiteness of the actual coefficient quotient, inherited from its recorded theorem.
Source: blueprint finite coefficient convention
(blueprint: lem-sf-proetale-pf-admissible-models). -/
instance pfModelCoefficients_finite (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (pfModelCoefficients l E n) :=
  let := Padic.finite_coefficientExtensionRing l E n n.property
  Finite.of_equiv (Padic.coefficientExtensionRing l E n) Equiv.ulift.symm

/-- All model clauses, using the canonical termwise functors and signed total tensor.
The local tensor structure is the published sheaf tensor. The totalization has terms
sum over i+h=m and differential d_C tensor 1 + (-1)^i 1 tensor d_P.
Source: Stacks Tags 08G1, 06YQ, 0G7E, 06YY, 03DJ and 06YU
(blueprint: lem-sf-proetale-pf-admissible-models). -/
def pfAdmissibleModelAssertions (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K0 : Etale.DerivedCategoryModule A X) (L0 : Etale.DerivedCategoryModule A Y)
    (u0 v0 a b : ℤ) : Prop :=
  let := Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let := Sheaf.monoidalCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  ∃ (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
    let RP : CochainComplex
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
      ((Etale.upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj P
    let JC : CochainComplex
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ := ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj C
    let T : CochainComplex
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
      CochainComplex.mapBifunctor JC RP (curriedTensor _)
    let M0 : Etale.DerivedCategoryModule A Z :=
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K0
    let RL0 : Etale.DerivedCategoryModule A Z :=
      (Etale.upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory.obj L0
    let Q0 : Etale.DerivedCategoryModule A Z :=
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj M0).obj RL0
    Nonempty (_root_.DerivedCategory.Q.obj C ≅ K0) ∧
    (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (C.X i)) ∧
    Nonempty (_root_.DerivedCategory.Q.obj P ≅ L0) ∧
    (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) ∧
    (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat RP ∧
    Nonempty (_root_.DerivedCategory.Q.obj RP ≅ RL0) ∧
    Nonempty (_root_.DerivedCategory.Q.obj JC ≅ M0) ∧
    (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero (JC.X i)) ∧
    Nonempty (_root_.DerivedCategory.Q.obj T ≅ Q0) ∧
    (∀ i : ℤ, (i < u0 + a ∨ v0 + b < i) → IsZero (T.X i)) ∧
    _root_.DerivedCategory.TStructure.t.plus M0 ∧
    _root_.DerivedCategory.TStructure.t.plus Q0 ∧
    QuasiCompact r ∧ QuasiSeparated r

/-- Existence and all-witness assertions. Origin pairs retain their specified comparison
isomorphisms. The universal clause accepts arbitrary preassigned representatives and
witnesses, and recovers the same Tor intervals before choosing the models.
Source: Stacks Tags 09AL and 08G1
(blueprint: lem-sf-proetale-pf-admissible-models). -/
def pfAdmissibleOriginAssertions (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (c0 d0 a b : ℤ) : Prop :=
  (∃ (WK : Scheme.FixedEtaleOriginWitness X A K)
      (WL : Scheme.FixedEtaleOriginWitness Y A L),
    Etale.DerivedCategory.isBoundedConstructible A X WK.complex.obj ∧
    Etale.DerivedCategory.isBoundedConstructible A Y WL.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A X c0 d0 WK.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A Y a b WL.complex.obj) ∧
  ∀ (WK : Scheme.FixedEtaleOriginWitness X A K)
    (WL : Scheme.FixedEtaleOriginWitness Y A L),
    Etale.DerivedCategory.isBoundedConstructible A X WK.complex.obj →
    Etale.DerivedCategory.isBoundedConstructible A Y WL.complex.obj →
    Etale.DerivedCategory.hasTorAmplitudeIn A X c0 d0 WK.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A Y a b WL.complex.obj ∧
    ∀ u0 v0 : ℤ, u0 ≤ v0 →
      (∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero
        ((_root_.DerivedCategory.homologyFunctor _ i).obj WK.complex.obj)) →
      pfAdmissibleModelAssertions A j r WK.complex.obj WL.complex.obj u0 v0 a b


private theorem coefficientSheafWIsMonoidal (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : (X.smallEtaleTopology.W (A := ModuleCat.{u + 1} A)).IsMonoidal := by
  exact GrothendieckTopology.W.monoidal

attribute [local instance 2000] coefficientSheafWIsMonoidal

private theorem proEtaleCoefficientSheafWIsMonoidal (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : ((Scheme.ProEt.topology X).W (A := ModuleCat.{u + 1} A)).IsMonoidal := by
  exact GrothendieckTopology.W.monoidal

attribute [local instance 2000] proEtaleCoefficientSheafWIsMonoidal

private theorem boundedOrigin (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hb : _root_.DerivedCategory.TStructure.t.bounded K.obj)
    (hc : ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj)) :
    ∃ W : Scheme.FixedEtaleOriginWitness X A K,
      Etale.DerivedCategory.isBoundedConstructible A X W.complex.obj := by
  have hc' (q : ℤ) : IsConstructible A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj) := by
    obtain ⟨S, _, _, hS⟩ := hc q
    exact ⟨S, fun i ↦ Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)⟩
  have ho (q : ℤ) := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hc' q)
  obtain ⟨Ke, hKe, ⟨e⟩⟩ := DerivedCategory.boundedConstructible_of_homology A hb ho
  refine ⟨⟨⟨Ke, hKe.1.1⟩, e⟩, ?_⟩
  refine ⟨fun q ↦
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hKe.2 q), ?_⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hKe.1
  refine ⟨min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff Ke a).mp ha q
      (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff Ke b).mp hb q hq

attribute [local irreducible] _root_.DerivedCategory.torAmplitudeIn

private theorem originTor (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A K) (a b : ℤ)
    (h : Scheme.HasFixedCoefficientProEtaleTorAmplitude X A K.obj a b) :
    Etale.DerivedCategory.hasTorAmplitudeIn A X a b W.complex.obj := by
  apply (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
    (Λ := A) (K := W.complex.obj)).mpr
  apply (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (Λ := A) a b W.complex.obj).mp
  exact (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b).prop_of_iso
    W.iso.symm h.2

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.mapDerivedCategory
  DerivedMonoidal.bifunctor

section GenericTensor
universe v w t
variable {V : Type v} [Category.{w} V] [Abelian V] [IsGrothendieckAbelian.{w} V]
  [MonoidalCategory V] [MonoidalPreadditive V] [MonoidalClosed V] [BraidedCategory V]
  [Abelian.HasFunctorialFlatResolution V] [HasDerivedCategory.{t} V]
  [HasColimitsOfSize.{0, 0} V]

private theorem tensorModel (C P : CochainComplex V ℤ) (u0 v0 a b : ℤ)
    [C.IsStrictlyGE u0] [C.IsStrictlyLE v0] [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (M N : _root_.DerivedCategory V) (eC : _root_.DerivedCategory.Q.obj C ≅ M)
    (eP : _root_.DerivedCategory.Q.obj P ≅ N) :
    Nonempty (_root_.DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor C P (curriedTensor V)) ≅ M ⊗ N) ∧
    (∀ i : ℤ, (i < u0 + a ∨ v0 + b < i) → IsZero
      ((CochainComplex.mapBifunctor C P (curriedTensor V)).X i)) ∧
    _root_.DerivedCategory.TStructure.t.plus (M ⊗ N) := by
  let T := CochainComplex.mapBifunctor C P (curriedTensor V)
  have : T.IsStrictlyGE (u0 + a) := CochainComplex.isStrictlyGE_tensorObj C P u0 a
  have : T.IsStrictlyLE (v0 + b) := CochainComplex.isStrictlyLE_tensorObj C P v0 b
  let e : _root_.DerivedCategory.Q.obj T ≅ M ⊗ N :=
    (_root_.DerivedCategory.QObjTensorQObjIsoOfKFlatRight C P hP).symm ≪≫ tensorIso eC eP
  refine ⟨⟨e⟩, ?_, ⟨u0 + a, _root_.DerivedCategory.TStructure.t.isGE_of_iso e _⟩⟩
  intro i hi
  rcases hi with hi | hi
  · exact T.isZero_of_isStrictlyGE (u0 + a) i hi
  · exact T.isZero_of_isStrictlyLE (v0 + b) i hi
end GenericTensor

attribute [local instance 2000] GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem admissibleModels (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (K0 : Etale.DerivedCategoryModule A X) (L0 : Etale.DerivedCategoryModule A Y)
    (u0 v0 a b : ℤ)
    (hK : ∀ i : ℤ, (i < u0 ∨ v0 < i) → IsZero
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K0))
    (hL : Etale.DerivedCategory.hasTorAmplitudeIn A Y a b L0) :
    pfAdmissibleModelAssertions A j r K0 L0 u0 v0 a b := by
  classical
  let : MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let : MonoidalCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    Sheaf.monoidalCategory Z.smallEtaleTopology (ModuleCat.{u + 1} A)
  have : K0.IsGE u0 := (_root_.DerivedCategory.isGE_iff _ _).mpr
    (fun i hi ↦ hK i (Or.inl hi))
  have : K0.IsLE v0 := (_root_.DerivedCategory.isLE_iff _ _).mpr
    (fun i hi ↦ hK i (Or.inr hi))
  obtain ⟨C, hCa, hCb, ⟨eC⟩⟩ := K0.exists_iso_Q_obj_of_isGE_of_isLE u0 v0
  obtain ⟨P, hPa, hPb, hPf, ⟨eP⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hL)
  let F := Etale.upperStar (ModuleCat.{u + 1} A) r
  let J := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let RP : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj P
  let JC : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
    (J.mapHomologicalComplex (.up ℤ)).obj C
  have : RP.IsStrictlyGE a := (RP.isStrictlyGE_iff a).2 fun i hi ↦
    F.map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : RP.IsStrictlyLE b := (RP.isStrictlyLE_iff b).2 fun i hi ↦
    F.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have : JC.IsStrictlyGE u0 := (JC.isStrictlyGE_iff u0).2 fun i hi ↦
    J.map_isZero (C.isZero_of_isStrictlyGE u0 i hi)
  have : JC.IsStrictlyLE v0 := (JC.isStrictlyLE_iff v0).2 fun i hi ↦
    J.map_isZero (C.isZero_of_isStrictlyLE v0 i hi)
  have hRPf (i : ℤ) : ObjectProperty.flat (RP.X i) :=
    Functor.PreservesFlat.flat_obj (F := F) (hPf i)
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P a b hPf
  have hRPk := CochainComplex.kFlat_of_bounded_of_flat RP a b hRPf
  let eRP : _root_.DerivedCategory.Q.obj RP ≅ F.mapDerivedCategory.obj L0 :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP
  let eJC : _root_.DerivedCategory.Q.obj JC ≅ J.mapDerivedCategory.obj K0 :=
    (J.mapDerivedCategoryFactors.app C).symm ≪≫ J.mapDerivedCategory.mapIso eC.symm
  obtain ⟨eT, hT, hQ⟩ := tensorModel JC RP u0 v0 a b hRPk
    (J.mapDerivedCategory.obj K0) (F.mapDerivedCategory.obj L0) eJC eRP
  have hM : _root_.DerivedCategory.TStructure.t.plus (J.mapDerivedCategory.obj K0) :=
    ⟨u0, _root_.DerivedCategory.TStructure.t.isGE_of_iso eJC u0⟩
  dsimp only [pfAdmissibleModelAssertions]
  refine ⟨C, P, ⟨eC.symm⟩, ?_, ⟨eP⟩, fun i ↦ (hPf i).2, ?_, hPk, hRPk,
    ⟨eRP⟩, ⟨eJC⟩, ?_, eT, hT, hM, hQ, inferInstance, inferInstance⟩
  · intro i hi
    rcases hi with hi | hi
    · exact C.isZero_of_isStrictlyGE u0 i hi
    · exact C.isZero_of_isStrictlyLE v0 i hi
  · intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · intro i hi
    rcases hi with hi | hi
    · exact JC.isZero_of_isStrictlyGE u0 i hi
    · exact JC.isZero_of_isStrictlyLE v0 i hi

/-- Etale origins with the same Tor bounds and bounded models for compactification inputs.
Source: Stacks Tags 09AL, 08G1, 06YQ, 0G7E, 06YY, 03DJ, 06YU and 09A6;
blueprint main-20261015, thm-sf-pf-proetale, finite-coefficient transport paragraph
(blueprint: lem-sf-proetale-pf-admissible-models).

Proof:
1. On each constructible stratum, finite stalks give finite constant models. The existing
   fixed-module constructible comparison descends each cohomology sheaf, and bounded
   derived descent gives bounded constructible etale origins. Retain their displayed
   comparison isomorphisms in the D+ witnesses.
2. For every supplied witness, transport categorical Tor amplitude through its specified
   isomorphism and reflect the interval with torAmplitudeIn_mapDerivedCategory_iff.
   Convert this to the recorded etale degree-zero tensor test.
3. Mathlib's exists_iso_Q_obj_of_isGE_of_isLE supplies C with support [u0,v0].
   The source exists_iso_Q_obj_flat_of_torAmplitudeIn supplies P with flat terms and
   support [a,b]. Bounded-above flat complexes are K-flat.
4. Geometric inverse image preserves flat module sheaves; it preserves zero terms as
   an additive functor. Thus RP is bounded flat and K-flat. The exact-functor localization
   isomorphism identifies Q(RP) with the specified derived inverse image of L0.
5. Exact open extension gives the analogous localization isomorphism for JC, and its
   additivity preserves support [u0,v0].
6. QObjTensorQObjIsoOfKFlatRight computes the derived tensor using RP as its K-flat
   factor. Compose with the representing isomorphisms of JC and RP. The signed total
   tensor has strict support [u0+a,v0+b] by the strict tensor support lemmas, so its
   localization is bounded below. The lower support of JC likewise bounds M0 below.
7. Properness supplies quasi-compactness and quasi-separatedness of r. These complete
   the admissibility assertions; no direct-image boundedness is claimed.
-/
theorem proEtale_pf_admissible_models
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r] (_hjr : j ≫ r = f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (pfModelCoefficients l E n))))
    (L : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (pfModelCoefficients l E n))))
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
  obtain ⟨WK, hWK⟩ := boundedOrigin _ X K _hKb _hKc
  obtain ⟨WL, hWL⟩ := boundedOrigin _ Y L _hLb _hLc
  refine ⟨⟨WK, WL, hWK, hWL, originTor _ X K WK c0 d0 _hKTor,
    originTor _ Y L WL a b _hLTor⟩, ?_⟩
  intro WK WL _ _
  have hK := originTor _ X K WK c0 d0 _hKTor
  have hL := originTor _ Y L WL a b _hLTor
  refine ⟨hK, hL, ?_⟩
  intro u0 v0 _ hbound
  exact admissibleModels _ j r WK.complex.obj WL.complex.obj u0 v0 a b hbound hL

end AlgebraicGeometry.ProEtale
