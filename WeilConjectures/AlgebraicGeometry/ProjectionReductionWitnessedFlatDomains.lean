/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare
public import WeilConjectures.AlgebraicGeometry.EtalePullbackLineFlatModel
public import WeilConjectures.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleComplex
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.ConstructibleCoefficientSiteSquare
import WeilConjectures.Compactification.Noetherian

/-! # Witnessed flat domains for finite reduction of the projection formula

Source: main-20261015, sec-six-functors-basics/sk-prop-sf-pf-reduction,
prop-sf-pf-reduction.proof.md, first paragraph and compactification inputs
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains).

The helpers only abbreviate the actual complexes, coefficient maps and domain clauses
of this node. Coefficient changes retain their target-ring actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace WeilConjectures.ProjectionReduction

/-- The quotient coefficient ring in the module-sheaf size convention.
Source: main-20261015, projection reduction, coefficient datum
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev Coeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)

/-- Finiteness at a positive coefficient level, using the recorded coefficient theorem.
Source: main-20261015, projection reduction, coefficient datum
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
instance finiteCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Coeff l E n) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n))
    Equiv.ulift.symm

/-- The quotient map induced by the inclusion of powers of the uniformizer ideal.
Source: main-20261015, projection reduction, coefficient datum
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def quotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {m n : ℕ} (hmn : m ≤ n) :
    Coeff l E n →+* Coeff l E m :=
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)).ulift

/-- The ordinary etale complex category used for the representatives.
Source: main-20261015, projection reduction, flat-model clause
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev EtaleComplex (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ

/-- The ordinary constant-coefficient pro-etale derived category.
Source: main-20261015, projection reduction, ambient-category clause
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev ProDerived (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))

/-- Exact comparison applied to the localization of the specified etale complex.
Source: main-20261015, projection reduction, etale-origin witnesses
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev origin (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (P : EtaleComplex R X) : ProDerived R X :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj
    (_root_.DerivedCategory.Q.obj P)

/-- Exactly the three termwise model requirements in the node.
Source: main-20261015, projection reduction, flat-model clause
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def model (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u}) (a b : ℤ)
    (P : EtaleComplex R X) : Prop :=
  (∀ q : ℤ, exactFunctor _ _
    (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
      (ModuleCat.{u + 1} R)) (P.X q))) ∧
  (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) ∧
  (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))

/-- The termwise scalar extension, rather than its derived functor.
Source: main-20261015, projection reduction, definition of P_B and Q_B
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev reduceComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (P : EtaleComplex A X) : EtaleComplex B X :=
  ((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P

/-- The signed total tensor of P and the actual termwise inverse image of Q.
Source: main-20261015, projection reduction, total-tensor clause
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def total (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : EtaleComplex R X) (Q : EtaleComplex R Y) : EtaleComplex R X :=
  CochainComplex.mapBifunctor P
    (((Etale.upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj Q)
    (@curriedTensor _ _ (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} R)))

/-- The actual derived tensor input H_R, with the recorded derived pullback.
Source: main-20261015, projection reduction, definition of H_R
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev tensorInput (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : ProDerived R X) (L : ProDerived R Y) : ProDerived R X :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) X).obj K).obj
    ((ProEtale.upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj L)

/-- The actual exact derived extension by zero for an open immersion.
Source: main-20261015, projection reduction, proper-factor inputs
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
abbrev extend (R : Type (u + 1)) [CommRing R] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : ProDerived R U ⥤ ProDerived R X :=
  (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory

/-- The prescribed canonical open tensor isomorphism, preceded by pullback composition.
Source: main-20261015, projection reduction, final clause; Stacks 0GL1 and 0D6D
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def openTensorIso (R : Type (u + 1)) [CommRing R] [Finite R] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : ProDerived R X) (L : ProDerived R Y) :
    (extend R c.i).obj (tensorInput R f K L) ≅
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) c.Z).obj
        ((extend R c.i).obj K)).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj L) :=
  (extend R c.i).mapIso
    (((ProEtale.derivedTensor (ModuleCat.{u + 1} R) X).obj K).mapIso
      (((ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) c.comm) ≪≫
        ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} R) c.i c.g).app L)) ≪≫
    (((ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} R) c.i).app K).app
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj L))

/-- A witnessed bounded constructible domain and the full prescribed Tor test.
Source: main-20261015, projection reduction, proper-factor domain clause
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def witnessedDomain (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (a b : ℤ) (K : ProDerived R X) : Prop :=
  ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K ∧
  ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b K ∧
  ∃ O : Etale.DerivedCategoryModule R X,
    Etale.DerivedCategory.isBoundedConstructible R X O ∧
    Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj O ≅ K)

/-- All assertions for one of the two coefficient rings, on the same chosen P and Q.
Source: main-20261015, projection reduction, both finite stages and compactifications
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains). -/
def stage (R : Type (u + 1)) [CommRing R] [Finite R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a b c d : ℤ) (P : EtaleComplex R X) (Q : EtaleComplex R Y)
    (K : ProDerived R X) (L : ProDerived R Y) : Prop :=
  model R X a b P ∧ model R Y c d Q ∧
  Nonempty (origin R X P ≅ K) ∧ Nonempty (origin R Y Q ≅ L) ∧
  model R X (a + c) (b + d) (total R f P Q) ∧
  Nonempty (origin R X (total R f P Q) ≅ tensorInput R f K L) ∧
  witnessedDomain R X a b K ∧ witnessedDomain R Y c d L ∧
  witnessedDomain R X (a + c) (b + d) (tensorInput R f K L) ∧
  ∀ comp : Compactification f,
    witnessedDomain R comp.Z a b ((extend R comp.i).obj K) ∧
    witnessedDomain R comp.Z (a + c) (b + d)
      ((extend R comp.i).obj (tensorInput R f K L))

private theorem finiteValue_of_bounded (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule R X)
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X K) :
    Etale.DerivedCategory.isBoundedConstructible R X K := by
  refine ⟨fun q ↦
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hK.2 q), ?_⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  refine ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q
      (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q
      (lt_of_le_of_lt (le_max_right _ _) hq)

private theorem witnessed_of_ctf (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) (a b : ℤ) (K : ProDerived R X)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K)
    (ht : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b K) :
    witnessedDomain R X a b K := by
  obtain ⟨O, hO, e⟩ := hK.1
  exact ⟨hK, ht, O, finiteValue_of_bounded R X O hO, e⟩

private theorem exists_model (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) [IsNoetherian X] (a b : ℤ) (hab : a ≤ b) (K : ProDerived R X)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K)
    (ht : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b K) :
    ∃ P : EtaleComplex R X, model R X a b P ∧ Nonempty (origin R X P ≅ K) := by
  obtain ⟨O, hO, ⟨e⟩⟩ := hK.1
  have htO := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b O).1
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht)
  obtain ⟨P, hf, hc, hz, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel R X a b hab O
      (finiteValue_of_bounded R X O hO)).1
        ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).2 htO)
  exact ⟨P, ⟨fun q ↦ (hf q).2, hc, hz⟩,
    ⟨(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.mapIso eP ≪≫ e⟩⟩

private theorem flat_of_exact {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (h : exactFunctor _ _ (tensorRight F)) : ObjectProperty.flat F :=
  ⟨(exactFunctor _ _).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight F).symm h, h⟩

private theorem model_pullback (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : ℤ) (P : EtaleComplex R Y)
    (hP : model R Y a b P) :
    model R X a b (((Etale.upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex
      (.up ℤ)).obj P) := by
  refine ⟨fun q ↦ ?_, fun q ↦ ?_, fun q hq ↦ ?_⟩
  · exact (Functor.PreservesFlat.flat_obj
      (F := Etale.upperStar (ModuleCat.{u + 1} R) f)
      (flat_of_exact (P.X q) (hP.1 q))).2
  · have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hP.2.1 q)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.upperStar f (P.X q))
  · exact (Etale.upperStar (ModuleCat.{u + 1} R) f).map_isZero (hP.2.2 q hq)

private theorem ctf_of_model (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) [IsNoetherian X] (a b : ℤ) (P : EtaleComplex R X)
    (hP : model R X a b P) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X
      (_root_.DerivedCategory.Q.obj P) := by
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 fun q hq ↦ hP.2.2 q (.inl hq)
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 fun q hq ↦ hP.2.2 q (.inr hq)
  exact Etale.DerivedCategory.constructibleFiniteTor_Q_obj P a b
    (fun q ↦ flat_of_exact (P.X q) (hP.1 q))
    (fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hP.2.1 q))

private theorem domain_of_model (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) [IsNoetherian X] (a b : ℤ) (_hab : a ≤ b)
    (P : EtaleComplex R X) (hP : model R X a b P)
    (K : ProDerived R X) (e : origin R X P ≅ K) : witnessedDomain R X a b K := by
  have hc := ctf_of_model R X a b P hP
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 fun q hq ↦ hP.2.2 q (.inl hq)
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 fun q hq ↦ hP.2.2 q (.inr hq)
  have ht' := _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b
    (fun q ↦ flat_of_exact (P.X q) (hP.1 q))
  exact witnessed_of_ctf R X a b K
    ((ProEtale.DerivedCategory.constructibleFiniteTor _ X).prop_of_iso e
      (ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory R hc))
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory R ht'))

private theorem domain_open (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (a b : ℤ) (K : ProDerived R X) (hK : witnessedDomain R X a b K) :
    witnessedDomain R Z a b ((extend R j).obj K) := by
  obtain ⟨O, hO, ⟨e⟩⟩ := hK.1.1
  have ht := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b O).1
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm hK.2.1)
  have h :=
    Etale.boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
      R j hO (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht) ht
  let e' := (ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} R) j).app O ≪≫ (extend R j).mapIso e
  exact witnessed_of_ctf R Z a b _
    ((ProEtale.DerivedCategory.constructibleFiniteTor _ Z).prop_of_iso e'
      (ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory R
        ⟨h.1, a, b, h.2.2⟩))
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e'
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory R h.2.2))

private theorem total_model_origin (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P : EtaleComplex R X) (Q : EtaleComplex R Y)
    (hP : model R X a b P) (hQ : model R Y c d Q)
    (K : ProDerived R X) (L : ProDerived R Y)
    (eP : origin R X P ≅ K) (eQ : origin R Y Q ≅ L) :
    model R X (a + c) (b + d) (total R f P Q) ∧
      Nonempty (origin R X (total R f P Q) ≅ tensorInput R f K L) := by
  let F := Etale.upperStar (ModuleCat.{u + 1} R) f
  let Q' := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have hQ' := model_pullback R f c d Q hQ
  have h := Etale.finiteFlatConstructible_totalTensor R X a b c d hab hcd P Q'
    hP.1 hQ'.1 hP.2.1 hQ'.2.1 hP.2.2 hQ'.2.2 (total R f P Q) rfl
  refine ⟨⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
  obtain ⟨e⟩ := h.2.2.2.2.2.1
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X
  let G := ProEtale.upperStar (ModuleCat.{u + 1} R) f
  let epull : N.mapDerivedCategory.obj (_root_.DerivedCategory.Q.obj Q') ≅
      G.leftDerivedFunctor.obj L :=
    (N.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app Q).symm) ≪≫
      ((ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} R) f).app (_root_.DerivedCategory.Q.obj Q)).symm ≪≫
      G.mapDerivedCategory.mapIso eQ ≪≫
      (G.leftDerivedFunctorIsoMapDerivedCategory.app L).symm
  exact ⟨N.mapDerivedCategory.mapIso e ≪≫
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} R) (_root_.DerivedCategory.Q.obj P)).app
        (_root_.DerivedCategory.Q.obj Q') ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) X).mapIso eP).app _ ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) X).obj K).mapIso epull⟩

private theorem stage_of_models (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P : EtaleComplex R X) (Q : EtaleComplex R Y)
    (hP : model R X a b P) (hQ : model R Y c d Q)
    (K : ProDerived R X) (L : ProDerived R Y)
    (eP : origin R X P ≅ K) (eQ : origin R Y Q ≅ L) :
    stage R f a b c d P Q K L := by
  obtain ⟨hT, ⟨eT⟩⟩ := total_model_origin R f a b c d hab hcd P Q hP hQ K L eP eQ
  have hK := domain_of_model R X a b hab P hP K eP
  have hL := domain_of_model R Y c d hcd Q hQ L eQ
  have hH := domain_of_model R X (a + c) (b + d) (add_le_add hab hcd)
    (total R f P Q) hT _ eT
  refine ⟨hP, hQ, ⟨eP⟩, ⟨eQ⟩, hT, ⟨eT⟩, hK, hL, hH, fun comp ↦ ?_⟩
  have : TopologicalSpace.NoetherianSpace X := inferInstance
  have : QuasiCompact comp.i :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact ⟨domain_open R comp.i a b K hK,
    domain_open R comp.i (a + c) (b + d) _ hH⟩

private theorem reduction_model_origin {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X] (a b : ℤ) (hab : a ≤ b)
    (P : EtaleComplex A X) (hP : model A X a b P)
    (K : ProDerived A X) (eP : origin A X P ≅ K) :
    model B X a b (reduceComplex φ X P) ∧
      Nonempty (origin B X (reduceComplex φ X P) ≅
        (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X).obj K) := by
  have hflat := ProEtale.BoundedFlatCoefficientSiteSquare.boundedFlatCoefficientSiteSquare
    X φ a b hab P hP.1 hP.2.2
  have hcons := constructibleCoefficientSiteSquare X A B φ a b hab P hP.2.2 hP.2.1
  refine ⟨⟨hflat.2.1.1.1, hcons.1, hflat.2.1.1.2.1⟩, ?_⟩
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let M := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
  let S := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X
  have := hflat.2.2.2.2.2.2.1
  exact ⟨M.mapDerivedCategoryFactors.app (reduceComplex φ X P) ≪≫
    _root_.DerivedCategory.Q.mapIso
      ((ProEtale.BoundedFlatCoefficientSiteSquare.chainComparison φ X).app P) ≪≫
    (asIso (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ X
      ((N.mapHomologicalComplex (.up ℤ)).obj P))).symm ≪≫
    S.mapIso ((N.mapDerivedCategoryFactors.app P).symm ≪≫ eP)⟩

/-- Simultaneous flat constructible etale-origin witnesses for finite coefficient
reduction, pullback, total tensor and every compactification's two proper-factor inputs.
The isomorphism identifying the second input with the proper-factor tensor is the
explicit `openTensorIso`, constructed from the recorded canonical open projection formula.

Source: main-20261015, sec-six-functors-basics/sk-prop-sf-pf-reduction,
prop-sf-pf-reduction.proof.md, first paragraph and compactification inputs
(blueprint: lem-sf-pf-reduction-witnessed-flat-domains).

Proof plan:
1. The coefficient quotients are finite (def-weil-l-adic-coefficient-extension).
   Finite-type schemes over k are Noetherian (finite-type-over-noetherian).
   Since ell differs from the characteristic, ell is invertible on every k-scheme.
2. Choose bounded constructible etale origins using finite-ring-constructible-derived-origin.
   Comparison-tor-interval reflects the full Tor tests to these origins.
3. Etale-flat-constructible gives models in the exact specified intervals. Apply
   bounded-flat-coefficient-site-square and constructible-coefficient-site-square:
   the termwise reductions are flat, constructible, supported in the same intervals
   and represent the actual derived reductions, retaining their B-actions. The
   reduced origin witness is N_B[P_B] -> [N_B P_B] -> [(N_A P)_B] ->
   N_A[P] tensor B -> K tensor B, using the inverse scalar-adjunction mate.
   On the empty scheme use the one-empty-stratum zero-module normalization.
4. Etale-pullback-line-flat-model with the trivial line and zero shift gives the
   termwise inverse image of Q. Comparison-pullback and proetale-constant-exact
   identify its comparison image with the recorded derived pullback of L.
5. Finite-flat-constructible-total-tensor gives the signed total model, its sum
   interval and its full Tor test. Ringed-topoi-derived-tensor-pullback identifies
   its comparison image with H. The chosen origins supply the witnessed domains.
6. Nagata-sketch-noetherian gives a compactification. For every compactification,
   properness and finite-type composition make the ambient scheme finite type over
   k and Noetherian, so the same coefficient and origin results apply there.
7. Open-ctf preserves the exact Tor intervals for K and H. Choose bounded
   constructible etale origins of their extensions by finite-ring-derived-origin.
8. Extension-zero-projection-formula, exact constant inverse image, and derived
   pullback composition for the same open/proper factorization give precisely
   openTensorIso, identifying j_!H with j_!K tensor Lr^*L. No flatness of B over A
   is used, and all Tor tests range over every module sheaf in degree zero. -/
theorem exists_witnessedFlatDomains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (m n : ℕ) [Fact (1 ≤ m)] [Fact (1 ≤ n)] (hmn : m ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K : ProDerived (Coeff C.l E n) X) (L : ProDerived (Coeff C.l E n) Y)
    (_hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Coeff C.l E n)) X K)
    (_hL : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Coeff C.l E n)) Y L)
    (_hKTor : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (Coeff C.l E n)) X a b K)
    (_hLTor : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (Coeff C.l E n)) Y c d L) :
    Nonempty (Compactification f) ∧
    ∃ (P : EtaleComplex (Coeff C.l E n) X) (Q : EtaleComplex (Coeff C.l E n) Y),
      stage (Coeff C.l E n) f a b c d P Q K L ∧
      stage (Coeff C.l E m) f a b c d
        (reduceComplex (quotient C.l E hmn) X P)
        (reduceComplex (quotient C.l E hmn) Y Q)
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar (quotient C.l E hmn) X).obj K)
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar (quotient C.l E hmn) Y).obj L) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of D.k))
  have : IsNoetherian Y := ⟨⟩
  have := nagataCompactification_of_isNoetherian f
  refine ⟨⟨HasCompactification.compactification f⟩, ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_model (Coeff C.l E n) X a b _hab K _hK _hKTor
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_model (Coeff C.l E n) Y c d _hcd L _hL _hLTor
  obtain ⟨hPB, ⟨ePB⟩⟩ := reduction_model_origin (quotient C.l E hmn) X a b _hab P hP K eP
  obtain ⟨hQB, ⟨eQB⟩⟩ := reduction_model_origin (quotient C.l E hmn) Y c d _hcd Q hQ L eQ
  exact ⟨P, Q, stage_of_models _ f a b c d _hab _hcd P Q hP hQ K L eP eQ,
    stage_of_models _ f a b c d _hab _hcd _ _ hPB hQB _ _ ePB eQB⟩

end WeilConjectures.ProjectionReduction
