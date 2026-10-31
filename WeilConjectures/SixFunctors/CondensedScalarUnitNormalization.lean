/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement

/-! # Normalized condensed coefficient scalar unit

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six.proof.md, opening and final paragraphs
(blueprint: lem-coef-verdier-scalar-unit-normalization).

The identity coefficient change is the ordinary, uncompleted derived scalar extension
already fixed by `scalarSixChange`.  Its normalized unit is the inverse of the canonical
scalar unitor, and its multiplication adjunct is the unitor itself.  The finite-stage
clause uses the canonical tower comparisons, so no arbitrary isomorphism is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! The finite coefficient notation used by the final tower clause is the
published quotient ring and its discrete condensed ring object. -/
/-- The finite coefficient ring `A_{E,n} = 𝒪_E / π_Eⁿ` of `Padic.coefficientExtensionRing`,
with the discrete topology, as a condensed scalar-six ring (the continuous-function
presentation used by `IsLocalizingAdmissibleCoefficient`).
Source: sk-prop-scalar-six statement, coefficients `A_{E,n}`; node statement, clause
`Λ = A_{E,n}` (blueprint: lem-coef-verdier-scalar-unit-normalization). -/
abbrev finiteCoefficientRing (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E] (n : ℕ) : ScalarSixRing.{u} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell E n) :=
    discreteTopology_bot _
  scalarSixTopologicalRing (Padic.coefficientExtensionRing ell E n)

/-- The quotient map `b : A_{E,n} → A_{E,m}` for `m ≤ n`, the canonical quotient factor
map, continuous for the discrete topologies, as a map of condensed scalar-six rings.
Source: node statement, clause `b : A_{E,n} → A_{E,m}`
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def finiteCoefficientMap (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E] {m n : ℕ} (hmn : m ≤ n) :
    finiteCoefficientRing ell E n ⟶ finiteCoefficientRing ell E m :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell E n) := ⊥
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell E m) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell E n) :=
    discreteTopology_bot _
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell E m) :=
    discreteTopology_bot _
  scalarSixContinuousMap
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) continuous_of_discreteTopology

/-- The derived restriction along the identity coefficient map is the identity functor:
the canonical composite of `coefficientMap_id`, `Mod.comapId` and the identity of the
derived category.
Source: scalar-six proof, opening paragraph; node statement, "whose right adjoint is the
identity restriction" (blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityRestriction (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
  Functor.mapDerivedCategoryNatIso
      (Mod.comapCongr (coefficientMap_id (Λ := Λ.X) X)) ≪≫
    Functor.mapDerivedCategoryNatIso (Mod.comapId (condensedRingObj Λ.X X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The derived extension/restriction adjunction `T_id ⊣ Res_id` of
`Mod.derivedExtendMapDerivedCategoryAdjunction` for the identity coefficient map, with its
right adjoint identified with the identity by `condensedScalarIdentityRestriction`.
Source: Stacks Tag 07A6 and Tag 0FND, identity ring map; node statement
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityAdjunction (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    scalarSixChange (𝟙 Λ) X ⊣
      𝟭 (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).ofNatIsoRight
      (condensedScalarIdentityRestriction Λ X)

/-- Termwise restriction along the identity coefficient map is the identity functor.
Source: Stacks Tag 07A6, identity ring map
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityOrdinaryRestriction (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X) ≅
      𝟭 (ModuleRingedComparison.internalModules Λ.X X) :=
  Mod.comapCongr (coefficientMap_id (Λ := Λ.X) X) ≪≫
    Mod.comapId (condensedRingObj Λ.X X)

/-- The chain level extension/restriction adjunction for the identity coefficient map,
applied termwise to cochain complexes.
Source: Stacks Tag 07A6, identity ring map; node proof step 2
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityChainAdjunction (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).mapHomologicalComplex
        (.up ℤ)) ⊣
      ((𝟭 (ModuleRingedComparison.internalModules Λ.X X)).mapHomologicalComplex (.up ℤ)) :=
  ((Mod.extendRestrictAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).ofNatIsoRight
    (condensedScalarIdentityOrdinaryRestriction Λ X)).mapHomologicalComplex (.up ℤ)

/-- The chain map `η_P : P → Λ_X ⊗_{Λ_X} P`, `p ↦ 1 ⊗ p` (unit of the chain adjunction).
Source: node statement, representative of `u_K`
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityChainUnit (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules Λ.X X) ℤ) :
    P ⟶ ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).mapHomologicalComplex
        (.up ℤ)).obj P :=
  (condensedScalarIdentityChainAdjunction Λ X).unit.app P

/-- The chain map `μ_P : Λ_X ⊗_{Λ_X} P → P`, `a ⊗ p ↦ a · p` (adjunct of `𝟙 P`).
Source: node statement, representative of `v_K`
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityChainMultiplication (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules Λ.X X) ℤ) :
    ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).mapHomologicalComplex
        (.up ℤ)).obj P ⟶ P :=
  ((condensedScalarIdentityChainAdjunction Λ X).homEquiv P P).symm (𝟙 P)

/-- The comparison `T_id (Q P) → Q(Λ_X ⊗_{Λ_X} P)` of the left derived functor on a
representative (counit of `leftDerivedFunctor`); an isomorphism for K-flat `P`.
Source: Stacks Tag 0FND; node proof step 2, `c_P`
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityRepresentativeCounit (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules Λ.X X) ℤ) :
    (scalarSixChange (𝟙 Λ) X).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((Mod.extendScalars
        (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (Mod.extendScalars
    (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The normalized derived adjunction unit `u_K : K → T_id K`.
Source: node statement, `u_K`; Stacks Tag 07A6 and Tag 0FND
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityUnit (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    K ⟶ (scalarSixChange (𝟙 Λ) X).obj K :=
  (condensedScalarIdentityAdjunction Λ X).unit.app K

/-- The adjunct `v_K : T_id K → K` of `𝟙 K` under the identity adjunction.
Source: node statement, `v_K`; scalar-six proof, opening paragraph
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityMultiplication (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange (𝟙 Λ) X).obj K ⟶ K :=
  ((condensedScalarIdentityAdjunction Λ X).homEquiv K K).symm (𝟙 K)

/-- The comparison `γ : T_b T_id ≅ T_{b∘id} = T_b = T_{id∘b} ≅ T_id T_b`, composite of the
canonical scalar composition comparisons `scalarSixTower`.
Source: scalar-six proof, final paragraph; node statement, `γ_K`
(blueprint: lem-coef-verdier-scalar-unit-normalization). -/
def condensedScalarIdentityComparison {Λ Λ' : ScalarSixRing.{u}} (b : Λ ⟶ Λ') (X : Scheme.{u}) :
    scalarSixChange (𝟙 Λ) X ⋙ scalarSixChange b X ≅
      scalarSixChange b X ⋙ scalarSixChange (𝟙 Λ') X :=
  scalarSixTower (𝟙 Λ) b X ≪≫
    eqToIso (congrArg (fun c ↦ scalarSixChange c X)
      ((Category.id_comp b).trans (Category.comp_id b).symm)) ≪≫
    (scalarSixTower b (𝟙 Λ') X).symm

/-- Identity scalar units and their finite coefficient compatibility are normalized by the
canonical derived change-of-rings adjunction.  On flat-term K-flat models the two maps are
respectively insertion of `1` and scalar multiplication; the displayed comparison is the
canonical composition comparison.  The assertion includes zero objects and empty schemes.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six.proof.md, opening and final paragraphs
(blueprint: lem-coef-verdier-scalar-unit-normalization).

Proof.
1. The coefficient datum, `D_ctf` and the derived tensor are those of sk-prop-scalar-six,
   det-def-sf-operations, det-def-sfb-bounded-constructible and sk-def-sfb-derived-tensor-hom;
   the identity coefficient map gives `T_id K = Λ_X ⊗^L_{Λ_X} K` with its derived
   extension/restriction adjunction (sk-def-sfb-coefficient-change,
   sk-def-sfb-derived-extension-of-scalars).
2. Through the tensor equivalence of lem-pe-internal-section-tensor-comparison and the
   symmetry, `T_id ⊣ Res_id` is the derived change of rings of
   lem-pur-sheaf-ring-derived-coefficient-adjunction (def-sf-condensed-scalar-tensor-comparison).
   Choose a flat-term K-flat `P → K` (lem-pc-kflat-resolution); then `c_P` is invertible.
   By clause (1) of that lemma, `u_K` is the class of `η_P : p ↦ 1 ⊗ p`; since
   `Res_id P = P`, clause (2) with `g = 𝟙 P` shows `v_K` is the class of
   `μ_P : a ⊗ p ↦ a · p`. Termwise `μ_P` is the left unitor with inverse `η_P`
   (`μη(p) = p`, `ημ(a ⊗ p) = 1 ⊗ ap = a ⊗ p`), so `u_K`, `v_K` are inverse. `u` is natural
   as a unit and `v` as the adjunct of the identity. For `K = 0` or `X = ∅` all objects
   are zero.
3. For `Λ = A_{E,n}` and `b : A_{E,n} → A_{E,m}`, sk-prop-scalar-six gives `T_b K ∈ D_ctf`.
   By lem-sfb-ringed-derived-monoidal-comparisons the comparisons in `γ_K` are computed on
   flat-term K-flat complexes by composition of module pullbacks; by
   lem-pur-kflat-change-of-rings and lem-pur-derived-change-of-rings,
   `(A_{E,m})_X ⊗ P` is flat-term K-flat and represents `T_b K`. On these representatives
   `T_b(u_K)` is `c ⊗ p ↦ c ⊗ (1 ⊗ p)`, `γ_K` is `c ⊗ (a ⊗ p) ↦ 1 ⊗ (c ⊗ ap)` and
   `u_{T_b K}` is `c ⊗ p ↦ 1 ⊗ (c ⊗ p)`, so `γ_K ∘ T_b(u_K) = u_{T_b K}`. Since `v = u⁻¹`,
   `v_{T_b K} ∘ γ_K = T_b(u_K)⁻¹ = T_b(v_K)`.
-/
theorem condensedScalarUnitNormalization (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) (Λ : ScalarSixRing.{u})
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (∀ {L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)}
      (f : K.obj ⟶ L),
      f ≫ condensedScalarIdentityUnit Λ X.left L =
        condensedScalarIdentityUnit Λ X.left K.obj ≫
          (scalarSixChange (𝟙 Λ) X.left).map f) ∧
      (∀ {L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)}
        (f : K.obj ⟶ L),
        (scalarSixChange (𝟙 Λ) X.left).map f ≫
            condensedScalarIdentityMultiplication Λ X.left L =
          condensedScalarIdentityMultiplication Λ X.left K.obj ≫ f) ∧
      IsIso (condensedScalarIdentityUnit Λ X.left K.obj) ∧
      IsIso (condensedScalarIdentityMultiplication Λ X.left K.obj) ∧
      (condensedScalarIdentityUnit Λ X.left K.obj ≫ condensedScalarIdentityMultiplication Λ X.left
          K.obj = 𝟙 K.obj) ∧
      (condensedScalarIdentityMultiplication Λ X.left K.obj ≫ condensedScalarIdentityUnit Λ X.left
          K.obj = 𝟙 ((scalarSixChange (𝟙 Λ) X.left).obj K.obj)) ∧
      (∀ (P : CochainComplex
          (ModuleRingedComparison.internalModules Λ.X X.left) ℤ)
        (e : DerivedCategory.Q.obj P ≅ K.obj)
        (_hP : (HomologicalComplex.quasiIso
          (ModuleRingedComparison.internalModules Λ.X X.left) (.up ℤ)).kFlat P)
        (_hflat : ∀ i : ℤ, ObjectProperty.flat (P.X i)),
        IsIso (condensedScalarIdentityRepresentativeCounit Λ X.left P) ∧
        (∀ i : ℤ,
          ((condensedScalarIdentityChainUnit Λ X.left P).f i).hom =
            Mod.extendUnitHom
              (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X.left) (P.X i)) ∧
        (∀ i : ℤ,
          Mod.extendπ (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X.left) (P.X i) ≫
            ((condensedScalarIdentityChainMultiplication Λ X.left P).f i).hom =
              γ[condensedRingObj Λ.X X.left, (P.X i).X]) ∧
        ∀ (c : (scalarSixChange (𝟙 Λ) X.left).obj (DerivedCategory.Q.obj P) ≅
          DerivedCategory.Q.obj (((Mod.extendScalars
            (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 _) X.left)).mapHomologicalComplex
              (.up ℤ)).obj P))
          (_hc : c.hom = condensedScalarIdentityRepresentativeCounit Λ X.left P),
          (e.inv ≫ DerivedCategory.Q.map (condensedScalarIdentityChainUnit Λ X.left P) ≫
            c.inv ≫ (scalarSixChange (𝟙 Λ) X.left).map e.hom =
              condensedScalarIdentityUnit Λ X.left K.obj) ∧
          ((scalarSixChange (𝟙 Λ) X.left).map e.inv ≫ c.hom ≫
            DerivedCategory.Q.map (condensedScalarIdentityChainMultiplication Λ X.left P) ≫
              e.hom = condensedScalarIdentityMultiplication Λ X.left K.obj)) ∧
      (∀ (E : Type) [Field E] [Algebra ℚ_[ell] E]
        [FiniteDimensional ℚ_[ell] E] (n m : ℕ) (_hn : 1 ≤ n) (_hm : 1 ≤ m) (hmn : m ≤ n)
        (hΛE : Λ = finiteCoefficientRing ell E n),
        (constantModelBoundedConstructible
          (finiteCoefficientRing ell E m).X X.left ⊓
          DerivedCategory.finiteTorAmplitude _)
          ((scalarSixChange (finiteCoefficientMap ell E hmn) X.left).obj (hΛE ▸ K.obj)) ∧
        (scalarSixChange (finiteCoefficientMap ell E hmn) X.left).map
            (condensedScalarIdentityUnit (finiteCoefficientRing ell E n) X.left
              (hΛE ▸ K.obj)) ≫
          (condensedScalarIdentityComparison (finiteCoefficientMap ell E hmn) X.left).hom.app
            (hΛE ▸ K.obj) =
          condensedScalarIdentityUnit (finiteCoefficientRing ell E m) X.left
            ((scalarSixChange (finiteCoefficientMap ell E hmn) X.left).obj (hΛE ▸ K.obj))) ∧
      (∀ (E : Type) [Field E] [Algebra ℚ_[ell] E]
        [FiniteDimensional ℚ_[ell] E] (n m : ℕ) (_hn : 1 ≤ n) (_hm : 1 ≤ m) (hmn : m ≤ n)
        (hΛE : Λ = finiteCoefficientRing ell E n),
        (condensedScalarIdentityComparison (finiteCoefficientMap ell E hmn) X.left).hom.app
            (hΛE ▸ K.obj) ≫
          condensedScalarIdentityMultiplication (finiteCoefficientRing ell E m) X.left
            ((scalarSixChange (finiteCoefficientMap ell E hmn) X.left).obj (hΛE ▸ K.obj)) =
          (scalarSixChange (finiteCoefficientMap ell E hmn) X.left).map
            (condensedScalarIdentityMultiplication (finiteCoefficientRing ell E n) X.left
              (hΛE ▸ K.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
