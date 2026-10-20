/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralUniformCoefficient

/-! # Completed coefficient presentation and tensor transport

Source: main-20261015, sec-six-functors-basics/sk-lem-sf-mate,
fix-prop-adjunctions.proof.md, Step 1; Stacks 099N (2),(5), 03D7, 070I;
Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: def-pur-completed-coefficient-presentation-transport).

The coefficient ring comparison and derived transport are the landed integral
stratified-perfect interfaces. Only the CommRing lift, its explicit inverse
restriction model, completeness tests and normalized tensor comparison are supplied here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section CoefficientPresentation
variable (W : Scheme.{u})

/-- Lift the landed Ring-level coefficient comparison to commutative ring sheaves.
Its image under forgetting commutativity is the existing normalized comparison.
Source: Stacks 099N and Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: a morphism between commutative rings is exactly a ring morphism. Thus the
forgetful functor on ring sheaves is fully faithful. Lift the existing comparison
and its inverse. Faithfulness gives their inverse identities and uniqueness. The
finite projection normalization is inherited from the landed comparison. -/
theorem purCoefficientIso_existsUnique :
    ∃! e : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E W,
      (adicLisseForget W).mapIso e = integralDetailedCoefficientComparison W l E := by
  sorry

/-- The CommRing lift of integralDetailedCoefficientComparison, with no new choice
of normalization. Source: Stacks 099N
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCoefficientIso := (purCoefficientIso_existsUnique l E W).exists.choose

end CoefficientPresentation

/-- The actual coefficient transport on ordinary module sheaves.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
abbrev purOrdinaryCoefficientModel (W : Scheme.{u}) :
    pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)) ⥤
      integralTowerModules.{u, u} l E W :=
  pbcRestrict (purCoefficientIso l E W).inv

/-- Additivity of the specified exact coefficient restriction.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_additive (W : Scheme.{u}) :
    (purOrdinaryCoefficientModel l E W).Additive := pbcRestrict_additive _

/-- Exactness of the specified coefficient restriction on finite limits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_limits _

/-- Exactness of the specified coefficient restriction on finite colimits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_colimits _

/-- The ordinary restriction round trip is the identity on every section.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: the CommRing lift forgets to the landed ring isomorphism. Restricting along
its inverse and then its forward map restores the same scalar action. Identity
section functions are linear and natural, with identity inverses. Sections detect
module morphisms, so this normalization determines the isomorphism uniquely. -/
theorem purOrdinaryCoefficientRoundTrip_existsUnique (W : Scheme.{u}) :
    ∃! e : purOrdinaryCoefficientModel l E W ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison W l E).hom ≅
      𝟭 (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))),
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  sorry

/-- The uniquely section-normalized ordinary restriction round trip.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purOrdinaryCoefficientRoundTrip (W : Scheme.{u}) :=
  (purOrdinaryCoefficientRoundTrip_existsUnique l E W).exists.choose

/-- The landed integralDetailedTransport is an equivalence.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: restriction along the inverse coefficient ring isomorphism is an exact
inverse to the landed restriction functor. Both ordinary round trips are identity
on sections. Termwise round trips descend through derived localization, proving
full faithfulness and essential surjectivity of the existing functor. -/
@[instance] theorem purDetailedTransport_isEquivalence (W : Scheme.{u}) :
    (integralDetailedTransport W l E).IsEquivalence := by
  sorry

/-- The exact restriction round trip, descended by the published localization API.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purDerivedCoefficientRoundTrip (W : Scheme.{u}) :
    pbcDerivedRestrict (purCoefficientIso l E W).inv ⋙
      integralDetailedTransport W l E ≅
        𝟭 (PbcCompletedDerived W (pbcIntegralDatum l E)) :=
  letI := (integralDetailedCoefficientRestriction_exact W l E).1
  letI := (integralDetailedCoefficientRestriction_exact W l E).2
  (Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
    (SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison W l E).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (purOrdinaryCoefficientRoundTrip l E W) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Reuse the inverse of the landed transport. changeFunctor gives its explicit
CommRing restriction model via the identity-on-sections round trip; the inverse
functor remains exactly integralDetailedTransport.
Source: Stacks 099N (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCoefficientModel (W : Scheme.{u}) :
    PbcCompletedDerived W (pbcIntegralDatum l E) ≌
      DerivedCategory (integralTowerModules.{u, u} l E W) :=
  (integralDetailedTransport W l E).asEquivalence.symm.changeFunctor
    ((Iso.isoCompInverse
      (H := (integralDetailedTransport W l E).asEquivalence)
      (purDerivedCoefficientRoundTrip l E W) ≪≫ Functor.leftUnitor _).symm)

/-- Completeness alone is invariant under the existing coefficient transport.
Source: Stacks 099N, Bhatt--Scholze 6.5
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: normalized coefficient projections identify the finite reductions and
quotient units. Exact restriction preserves the product and Roos descriptions of
the completion unit, so its being invertible is unchanged. The recorded intrinsic
and slice completeness predicates test this same unit, without geometric bounds. -/
theorem purCoefficientModel_predicates (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IntegralOnSlice.IsComplete l E W none ((purCoefficientModel l E W).functor.obj K)) ∧
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IsSfDerivedComplete l E W ((purCoefficientModel l E W).functor.obj K)) := by
  sorry

/-- Bounded constructibility comparison under exactly the landed geometric bounds.
Source: Bhatt--Scholze 6.5.1, 6.8.11(3)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: apply integralStratifiedPerfectDetailed to the transported object. The
inverse functor of purCoefficientModel is the landed integralDetailedTransport,
so its unit identifies the resulting object with K. Both bounded constructible
predicates are invariant under that isomorphism. The Noetherian, dimension and
invertibility assumptions are precisely those of the landed characterization. -/
theorem purCoefficientModel_bounded_predicate (W : Scheme.{u}) [IsNoetherian W]
    (_hdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hinv : IsUnit (l : Γ(W, ⊤)))
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E) K ↔
      sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj K) := by
  sorry

/-- The recorded tensor generator for ordinary integral scalar extension.
Source: Stacks 03EK (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purRawTensorSection (W : Scheme.{u}) (M : integralTowerModules l E W)
    (U : W.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) : ((integralOrdinaryScalar l E L ι W).obj M).val.obj U :=
  (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralCompletedScalarMap l E L ι W) M).presheaf).app U
        (a ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
          ((integralCompletedScalarMap l E L ι W).hom.app U).hom] x))

/-- Coefficient-model transport commutes with ordinary scalar tensor by the specified
balanced tensor map, on every generator.
Source: Stacks 03EK, Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: every finite projection identifies the scalar coefficient square. Thus its
completed square commutes. Send a tensor x to the same tensor with a transported
by the completed ring isomorphism. The inverse uses the inverse ring isomorphism.
Balancedness, restriction compatibility and the inverse identities hold on tensor
generators and descend through sheafification. Local generation proves uniqueness. -/
theorem purOrdinaryScalarModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pbcExtend (pbcScalarCoefficientMap l E L ι W) ⋙
        purOrdinaryCoefficientModel l L W ≅
      purOrdinaryCoefficientModel l E W ⋙ integralOrdinaryScalar l E L ι W,
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ) (a : (pbcAdicCompletion W (pbcIntegralDatum l L)).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (pbcTensorSection (pbcScalarCoefficientMap l E L ι W) M U a x) =
          purRawTensorSection l E L ι W ((purOrdinaryCoefficientModel l E W).obj M) U
            ((purCoefficientIso l L W).hom.hom.app U a) x := by
  sorry

/-- The ordinary scalar comparison, uniquely fixed on all tensor generators.
Source: Stacks 03EK (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purOrdinaryScalarModel (W : Scheme.{u}) :=
  (purOrdinaryScalarModel_existsUnique l E L ι W).exists.choose

/-- Termwise transport of the specified ordinary balanced tensor comparison.
Source: Stacks 06YY (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purScalarModelComplexIso (W : Scheme.{u}) :
    (pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ) ⋙
        (purOrdinaryCoefficientModel l L W).mapHomologicalComplex (.up ℤ) ≅
      (purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ) ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (purOrdinaryScalarModel l E L ι W) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := purOrdinaryCoefficientModel l E W)
      (G := integralOrdinaryScalar l E L ι W) (Iso.refl _) (.up ℤ)).symm

/-- Derived transport of the same scalar comparison, retaining the ordinary comparison
on every complex (finite-free scalar extension is exact).
Source: Stacks 06YY, 099N (blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: the model functors are exact identity-on-sections restrictions. Finite-free
scalar tensor is exact. On resolving complexes the universal derived tensor counit
is invertible, and the displayed conjugation of the ordinary tensor comparison
therefore gives the comparison. It descends through resolving quasi-isomorphisms.
Every object has a complex representative, so the result is invertible and unique. -/
theorem purScalarModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E L ι W ⋙ (purCoefficientModel l L W).functor ≅
        (purCoefficientModel l E W).functor ⋙ integralOrdinaryDerivedScalar l E L ι W,
      ∀ P : CochainComplex (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (integralOrdinaryDerivedScalar l E L ι W).map
            ((purOrdinaryCoefficientModel l E W).mapDerivedCategoryFactors.hom.app P) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            (((purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ)).obj P) =
        (purCoefficientModel l L W).functor.map
            (pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) P) ≫
          (purOrdinaryCoefficientModel l L W).mapDerivedCategoryFactors.hom.app
            (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((purScalarModelComplexIso l E L ι W).hom.app P) := by
  sorry

/-- The actual derived balanced-tensor comparison between the coefficient models.
Source: Stacks 06YY (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purScalarModel (W : Scheme.{u}) := (purScalarModel_existsUnique l E L ι W).exists.choose

end WeilConjectures
