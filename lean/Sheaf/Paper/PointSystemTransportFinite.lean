/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q10 and D4
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PointSystemTransportChain
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.PointSystemEvaluationComparisons
import all Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointAutomorphismRestrictionNatural
import Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism
import Sheaf.Paper.PointSystemTensorTransition
import Sheaf.Paper.PointRestrictionSectionTransformation

/-! # Finite point-transport recipe and evaluation comparisons

The finite coefficient, section, tensor and representative constructions used by
point-system transport. The existing declarations retain their signatures and data;
the ordinary restriction construction is accessed through its proved named API.
(blueprint: lem-trf-point-system-transport-finite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTransport

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The exact coefficient squares for quotient and completed coefficients.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-finite).
Proof: both quotient composites extend the same map on constant presheaves, and
sheafification preserves the equality. The completed map is the limit lift with
these finite components, so its projection equation is the defining limit equation. -/
theorem coefficient_squares (r n : ℕ) :
    inverseImageFiniteCoefficientMap l E (pointPower D r).hom (n + 1) ≫
        integralCoefficientSheafTransition l E (Spec (.of D.k)) n =
      (isoSectionwiseInverseImage (pointPower D r).hom RingCat.{max u (t + 1)}).map
          (integralCoefficientSheafTransition l E (Spec (.of D.k)) n) ≫
        inverseImageFiniteCoefficientMap l E (pointPower D r).hom n ∧
    inverseImageCompletedCoefficientMap l E (pointPower D r).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (pointPower D r).hom RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (pointPower D r).hom n := by
  exact ⟨PointRestrictionSystem.finite_comparison_naturality D l E
      (pointPower D r).hom n, by
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π,
      inverseImageCompletedCoefficientComponent]⟩

/-- The finite tensor-unit comparison is invertible on every unbounded complex.
Source: blueprint proof (3), step 2
(blueprint: lem-trf-point-system-transport-finite).
Proof: on local tensor generators define the inverse by x tensor a mapping to
c_n inverse(a) times x. Balancedness is the identity
b c_n inverse(a)x = c_n inverse(c_n(b)a)x. It commutes with restrictions and
sheafifies. The two composites are identity on x and on x tensor a, respectively.
Apply naturality to each differential; no flatness assumption is used. -/
@[instance] theorem finiteComparison_isIso (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    IsIso (inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K) := by
  exact inverseImageFiniteComparisonComplex_isIso l E (pointPower D r).hom n K

/-- The inverse comparison sends the local tensor generator x tensor a to c_n inverse(a)x.
Here a times j(x) is exactly the sheafified generator x tensor a.
Source: blueprint proof (3), step 2
(blueprint: lem-trf-point-system-transport-finite).
Proof: expand the inverse on generators from finiteComparison_isIso. The tensor
balancing relation carries c_n inverse(a)x tensor 1 to x tensor a, so this is the
inverse of j on every generator and thus on the sheafification. -/
theorem finiteComparison_inverse (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ) (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U))
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) :
    ((inv (inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K)).f i).val.app
        (op U)
        (a • ((inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K).f i).val.app
          (op U) x) =
      @SMul.smul _ ((K.X i).val.obj
        (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) inferInstance
        ((inv (inverseImageFiniteCoefficientMap l E (pointPower D r).hom n)).hom.app
          (op U) a) x := by
  let j := inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K
  have hs := (((inv j).f i).val.app (op U)).hom.map_smul a ((j.f i).val.app (op U) x)
  have hi := congrArg (fun f ↦ (f.f i).val.app (op U) x) (IsIso.hom_inv_id j)
  change ((inv j).f i).val.app (op U) ((j.f i).val.app (op U) x) = x at hi
  change _ = @SMul.smul _ ((K.X i).val.obj
    (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) inferInstance
      ((inv (inverseImageFiniteCoefficientMap l E (pointPower D r).hom n)).hom.app
        (op U) a) (((inv j).f i).val.app (op U) ((j.f i).val.app (op U) x)) at hs
  exact hs.trans (congrArg (fun y ↦
    @SMul.smul _ ((K.X i).val.obj
      (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) inferInstance
      ((inv (inverseImageFiniteCoefficientMap l E (pointPower D r).hom n)).hom.app
        (op U) a) y) hi)

/-- The actual quotient of constant integral scalars in the common universe.
Source: blueprint coefficient conventions (blueprint: lem-trf-point-system-transport-finite). -/
def quotient (n : ℕ) : pointRestrictionScalars.{t, u} l E none →+*
    pointRestrictionScalars.{t, u} l E (some n) :=
  RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

attribute [local irreducible] quotient

/-- Additivity of the recorded finite inverse image, exposed at its finite-module interface.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-finite). -/
instance finitePullAdditive {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (inverseImageFiniteModules.{t, u} l E g n).Additive :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).1

/-- Left exactness of the recorded finite inverse image.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-finite). -/
instance finitePullLimits {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    PreservesFiniteLimits (inverseImageFiniteModules.{t, u} l E g n) :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).2.1

/-- Right exactness of the recorded finite inverse image.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-finite). -/
instance finitePullColimits {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    PreservesFiniteColimits (inverseImageFiniteModules.{t, u} l E g n) :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).2.2

/-- The recorded tensor pullback, with both finite-module endpoints explicit.
Source: def-weil-inverse-image-pullback-comparison (a)
(blueprint: lem-trf-point-system-transport-finite). -/
def tensorPull (r n : ℕ) : integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
    integralOperationsFiniteModules l E (Spec (.of D.k)) n :=
  integralOperationsLevelPullback.{t, u} l E (pointPower D r).hom n

/-- Additivity of that recorded tensor pullback.
Source: Stacks 03D2 (blueprint: lem-trf-point-system-transport-finite). -/
instance tensorPullAdditive (r n : ℕ) : (tensorPull D l E r n).Additive :=
  integralOperationsLevelPullback_additive l E (pointPower D r).hom n

/-- Left exactness of that recorded tensor pullback.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-finite). -/
instance tensorPullLimits (r n : ℕ) : PreservesFiniteLimits (tensorPull D l E r n) :=
  (inverseImageFinitePullback_exact l E (pointPower D r).hom n).1

/-- Right exactness of that recorded tensor pullback.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-finite). -/
instance tensorPullColimits (r n : ℕ) : PreservesFiniteColimits (tensorPull D l E r n) :=
  (inverseImageFinitePullback_exact l E (pointPower D r).hom n).2

/-- The unchanged finite coefficient sections, followed by the actual R→A_n restriction.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-finite). -/
def finiteRSections (n : ℕ) :
    integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none) :=
  pointRestrictionSections l E D.k (some n) ⋙
    ModuleCat.restrictScalars (quotient.{t, u} l E n)


private theorem restrictScalars_finiteExact {R S : Type v} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have h (X : ShortComplex (ModuleCat.{v} S)) (hx : X.Exact) :
      (X.map (ModuleCat.restrictScalars.{v} f)).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hx ⊢
    exact hx
  exact ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp h

/-- Finite R-sections are additive and exact with independent site/coefficient sizes.
Source: Stacks 0946, 015F (blueprint: lem-trf-point-system-transport-finite).
Proof: finite point sections are exact by lem-weil-point-proetale-sections-exact;
restriction of scalars keeps the kernel and cokernel of the underlying abelian groups.
The scalar map is the quotient homomorphism, so it does not impose flatness. -/
theorem finiteRSections_exact (n : ℕ) : (finiteRSections D l E n).Additive ∧
    PreservesFiniteLimits (finiteRSections D l E n) ∧
    PreservesFiniteColimits (finiteRSections D l E n) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have := (restriction_sections_exact l E D.k (some n)).1
  have := (restriction_sections_exact l E D.k (some n)).2
  let T := ModuleCat.restrictScalars.{max u (t + 1)} (quotient.{t, u} l E n)
  have hT := restrictScalars_finiteExact (quotient.{t, u} l E n)
  have : PreservesFiniteLimits T := hT.1
  have : PreservesFiniteColimits T := hT.2
  constructor
  · constructor
    intro M N f g
    ext x
    rfl
  · constructor
    · exact comp_preservesFiniteLimits (pointRestrictionSections l E D.k (some n)) T
    · exact comp_preservesFiniteColimits (pointRestrictionSections l E D.k (some n)) T

/-- Additivity from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-finite). -/
instance finiteRSectionsAdditive (n : ℕ) : (finiteRSections D l E n).Additive :=
  (finiteRSections_exact D l E n).1

/-- Left exactness from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-finite). -/
instance finiteRSectionsLimits (n : ℕ) : PreservesFiniteLimits (finiteRSections D l E n) :=
  (finiteRSections_exact D l E n).2.1

/-- Right exactness from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-finite). -/
instance finiteRSectionsColimits (n : ℕ) : PreservesFiniteColimits (finiteRSections D l E n) :=
  (finiteRSections_exact D l E n).2.2

/-- Additivity at the finite coefficient point-section interface.
Source: Stacks 03CW (blueprint: lem-trf-point-system-transport-finite). -/
instance finiteSectionsAdditive (n : ℕ) :
    (pointRestrictionSections l E D.k (some n)).Additive :=
  pointRestrictionSectionsAdditive l E D.k (some n)

private theorem normalized_chainMap_existsUnique
    {C : Type*} [Category* C] [HasZeroMorphisms C] {R : Type*} [Ring R]
    {F G : C ⥤ ModuleCat R} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (σ : F ⟶ G) (K : CochainComplex C ℤ) :
    ∃! τ : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj K,
      ∀ (i : ℤ) (x : F.obj (K.X i)), τ.f i x = σ.app (K.X i) x := by
  refine ⟨(NatTrans.mapHomologicalComplex σ (.up ℤ)).app K, fun _ _ ↦ rfl, ?_⟩
  intro τ hτ
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hτ i x

/-- The A_n-linear finite sigma, with precisely the restriction/insertion values.
Source: blueprint proof (3), step 1
(blueprint: lem-trf-point-system-transport-finite).
Proof: use the restriction construction of lem-weil-point-automorphism-restriction-natural
for h^r at some n; its coefficient normalization does not use l ≠ D.p.
The constant-section normalization makes restriction A_n-linear for the transported target
action. Apply module naturality to the differentials. Component values determine
the chain map uniquely. -/
theorem finiteSigma_existsUnique (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! σ : ((pointRestrictionSections l E D.k (some n)).mapHomologicalComplex
        (.up ℤ)).obj K ⟶
      ((pointRestrictionInverseImage.{t, u} l E (pointPower D r).hom (some n) ⋙
        pointRestrictionSections l E D.k (some n)).mapHomologicalComplex (.up ℤ)).obj K,
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        σ.f i x = pointRestrictionRaw l E (pointPower D r).hom (some n) (K.X i) x := by
  obtain ⟨σ, hσ, _⟩ := pointRestrictionSectionTransformation_existsUnique
    l E D.k (pointPower D r).hom (some n)
  obtain ⟨τ, hτ, huni⟩ := normalized_chainMap_existsUnique σ K
  refine ⟨τ, fun i x ↦ (hτ i x).trans (hσ (K.X i) x), ?_⟩
  intro τ' hτ'
  apply huni τ'
  intro i x
  exact (hτ' i x).trans (hσ (K.X i) x).symm


/-- The finite sigma as an A_n-linear chain map, before restricting to R.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-finite). -/
def finiteSigma (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
  (finiteSigma_existsUnique D l E r n K).exists.choose


/-- The identical finite map with its scalars restricted by R→A_n.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-finite). -/
def finiteSigmaR (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
        finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  ((ModuleCat.restrictScalars.{max u (t + 1)} (quotient.{t, u} l E n)).mapHomologicalComplex
      (.up ℤ)).map (finiteSigma D l E r n K)

/-- The dependency's comparison with its complex endpoints stated explicitly.
Source: def-weil-inverse-image-pullback-comparison (a)
(blueprint: lem-trf-point-system-transport-finite). -/
def comparisonComplex (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n).mapHomologicalComplex
      (.up ℤ)).obj K ⟶ ((tensorPull D l E r n).mapHomologicalComplex (.up ℤ)).obj K :=
  inverseImageFiniteComparisonComplex.{t, u} l E (pointPower D r).hom n K

/-- Map a comparison of finite complexes through sections, using the standard
composition isomorphisms rather than unfolding the tensor model.
Source: blueprint proof (3), steps 2 and 7
(blueprint: lem-trf-point-system-transport-finite). -/
def mapFiniteComplexComparison (n : ℕ)
    (F G : integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
      integralOperationsFiniteModules l E (Spec (.of D.k)) n)
    [F.Additive] [G.Additive]
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (j : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj K) :
    ((F ⋙ finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((G ⋙ finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (F ⋙ finiteRSections D l E n)) (.up ℤ)).inv.app K ≫
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).map j ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (G ⋙ finiteRSections D l E n)) (.up ℤ)).hom.app K

/-- The finite point-transport recipe on any representative: restriction, inverse-image
insertion and sheafification, followed by the sheafified tensor insertion j.
Source: def-weil-frobenius-point-transport with h^r replacing h, blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-finite). -/
def finiteTransportComplex (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((tensorPull D l E r n ⋙
        finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  finiteSigmaR D l E r n K ≫
    mapFiniteComplexComparison D l E n
      (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n)
      (tensorPull D l E r n) K (comparisonComplex D l E r n K)


/-- The tensor-model nth term, still a sheaf of completed-coefficient modules.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-finite). -/
def tensorLevel (r n : ℕ) : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    scalarReductionSource l E (Spec (.of D.k)) :=
  coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
    tensorPull D l E r n ⋙
      scalarReductionRestriction l E (Spec (.of D.k)) n


/-- The actual sheafified tensor insertion x↦x tensor 1 at any site object.
Source: def-weil-inverse-image-pullback-comparison (a), blueprint proof (3)
(blueprint: lem-trf-point-system-transport-finite). -/
def insertion (r n : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M).val.obj
      (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) :=
  (((tensorPull D l E r n).obj
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
    (proEtaleIsoCommaArrow (pointPower D r).hom U).op)
      (integralOperationsPullbackGenerator l E (pointPower D r).hom n
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
        ((proEtaleIsoPostcompose (pointPower D r).hom).obj U) x)


/-- The tensor transition is fixed on all local generators, including their scalar a.
For a=1 the formula is exactly v_n(x) tensor rho_n(1)=v_n(x) tensor 1.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-finite).
Proof: inverse-image the actual horizontal restriction of M, extend scalars by
rho_n, then sheafify. coefficient_squares makes the formula balanced and linear
after completed scalar restriction. On x tensor a it has precisely the displayed
value. It commutes with restrictions and module morphisms, and hence gives a natural
transformation. The local tensor generators generate the sheafified tensor product;
completed projections are locally surjective, so completed linearity and the formula
on all a prove uniqueness. This uses the original transitions of M, not derived
reduction isomorphisms or cartesianness. -/
theorem tensorTransition_existsUnique (r n : ℕ) :
    ∃! τ : tensorLevel D l E r (n + 1) ⟶ tensorLevel D l E r n,
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k)))
        (U : (Spec (.of D.k)).ProEt)
        (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U))
        (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M).val.obj
          (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))),
        (τ.app M).val.app (op U)
            (@SMul.smul _
              (((tensorPull D l E r (n + 1)).obj
                ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
                  (op U)) inferInstance a (insertion D l E r (n + 1) M U x)) =
          @SMul.smul _
            (((tensorPull D l E r n).obj
              ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
            inferInstance
            ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op U) a)
            (insertion D l E r n M U
              ((M.val.presheaf.map
                (Prod.mkHom (homOfLE (Nat.le_succ n))
                  (𝟙 ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))).op) x)) := by
  exact PointSystemTensorTransition.tensor_transition_existsUnique D l E (pointPower D r).hom n


/-- The ordinary nth evaluation on whole integral-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-transport-finite). -/
abbrev towerEvaluation (n : ℕ) :=
  (evaluation ℕᵒᵖ (ModuleCat.{max u (t + 1)}
    (pointRestrictionScalars.{t, u} l E none))).obj (op n)

/-- Canonical evaluation comparisons are identity on all underlying sections.
Source: blueprint proof (3), steps 3--4 and 7
(blueprint: lem-trf-point-system-transport-finite).
Proof: restricting through the completion and then through R has the quotient
R→A_n action, by the completed projection equation. The sequence reindexing is
(n,U)↦(n,h^r U), with action c_n inverse, exactly the finite inverse image. Thus
identity on the section carriers is linear, natural and inverse to itself on both
sides. Equality on every section proves uniqueness of the pair of comparisons. -/
theorem evaluation_existsUnique (r n : ℕ) :
    ∃! e :
      (sections D l E ⋙ towerEvaluation.{t, u} l E n ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ finiteRSections D l E n) ×
      ((pull D l E r ⋙ sections D l E) ⋙ towerEvaluation.{t, u} l E n ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
          (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙ finiteRSections D l E n)),
      ∀ M : coefficientSequenceModules l E (Spec (.of D.k)),
        HEq (fun x : ((sections D l E).obj M).obj (op n) ↦ e.1.hom.app M x)
          (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦ x) ∧
        HEq (fun x : ((sections D l E).obj ((pull D l E r).obj M)).obj (op n) ↦
            e.2.hom.app M x)
          (fun x : M.val.obj (op (n,
            (proEtaleIsoPostcompose (pointPower D r).hom).obj
              (ProEt.mk (𝟙 (Spec (.of D.k)))))) ↦ x) := by
  unfold finiteRSections quotient
  exact PointSystemEvaluation.evaluation_existsUnique D l E (pointPower D r).hom n

/-- Evaluation comparisons chosen by their unique identity-on-sections normalization.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-finite). -/
def evaluationComparisons (r n : ℕ) := (evaluation_existsUnique D l E r n).exists.choose

/-- Evaluate the source derived whole-tower functor, using the exact ordinary comparison.
Source: Stacks 015F, blueprint proof (3)
(blueprint: lem-trf-point-system-transport-finite). -/
def sourceEvaluation (r n : ℕ) :
    derivedSections D l E ⋙ (towerEvaluation.{t, u} l E n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙
        (finiteRSections D l E n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (sections D l E) (towerEvaluation.{t, u} l E n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (evaluationComparisons D l E r n).1 ≪≫
      Functor.mapDerivedCategoryCompIso
        (coefficientSequenceEvaluation l E (Spec (.of D.k)) n) (finiteRSections D l E n)


/-- Evaluate the target derived whole-tower functor, using its normalized comparison.
Source: Stacks 015F, blueprint proof (3)
(blueprint: lem-trf-point-system-transport-finite). -/
def targetEvaluation (r n : ℕ) :
    transportedDerivedSections D l E r ⋙
        (towerEvaluation.{t, u} l E n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙
        (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
          finiteRSections D l E n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (pull D l E r ⋙ sections D l E)
    (towerEvaluation.{t, u} l E n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (evaluationComparisons D l E r n).2 ≪≫
        Functor.mapDerivedCategoryCompIso
          (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
          (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙ finiteRSections D l E n)


/-- The finite j comparison on an arbitrary derived coefficient object, transported
through the localization's chosen representative. It is the same sheafified tensor-unit
comparison, evaluated after R-scalar restriction.
Source: blueprint proof (3), steps 2 and 7
(blueprint: lem-trf-point-system-transport-finite). -/
def finiteDerivedComparison (r n : ℕ)
    (C : normalizedDVRDerived l E (Spec (.of D.k)) n) :
    (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategory.obj C ⟶
        (tensorPull D l E r n ⋙
          finiteRSections D l E n).mapDerivedCategory.obj C :=
  (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
    finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).inv ≫
    (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.hom.app
        (DerivedCategory.Q.objPreimage C) ≫
    DerivedCategory.Q.map
      (mapFiniteComplexComparison D l E n
        (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n)
        (tensorPull D l E r n) (DerivedCategory.Q.objPreimage C)
        (comparisonComplex D l E r n (DerivedCategory.Q.objPreimage C))) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage C) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).hom


/-- The finite point-transport recipe with h replaced by h^r, using exactly sigma
followed by Gamma(j), and the canonical localization representative comparisons.
At r=1 this is the coefficient-sized presentation of def-weil-frobenius-point-transport;
no separate choice of a fiber identification is made.
Source: blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-finite). -/
def finiteTransportDerived (r n : ℕ)
    (C : normalizedDVRDerived l E (Spec (.of D.k)) n) :
    (finiteRSections D l E n).mapDerivedCategory.obj C ⟶
      (tensorPull D l E r n ⋙
        finiteRSections D l E n).mapDerivedCategory.obj C :=
  (finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).inv ≫
    (finiteRSections D l E n).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage C) ≫
    DerivedCategory.Q.map (finiteTransportComplex D l E r n (DerivedCategory.Q.objPreimage C)) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage C) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).hom


end WeilConjectures.PointSystemTransport
