module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.Projective
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.Paper.CompletedPerfectScalarPullback
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Topology.LocallyConstant.Algebra
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Paper.SfBcAdicRingDomain
import all Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import all Sheaf.Paper.CompletedPerfectScalarPullback
import all Sheaf.Paper.IntegralReductionTowerUnrestricted
import all Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-! # Adic scalar data and normalized flat reduction models

Source: Stacks Tags 093M, 06YQ, 0G7E and 05V4; Bhatt--Scholze, Lemma 6.5.9
and Proposition 6.6.11 (blueprint: lem-a1-adic-scalar-flat-reduction-model).

We reuse the published scalar-model constructions, not their pullback theorem.
The integer n denotes the positive exponent n+1. Locally constant functions on
connected components mean continuous functions to the discrete finite coefficient ring.
The source scheme and coefficient universes are independent; the explicit ULift only
places the scalar modules in a universe containing the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
open WeilConjectures.CompletedPerfectScalar

namespace WeilConjectures.AdicScalarFlatReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{t})

/-- The exact augmented free resolution, with its two free copies of R placed in
chain degrees -1 and 0, and annihilation by a power of l. Source: Stacks algebra,
Tags 00NX and 05CF (blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def ScalarResolution : Prop :=
  ∀ n : ℕ,
    Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
    (∀ x : Padic.coefficientExtensionRing l E (n + 1), (l ^ (n + 1)) • x = 0) ∧
    Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
    Function.Exact
      (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
    Function.Surjective (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

/-- The scalar finite sheaves identified with the datum's continuous functions on
connected components, preserving constants, restrictions and consecutive quotients.
Source: Bhatt--Scholze 4.2.12 and Stacks 093J
(blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
structure FiniteCoefficients where
  sections : ∀ (n : ℕ) (U : T.ProEtᵒᵖ),
    ((integralCoefficientCommRingSheaf l E T n).obj.obj U) ≃+*
      LocallyConstant (ConnectedComponents U.unop.left)
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  constants : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (c : ConnectedComponents U.unop.left),
    sections n U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
        U a) c = a
  restriction : ∀ (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (c : ConnectedComponents V.unop.left),
    sections n V ((integralCoefficientCommRingSheaf l E T n).obj.map f a) c =
      sections n U a (f.unop.left.continuous.connectedComponentsMap c)
  transition : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T (n + 1)).obj.obj U)
    (c : ConnectedComponents U.unop.left),
    sections n U ((integralCoefficientSheafTransition l E T n).hom.app U a) c =
      ULift.up (Padic.coefficientExtensionTransition l E (n + 1)
        (sections (n + 1) U a c).down)
  completed : ∀ (U : T.ProEtᵒᵖ)
    (a : ∀ n : ℕ, (integralCoefficientCommRingSheaf l E T n).obj.obj U),
    (∀ n : ℕ, (integralCoefficientSheafTransition l E T n).hom.app U (a (n + 1)) = a n) →
      ∃! b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U,
        ∀ n : ℕ, (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b = a n

/-- Functoriality on local scalar generators. In particular the last equality remains
valid when the scalar is the image under any consecutive quotient map, which is
precisely coefficient-transition compatibility of the degreewise splitting maps.
Source: Stacks 03EK (blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def MapFormula
    {V W : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)} (f : V ⟶ W) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (x : V),
    ((constant T (Scalars.{t, u} l E)).map f).val.app U
      (constantSection l E T V U x) = constantSection l E T W U (f x)) ∧
  (∀ (U : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj V).val.obj U),
    ((modelModules l E T).map f).val.app U (modelSection l E T V U b x) =
      modelSection l E T W U b (((constant T (Scalars.{t, u} l E)).map f).val.app U x)) ∧
  (∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj V).val.obj U),
    ((finiteChange l E T n).E.map ((constant T (Scalars.{t, u} l E)).map f)).val.app U
      (finiteSection l E T n V U a x) =
      finiteSection l E T n W U a
        (((constant T (Scalars.{t, u} l E)).map f).val.app U x))

/-- Degreewise finite-free splittings, retained by constants and by both scalar
extensions. No assertion that i and s commute with the scalar differential is made.
Source: Stacks 00NX and 05CF (blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def Splittings (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) : Prop :=
  ∀ j : ℤ, ∃ (m : ℕ)
    (i : P.X j ⟶ ModuleCat.of (Scalars.{t, u} l E) (Fin m → Scalars.{t, u} l E))
    (s : ModuleCat.of (Scalars.{t, u} l E) (Fin m → Scalars.{t, u} l E) ⟶ P.X j),
    i ≫ s = 𝟙 (P.X j) ∧
    (constant T (Scalars.{t, u} l E)).map i ≫
      (constant T (Scalars.{t, u} l E)).map s =
        𝟙 ((constant T (Scalars.{t, u} l E)).obj (P.X j)) ∧
    (modelModules l E T).map i ≫ (modelModules l E T).map s =
      𝟙 ((modelModules l E T).obj (P.X j)) ∧
    (∀ n : ℕ,
      (finiteChange l E T n).E.map ((constant T (Scalars.{t, u} l E)).map i) ≫
        (finiteChange l E T n).E.map ((constant T (Scalars.{t, u} l E)).map s) =
          𝟙 ((finiteChange l E T n).E.obj
            ((constant T (Scalars.{t, u} l E)).obj (P.X j)))) ∧
    MapFormula l E T i ∧ MapFormula l E T s

/-- The inverse balancing formula on every local section of the constant term.
Source: Stacks 05V4 (blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def InverseFormula (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (r : Reductions l E T P) : Prop :=
  ∀ (n : ℕ) (j : ℤ) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj (P.X j)).val.obj U),
    ((r n).inv.f j).val.app U (finiteSection l E T n (P.X j) U a x) =
      unrestrictedIntegralTensorSection l E T n (((model l E T).obj P).X j) U a
        (modelSection l E T (P.X j) U 1 x)

/-- Compatibility with the actual ordinary reduction unit x ↦ x tensor 1.
Its composite is exactly the quotient augmentation, without a chosen splitting.
Source: Stacks 05V4 and 06YY (blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def UnitFormula (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (r : Reductions l E T P) : Prop :=
  ∀ (n : ℕ) (j : ℤ) (U : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj (P.X j)).val.obj U),
    ((r n).hom.f j).val.app U
      (((unrestrictedTowerUnit l E T ((model l E T).obj P) n).f j).val.app U
        (modelSection l E T (P.X j) U b x)) =
      finiteSection l E T n (P.X j) U
        ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b) x

/-- The coefficient verification and the canonical family of chain and derived
comparisons. All scalar-model terms and differentials are the existing constructions.
The derived comparisons (derivedReductionIso, the K-flat counit followed by the
balancing chain isomorphism) are natural in scalar chain maps.
Source: Stacks 093M, 06YQ, 0G7E, 05V4 and 06YY
(blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
structure Data where
  datum : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)
  datumIdeal : datum.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}
  resolutions : ScalarResolution l E
  coefficients : FiniteCoefficients l E T
  reductions : ModelReductions l E T
  constantFlat : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E), IsModel l E P →
    ∀ j : ℤ,
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := constantRing T (Scalars.{t, u} l E))
      ((constant T (Scalars.{t, u} l E)).obj (P.X j))
  bounded : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E), IsModel l E P →
    ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (((model l E T).obj P).X j)
  kflat : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E), IsModel l E P →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) ((model l E T).obj P)
  termFlat : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E), IsModel l E P →
    ∀ j : ℤ,
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E T)
      (((model l E T).obj P).X j)
  splittings : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E), IsModel l E P →
    Splittings l E T P
  inverseFormula : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P),
    InverseFormula l E T P (reductions.reduction P hP)
  unitFormula : ∀ (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P),
    UnitFormula l E T P (reductions.reduction P hP)
  independent : ∀ (r : ModelReductions l E T)
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P) (n : ℕ),
    r.reduction P hP n = reductions.reduction P hP n
  derivedNatural : ∀ (P Q : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P) (hQ : IsModel l E Q) (f : P ⟶ Q) (n : ℕ),
    (scalarReductionDerivedExtension l E T n).map ((derivedModel l E T).map f) ≫
        (derivedReductionIso l E T Q hQ (reductions.reduction Q hQ) n).hom =
      (derivedReductionIso l E T P hP (reductions.reduction P hP) n).hom ≫
        DerivedCategory.Q.map ((finiteModel l E T n).map f)

/-- The derived comparison is the recorded K-flat computation counit on the identity
resolution, followed by the localization of the specified balancing chain isomorphism.
This definition uses no degreewise splitting and fixes the derived map, not just its
isomorphism class. Source: Stacks 06YY and 05V4
(blueprint: lem-a1-adic-scalar-flat-reduction-model). -/
def derivedComparison (d : Data l E T)
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P) (n : ℕ) :
    (scalarReductionDerivedExtension l E T n).obj ((derivedModel l E T).obj P) ≅
      DerivedCategory.Q.obj ((finiteModel l E T n).obj P) :=
  derivedReductionIso l E T P hP (d.reductions.reduction P hP) n


local instance : (ProEt.topology T).HasSheafCompose
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) := inferInstance

private def ctPresheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj V := CommRingCat.of C(V.unop.left, A)
  map h := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def ctUnit (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ ctPresheaf X A where
  app V := CommRingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem ctPresheaf_isSheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (ctPresheaf X A) := by
  let : ReflectsLimitsOfSize.{t, t + 1}
      (CategoryTheory.forget CommRingCat.{max u (t + 1)}) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _
    (CategoryTheory.forget CommRingCat.{max u (t + 1)})
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem ctUnit_locallyInjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (ctUnit X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem ctUnit_locallySurjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (ctUnit X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm

private def ctSheafMap (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj (CommRingCat.of A) ⟶
      ⟨ctPresheaf X A, ctPresheaf_isSheaf X A⟩ :=
  ⟨sheafifyLift (ProEt.topology X) (ctUnit X A) (ctPresheaf_isSheaf X A)⟩

private theorem ctSheafMap_iso (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] : IsIso (ctSheafMap X A) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : (ProEt.topology X).WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, max u (t + 1),
      t + 1, max u (t + 1) + 1, max u (t + 1)} _
  let := ctUnit_locallyInjective X A
  let := ctUnit_locallySurjective X A
  refine (Sheaf.isLocallyBijective_iff_isIso (ctSheafMap X A)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology X) _)]
    change Presheaf.IsLocallyInjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology X) _)]
    change Presheaf.IsLocallySurjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance

private def componentEquiv (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    C(X, A) ≃+* LocallyConstant (ConnectedComponents X) A where
  toFun f := ⟨f.continuous.connectedComponentsLift,
    (IsLocallyConstant.iff_continuous _).2 f.continuous.connectedComponentsLift_continuous⟩
  invFun f := f.toContinuousMap.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  left_inv f := by ext x; rfl
  right_inv f := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_mul' f g := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_add' f g := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

private def ctSections (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (U : X.ProEtᵒᵖ) :
    ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of A)).obj.obj U ≃+* LocallyConstant (ConnectedComponents U.unop.left) A :=
  let := ctSheafMap_iso X A
  (((sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).mapIso
    (asIso (ctSheafMap X A))).app U).commRingCatIsoToRingEquiv.trans
      (componentEquiv U.unop.left A)

private def ctPost (X : Scheme.{t})
    {A B : Type (max u (t + 1))} [CommRing A] [CommRing B]
    [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
    (φ : A →+* B) : ctPresheaf X A ⟶ ctPresheaf X B where
  app U := CommRingCat.ofHom (φ.compLeftContinuous U.unop.left continuous_of_discreteTopology)
  naturality _ _ _ := by rfl

private theorem ctPost_natural (X : Scheme.{t})
    {A B : Type (max u (t + 1))} [CommRing A] [CommRing B]
    [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
    (φ : A →+* B) :
    ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom φ)).hom ≫ (ctSheafMap X B).hom =
        (ctSheafMap X A).hom ≫ ctPost X φ := by
  apply sheafify_hom_ext _ _ _ (ctPresheaf_isSheaf X B)
  change toSheafify _ _ ≫ sheafifyMap _ _ ≫ _ = _
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, ctSheafMap, toSheafify_sheafifyLift,
    toSheafify_sheafifyLift_assoc]
  ext U a
  rfl

private theorem completed_sections (U : T.ProEtᵒᵖ)
    (a : ∀ n : ℕ, (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (ha : ∀ n, (integralCoefficientSheafTransition l E T n).hom.app U (a (n + 1)) = a n) :
    ∃! b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U,
      ∀ n, (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b = a n := by
  let D := integralCoefficientSheafSystem l E T
  let ev := sheafToPresheaf (ProEt.topology T) RingCat.{max u (t + 1)} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U ⋙
      CategoryTheory.forget RingCat.{max u (t + 1)}
  let γ : (CategoryTheory.Functor.const ℕᵒᵖ).obj PUnit ⟶ D ⋙ ev :=
    NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ a n) (by
      intro n
      ext x
      dsimp only [Functor.const_obj_map, types_comp_apply, Functor.comp_map]
      change a n = ((integralCoefficientSheafSystem l E T).map
        (homOfLE (Nat.le_succ n)).op).hom.app U (a (n + 1))
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (ha n).symm)
  let hc := isLimitOfPreserves ev (limit.isLimit D)
  let x : (D ⋙ ev).sections := ⟨fun j ↦ γ.app j PUnit.unit, fun f ↦ by
    exact (ConcreteCategory.congr_hom (γ.naturality f) PUnit.unit).symm⟩
  let b := (Types.isLimitEquivSections hc).symm x
  have hb (n : ℕ) :
      (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b = a n := by
    have h := Types.isLimitEquivSections_symm_apply hc x (op n)
    change (ev.map (limit.π D (op n))) b = a n
    exact h
  refine ⟨b, hb, ?_⟩
  intro c hc'
  apply Concrete.isLimit_ext (D ⋙ ev) hc c b
  intro j
  change (completedIntegralCommRingProjectionUnrestricted l E T j.unop).hom.app U c =
    (completedIntegralCommRingProjectionUnrestricted l E T j.unop).hom.app U b
  exact (hc' j.unop).trans (hb j.unop).symm

private theorem finite_coefficients : Nonempty (FiniteCoefficients l E T) := by
  let A (n : ℕ) := ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let top (n : ℕ) : TopologicalSpace (A n) := ⊥
  let disc (n : ℕ) : DiscreteTopology (A n) := ⟨rfl⟩
  refine ⟨{ sections := fun n U ↦ ctSections T (A n) U
            constants := ?_
            restriction := ?_
            transition := ?_
            completed := completed_sections l E T }⟩
  · intro n U a c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg (fun k ↦ (k.app U a : C(U.unop.left, A n)) x)
      (toSheafify_sheafifyLift (ProEt.topology T) (ctUnit T (A n))
        (ctPresheaf_isSheaf T (A n)))
  · intro n U V f a c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg (fun k ↦ (k a : C(V.unop.left, A n)) x)
      (congrArg (fun k ↦ k.hom) ((ctSheafMap T (A n)).hom.naturality f))
  · intro n U a c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg (fun k ↦ (k.app U a : C(U.unop.left, A n)) x)
      (ctPost_natural T (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1))))

section SiteBalancing
universe a b r
variable {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

private abbrev Mods (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

private abbrev res {R S : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) := SheafOfModules.restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

private theorem normalizedTensor_smul {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (M : Mods J R)
    (N : Mods J S)
    (h : N = SheafOfModules.changeOfRings φ M)
    (U : Cᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s • (eqToHom h.symm).val.app U
        ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{r}
    (R := (sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{b, a, r} φ M)).app U
  let e := eqToHom h.symm
  change e.val.app U (η ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom s z x
  have hη := η.hom.map_smul s (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul s
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)


private def resCompIso {R S V : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (ψ : S ⟶ V) :
    res J (φ ≫ ψ) ≅ res J ψ ⋙ res J φ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
private theorem balance_from_adjunctions {R S V : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (hχ : φ ≫ ψ = χ)
    (E1 : Mods J R ⥤ Mods J S)
    (τ1 : ∀ (M : Mods J R) (U : Cᵒᵖ),
      S.obj.obj U → M.val.obj U → (E1.obj M).val.obj U)
    (a1 : E1 ⊣ res J φ)
    (h1 : ∀ (M : Mods J R) (N : Mods J S)
      (f : E1.obj M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
      (a1.homEquiv M N f).val.app U x = f.val.app U (τ1 M U 1 x))
    (hs1 : ∀ (M : Mods J R) (U : Cᵒᵖ) (s z : S.obj.obj U)
      (x : M.val.obj U), τ1 M U (s * z) x = s • τ1 M U z x)
    (E2 : Mods J S ⥤ Mods J V)
    (τ2 : ∀ (M : Mods J S) (U : Cᵒᵖ),
      V.obj.obj U → M.val.obj U → (E2.obj M).val.obj U)
    (a2 : E2 ⊣ res J ψ)
    (h2 : ∀ (M : Mods J S) (N : Mods J V)
      (f : E2.obj M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
      (a2.homEquiv M N f).val.app U x = f.val.app U (τ2 M U 1 x))
    (hs2 : ∀ (M : Mods J S) (U : Cᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ2 M U (s * z) x = s • τ2 M U z x)
    (E3 : Mods J R ⥤ Mods J V)
    (τ3 : ∀ (M : Mods J R) (U : Cᵒᵖ),
      V.obj.obj U → M.val.obj U → (E3.obj M).val.obj U)
    (a3 : E3 ⊣ res J χ)
    (h3 : ∀ (M : Mods J R) (N : Mods J V)
      (f : E3.obj M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
      (a3.homEquiv M N f).val.app U x = f.val.app U (τ3 M U 1 x))
    (hs3 : ∀ (M : Mods J R) (U : Cᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ3 M U (s * z) x = s • τ3 M U z x)
    : ∃ e : E1 ⋙ E2 ≅ E3,
      ∀ (M : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
        (U : Cᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (τ2 _ U s (τ1 _ U z x)) =
          τ3 _ U (s * ψ.hom.app U z) x := by
  subst χ
  let a := (a1.comp a2).ofNatIsoRight (resCompIso J φ ψ).symm
  let e := a.leftAdjointUniq a3
  have hcomp (M : Mods J R)
      (N : Mods J V)
      (f : ((E1) ⋙ E2).obj M ⟶ N)
      (U : Cᵒᵖ) (x : M.val.obj U) :
      (a.homEquiv M N f).val.app U x =
        f.val.app U (τ2 _ U 1
          (τ1 M U 1 x)) := by
    dsimp only [a]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change (a1.homEquiv M _ (a2.homEquiv _ N f)).val.app U x = _
    exact (h1 M _ (a2.homEquiv _ N f) U x).trans
      (h2 _ N f U (τ1 M U 1 x))
  clear_value a
  have hunit (M : Mods J R)
      (U : Cᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U 1
        (τ1 M U 1 x)) =
      τ3 M U 1 x := by
    have he := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a a3 M)
    rw [hcomp] at he
    rw [← a3.homEquiv_id M, h3] at he
    exact he
  clear_value e
  have hformula (M : Mods J R)
      (U : Cᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U s
        (τ1 M U z x)) =
      τ3 M U (s * ψ.hom.app U z) x := by
    have hz := hs1 M U z 1 x
    rw [mul_one] at hz
    have hs := hs2 ((E1).obj M) U s 1
      (τ1 M U z x)
    rw [mul_one] at hs
    erw [hs, map_smul, ← h2, hz, map_smul]
    change s • (ψ.hom.app U z •
      (show (E3.obj M).val.obj U from
        (a2.homEquiv _ _ (e.hom.app M)).val.app U (τ1 M U 1 x))) = _
    erw [h2, hunit, ← mul_smul]
    have ht := hs3 M U (s * ψ.hom.app U z) 1 x
    simpa only [mul_one] using ht.symm
  exact ⟨e, hformula⟩

private def normTensor
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤
      SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (ho : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (M : Mods J R)
    (U : Cᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (eqToHom (ho M).symm).val.app U
    (SheafOfModules.UnrestrictedTowerProof.tensorSection φ M U a x)

private theorem normAdjunction
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤
      SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (hadd : F.Additive)
    (ho : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (ho N).symm) :
    ∃ a : F ⊣ res J φ,
      ∀ (M : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
        (N : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
        (f : F.obj M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
        (a.homEquiv M N f).val.app U x = f.val.app U (normTensor J φ F ho M U 1 x) := by
  let := hadd
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, hn⟩ := ha F ho hm
  refine ⟨a, ?_⟩
  intro M N f U x
  have he := hn M N (eqToHom (ho M).symm ≫ f) U x
  have hh : eqToHom (ho M) ≫ (eqToHom (ho M).symm ≫ f) = f := by simp
  rw [hh] at he
  simpa only [normTensor, SheafOfModules.UnrestrictedTowerProof.tensorSection,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using he

private theorem normalized_map_formula
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤
      SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (ho : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (ho N).symm)
    {M N : SheafOfModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)}
    (f : M ⟶ N) (U : Cᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (F.map f).val.app U
      ((eqToHom (ho M).symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection φ M U a x)) =
      (eqToHom (ho N).symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection φ N U a (f.val.app U x)) := by
  rw [hm]
  change ((eqToHom (ho N).symm).val.app U)
    ((SheafOfModules.changeOfRingsHom φ M f).val.app U
      (((eqToHom (ho M)).val.app U)
        ((eqToHom (ho M).symm).val.app U _))) = _
  have he (z : (SheafOfModules.changeOfRings φ M).val.obj U) :
      ((eqToHom (ho M)).val.app U)
      ((eqToHom (ho M).symm).val.app U z) = z := by
    have h := congrArg (fun k ↦ k.val.app U z) (eqToHom_trans (ho M).symm (ho M))
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using h
  rw [he, SheafOfModules.UnrestrictedTowerProof.map_tensorSection]


end SiteBalancing


private theorem scalar_composite (n : ℕ) :
    scalarMap l E T ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      finiteScalarMap l E T n := by
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat RingCat)).map_injective
  rw [CategoryTheory.Functor.map_comp]
  unfold scalarMap finiteScalarMap
  rw [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_preimage]
  change integralConstantToCompletionOfUniverses l E T ≫
    limit.π (integralCoefficientSheafSystem l E T) (op n) =
      integralConstantQuotientOfUniverses l E T n
  exact limit.lift_π _ _

attribute [local irreducible] scalarChange finiteChange constant
  modelModules scalarMap finiteScalarMap
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence

private instance finiteChange_additive (n : ℕ) : (finiteChange l E T n).E.Additive :=
  (finiteChange l E T n).additive

private instance scalarChange_additive : (scalarChange l E T).E.Additive :=
  (scalarChange l E T).additive

private instance constant_scalar_additive :
    (constant T (Scalars.{t, u} l E)).Additive := constant_additive T _

private instance reduction_additive (n : ℕ) :
    (unrestrictedIntegralReductionFunctor l E T n).Additive :=
  unrestrictedIntegralReductionFunctor_additive l E T n

private theorem balancing_exists (n : ℕ) :
    ∃ e : (scalarChange l E T).E ⋙ unrestrictedIntegralReductionFunctor l E T n ≅
        (finiteChange l E T n).E,
      ∀ M U a b x,
        (e.hom.app M).val.app U
          (unrestrictedIntegralTensorSection l E T n _ U a
            (normTensor (ProEt.topology T) (scalarMap l E T) (scalarChange l E T).E
              (scalarChange l E T).obj_eq M U b x)) =
          normTensor (ProEt.topology T) (finiteScalarMap l E T n) (finiteChange l E T n).E
            (finiteChange l E T n).obj_eq M U
              (a * (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b) x := by
  obtain ⟨a1, h1⟩ := normAdjunction (ProEt.topology T) (scalarMap l E T) (scalarChange l E T).E
    (scalarChange l E T).additive
    (scalarChange l E T).obj_eq (scalarChange l E T).map_eq
  obtain ⟨a2, h2⟩ := normAdjunction (ProEt.topology T)
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (unrestrictedIntegralReductionFunctor l E T n)
    (unrestrictedIntegralReductionFunctor_additive l E T n)
    (unrestrictedReduction_obj l E T n) (unrestrictedReduction_map l E T n)
  obtain ⟨a3, h3⟩ := normAdjunction (ProEt.topology T) (finiteScalarMap l E T n)
    (finiteChange l E T n).E (finiteChange l E T n).additive
    (finiteChange l E T n).obj_eq (finiteChange l E T n).map_eq
  exact balance_from_adjunctions (ProEt.topology T) (scalarMap l E T)
    (completedIntegralCommRingProjectionUnrestricted l E T n) (finiteScalarMap l E T n)
    (scalar_composite l E T n)
    _ _ a1 h1 (fun M ↦ normalizedTensor_smul (ProEt.topology T) _ M _
      ((scalarChange l E T).obj_eq M))
    _ _ a2 h2 (fun M ↦ normalizedTensor_smul (ProEt.topology T) _ M _
      (unrestrictedReduction_obj l E T n M))
    _ _ a3 h3 (fun M ↦ normalizedTensor_smul (ProEt.topology T) _ M _
      ((finiteChange l E T n).obj_eq M))

private def moduleBalance (n : ℕ) := (balancing_exists l E T n).choose

private def chainBalance (n : ℕ) :
    model l E T ⋙ unrestrictedIntegralFiniteComplex l E T n ≅ finiteModel l E T n := by
  letI := (finiteChange l E T n).additive
  letI := constant_additive T (Scalars.{t, u} l E)
  letI := unrestrictedIntegralReductionFunctor_additive l E T n
  letI : (constant T (Scalars.{t, u} l E) ⋙ (finiteChange l E T n).E).Additive :=
    { map_add := by
        intro X Y f g
        change (finiteChange l E T n).E.map ((constant T (Scalars.{t, u} l E)).map (f + g)) = _
        rw [(constant T (Scalars.{t, u} l E)).map_add,
          (finiteChange l E T n).E.map_add]
        rfl }
  unfold model modelModules
  exact Functor.mapHomologicalComplexCompIso
    (Functor.isoWhiskerLeft (constant T (Scalars.{t, u} l E)) (moduleBalance l E T n)) (.up ℤ)

private def scalarReductions (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) :
    Reductions l E T P := fun n ↦ (chainBalance l E T n).app P

private theorem scalarReductions_formula
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) :
    ReductionFormula l E T P (scalarReductions l E T P) := by
  intro n j U b a x
  unfold model modelModules modelSection
  exact (balancing_exists l E T n).choose_spec _ U a b x

private theorem reduction_hom_ext
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) (n : ℕ)
    (Q : CochainComplex (scalarReductionTarget l E T n) ℤ)
    (f g : (unrestrictedIntegralFiniteComplex l E T n).obj ((model l E T).obj P) ⟶ Q)
    (h : ∀ j U a b x,
      (f.f j).val.app U (unrestrictedIntegralTensorSection l E T n _ U a
        (modelSection l E T (P.X j) U b x)) =
      (g.f j).val.app U (unrestrictedIntegralTensorSection l E T n _ U a
        (modelSection l E T (P.X j) U b x))) : f = g := by
  obtain ⟨a1, h1⟩ := normAdjunction (ProEt.topology T) (scalarMap l E T) (scalarChange l E T).E
    (scalarChange l E T).additive
    (scalarChange l E T).obj_eq (scalarChange l E T).map_eq
  obtain ⟨a2, h2⟩ := normAdjunction (ProEt.topology T)
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (unrestrictedIntegralReductionFunctor l E T n)
    (unrestrictedIntegralReductionFunctor_additive l E T n)
    (unrestrictedReduction_obj l E T n) (unrestrictedReduction_map l E T n)
  apply HomologicalComplex.Hom.ext
  funext j
  apply (a2.homEquiv _ _).injective
  unfold model modelModules at *
  apply (a1.homEquiv _ _).injective
  ext U x
  rw [h1, h1]
  change (a2.homEquiv _ _ (f.f j)).val.app U _ =
    (a2.homEquiv _ _ (g.f j)).val.app U _
  rw [h2, h2]
  exact h j U 1 1 x

private theorem reduction_independent (r s : ModelReductions l E T)
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P) (n : ℕ) : r.reduction P hP n = s.reduction P hP n := by
  apply Iso.ext
  apply reduction_hom_ext l E T P n
  intro j U a b x
  exact (r.formula P hP n j U b a x).trans (s.formula P hP n j U b a x).symm

private theorem reduction_inverse
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (r : Reductions l E T P) (hr : ReductionFormula l E T P r) :
    InverseFormula l E T P r := by
  intro n j U a x
  have h := hr n j U 1 a x
  rw [map_one, mul_one] at h
  have hc (z) : ((r n).inv.f j).val.app U (((r n).hom.f j).val.app U z) = z := by
    exact congrArg (fun f ↦ (f.f j).val.app U z) (r n).hom_inv_id
  exact (congrArg (fun z ↦ ((r n).inv.f j).val.app U z) h).symm.trans (hc _)

private theorem reduction_unit
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (r : Reductions l E T P) (hr : ReductionFormula l E T P r) :
    UnitFormula l E T P r := by
  intro n j U b x
  rw [unrestrictedTowerUnit_condition l E T ((model l E T).obj P) n j U]
  simpa only [unrestrictedTowerTensorSection, one_mul] using hr n j U b 1 x

private theorem scalarReductions_transition
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) :
    TransitionFormula l E T P (scalarReductions l E T P) := by
  intro n j U a x
  let r := scalarReductions l E T P
  have hinv := reduction_inverse l E T P r (scalarReductions_formula l E T P)
  simp only [integralOperationsTowerStep, quotientTower,
    CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
  change (((r n).hom.f j).val.app U)
    ((((unrestrictedIntegralTransition l E T n).app ((model l E T).obj P)).f j).val.app U
      (((r (n + 1)).inv.f j).val.app U (finiteSection l E T (n + 1) (P.X j) U a x))) = _
  rw [hinv]
  have ht := (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec
    ((model l E T).obj P) j U a (modelSection l E T (P.X j) U 1 x)
  change (((unrestrictedIntegralTransition l E T n).app
    ((model l E T).obj P)).f j).val.app U _ = _ at ht
  rw [ht]
  simpa only [map_one, mul_one] using
    scalarReductions_formula l E T P n j U 1
      ((integralCoefficientSheafTransition l E T n).hom.app U a) x

private def normalizedReductions : ModelReductions l E T where
  reduction P _ := scalarReductions l E T P
  formula P _ := scalarReductions_formula l E T P
  transition P _ := scalarReductions_transition l E T P
  naturality _P _Q _ _ f n := (chainBalance l E T n).hom.naturality f

private theorem derived_naturality (r : ModelReductions l E T)
    (P Q : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
    (hP : IsModel l E P) (hQ : IsModel l E Q) (f : P ⟶ Q) (n : ℕ) :
    (scalarReductionDerivedExtension l E T n).map ((derivedModel l E T).map f) ≫
        (derivedReductionIso l E T Q hQ (r.reduction Q hQ) n).hom =
      (derivedReductionIso l E T P hP (r.reduction P hP) n).hom ≫
        DerivedCategory.Q.map ((finiteModel l E T n).map f) := by
  have hc (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E)
      (hP : IsModel l E P) :
      (derivedReductionIso l E T P hP (r.reduction P hP) n).hom =
        (towerCounit l E T n).app ((model l E T).obj P) ≫
          DerivedCategory.Q.map (r.reduction P hP n).hom := by
    unfold derivedReductionIso
    change (unrestrictedTowerResolutionIso l E T n (𝟙 _) _).hom ≫ _ = _
    congr 1
    have he := towerResolution_hom l E T n (𝟙 ((model l E T).obj P))
      ⟨inferInstance, (model_good l E T P hP).1⟩
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using he
  have hn := (towerCounit l E T n).naturality ((model l E T).map f)
  change (scalarReductionDerivedExtension l E T n).map
      (DerivedCategory.Q.map ((model l E T).map f)) ≫
      (towerCounit l E T n).app ((model l E T).obj Q) =
    (towerCounit l E T n).app ((model l E T).obj P) ≫
      DerivedCategory.Q.map ((unrestrictedIntegralFiniteComplex l E T n).map
        ((model l E T).map f)) at hn
  rw [hc P hP, hc Q hQ]
  calc
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map (r.reduction Q hQ n).hom) hn
    _ = _ := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
        r.naturality P Q hP hQ f n, CategoryTheory.Functor.map_comp, Category.assoc]


private theorem constant_map_formula
    {V W : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)} (f : V ⟶ W)
    (U : T.ProEtᵒᵖ) (x : V) :
    ((constant T (Scalars.{t, u} l E)).map f).val.app U
      (constantSection l E T V U x) = constantSection l E T W U (f x) := by
  let := (constantUnit_local T (Scalars.{t, u} l E)).1
  let := (constantUnit_local T (Scalars.{t, u} l E)).2
  unfold constant
  exact (congrArg (fun k ↦ k.app U x)
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
      (constantUnit T (Scalars.{t, u} l E))).unit.naturality
        ((constantPresheaf T (Scalars.{t, u} l E)).map f))).symm

private theorem map_formula
    {V W : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)} (f : V ⟶ W) :
    MapFormula l E T f := by
  refine ⟨constant_map_formula l E T f, ?_, ?_⟩
  · intro U b x
    unfold modelModules modelSection
    exact normalized_map_formula (ProEt.topology T) (scalarMap l E T) (scalarChange l E T).E
      (scalarChange l E T).obj_eq (scalarChange l E T).map_eq
      ((constant T (Scalars.{t, u} l E)).map f) U b x
  · intro n U a x
    exact normalized_map_formula (ProEt.topology T) (finiteScalarMap l E T n)
      (finiteChange l E T n).E
      (finiteChange l E T n).obj_eq (finiteChange l E T n).map_eq
      ((constant T (Scalars.{t, u} l E)).map f) U a x

private theorem model_splittings
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) (hP : IsModel l E P) :
    Splittings l E T P := by
  intro j
  have := (hP.2 j).1
  have := (hP.2 j).2
  obtain ⟨m, s, i, _, _, hsi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (Scalars.{t, u} l E) (P.X j)
  let i' : P.X j ⟶ ModuleCat.of (Scalars.{t, u} l E) (Fin m → Scalars.{t, u} l E) :=
    ModuleCat.ofHom i
  let s' : ModuleCat.of (Scalars.{t, u} l E) (Fin m → Scalars.{t, u} l E) ⟶ P.X j :=
    ModuleCat.ofHom s
  have his : i' ≫ s' = 𝟙 _ := ModuleCat.hom_ext hsi
  refine ⟨m, i', s', his, ?_, ?_, ?_, map_formula l E T i', map_formula l E T s'⟩
  · rw [← CategoryTheory.Functor.map_comp, his, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, his, CategoryTheory.Functor.map_id]
  · intro n
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, his,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

private theorem scalarResolution : ScalarResolution l E := by
  intro n
  have h := (sf_bc_adic_ring_domain l E).2.2.2.2.2.2.2.2.2 (n + 1) (by omega)
  refine ⟨h.1, h.2.1, ?_, ?_, Ideal.Quotient.mk_surjective⟩
  · exact mul_right_injective₀ (pow_ne_zero _ (AlgebraicGeometry.uniformizer_ne_zero l E))
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change x ∈ (Ideal.span {Padic.coefficientExtensionUniformizer l E}) ^ (n + 1) ↔ _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

private theorem model_bounded
    (P : WeilConjectures.CompletedPerfectScalar.Complex.{t, u} l E) (hP : IsModel l E P) :
    ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (((model l E T).obj P).X j) := by
  obtain ⟨a, b, hab⟩ := hP.1
  exact ⟨a, b, fun j hj ↦ (modelModules l E T).map_isZero (hab j hj)⟩

/-- Adic scalar data and normalized flat reduction complexes exist on every small
pro-etale site. Source: Stacks 093M, 06YQ, 0G7E and 05V4; Bhatt--Scholze 4.2.12,
6.5.9 and 6.6.11 (blueprint: lem-a1-adic-scalar-flat-reduction-model).

Proof:
1. The valuation-ring theorem makes R a DVR with finite residue field. Thus R is
Noetherian and its uniformizer ideal is principal. The nonzero scalar l lies in
that ideal; l^(n+1) kills R/pi^(n+1). The finite-quotient theorem gives finiteness.
Multiplication by pi^(n+1) is injective, its image is the kernel of the quotient,
and the quotient is surjective. This is the displayed finite free resolution in
chain degrees -1 and 0, proving perfectness and all adic-datum hypotheses.
2. Bhatt--Scholze 4.2.12 identifies finite constant sections with continuous
functions on the underlying space. Factor through connected components with the
quotient topology. This is the displayed locally constant function ring; constants,
restrictions and quotient postcomposition are unchanged. The sectionwise limit
universal property identifies the completed sheaf and every coordinate projection.
3. A finite projective module splits off a finite free module by Stacks 00NX/05CF.
Apply constant realization and scalar extension to i followed by s. Functoriality
preserves the identity; the tensor formulas show commutation with each quotient.
These are degreewise splittings, with no chain splitting asserted.
4. Tensoring the retract with any short exact sequence splits its tensor sequence
off the exact finite direct sum sequence. This proves flatness for constant terms
and completed scalar terms. Realization preserves the zero terms outside the
original finite interval. Apply bounded-flat K-flatness (06YQ), at the independent
site and coefficient sizes, with the original scalar differentials.
5. Define balancing on local generators by (b tensor p) tensor a ↦ a pr(b) tensor p
and its inverse by a tensor p ↦ (1 tensor p) tensor a. Both balancing relations
hold because pr is a scalar-algebra map. Extend across the two sheafifications by
uniqueness of bilinear sheafification extension. The formulas compose to the
identity, respect restrictions and commute with the original differentials.
6. Apply the change-of-rings K-flat computation counit to the identity resolution
of the completed scalar complex, then localize the ordinary chain isomorphism.
This is precisely the displayed derivedReductionIso, including its counit.
7. For every consecutive quotient q both routes send the generator to
q(a) pr(b) tensor p. The inverse square inserts 1 on both routes. The actual
reduction unit sends b tensor p to (b tensor p) tensor 1, so balancing gives exactly
pr(b) tensor p, the stipulated quotient augmentation.
8. For a scalar chain map f both routes give a pr(b) tensor f(p); the inverse
routes give (1 tensor f(p)) tensor a. This proves naturality. Uniqueness on local
generators makes the comparisons independent of the auxiliary degreewise
splittings. These arguments allow the empty scheme, the zero complex, and l
noninvertible on T; neither a characteristic assumption nor a universe equality
is introduced. -/
theorem adicScalarFlatReductionModel : Nonempty (Data l E T) := by
  obtain ⟨d, hd⟩ := (sf_bc_adic_ring_domain l E).2.2.2.2.2.2.2.2.1
  obtain ⟨cf⟩ := finite_coefficients l E T
  refine ⟨{
    datum := d
    datumIdeal := hd
    resolutions := scalarResolution l E
    coefficients := cf
    reductions := normalizedReductions l E T
    constantFlat := ?_
    bounded := model_bounded l E T
    kflat := fun P hP ↦ (model_good l E T P hP).1
    termFlat := fun P hP ↦ (model_good l E T P hP).2
    splittings := model_splittings l E T
    inverseFormula := fun P _ ↦ reduction_inverse l E T P _
      (scalarReductions_formula l E T P)
    unitFormula := fun P _ ↦ reduction_unit l E T P _ (scalarReductions_formula l E T P)
    independent := fun r ↦ reduction_independent l E T r (normalizedReductions l E T)
    derivedNatural := derived_naturality l E T (normalizedReductions l E T) }⟩
  intro P hP j
  have := (hP.2 j).2
  exact constant_flat T (Scalars.{t, u} l E) (P.X j) inferInstance

end WeilConjectures.AdicScalarFlatReduction
