/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Sheaf.AlgebraicGeometry.VaryingRingOperations

/-! # Coherent composition of finite-coefficient pullback on strict systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and sites-modules.tex,
Tags 03D3, 03D7, 03D8. The strict-system refinement uses componentwise adjunctions
and coherence before localization
(blueprint: lem-pod-finite-system-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

namespace WeilConjectures

/-- The existing sheafification witness at the specified coefficient universe.
Source: Stacks 00W1 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} X

/-- The existing small-site witness, retaining the original two site universes.
Source: Stacks 09A5 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- Smallness of the sequence site in the very same coefficient universe.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemSequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  SemilinearSections.sequenceSmall.{u + 1, u, u + 1}

variable (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n)

/-- The actual constant ring sheaves, in the published coefficient presentation.
Source: Stacks 0D6D (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemRings (X : Scheme.{u}) (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  proEtaleConstantRing.{u} X (A n)

/-- The given coefficient maps, transported by constant sheafification.
Source: Stacks 0D6D (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemRingTransition (X : Scheme.{u}) (n : ℕ) :
    finiteSystemRings.{u} A X (n + 1) ⟶ finiteSystemRings.{u} A X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (ProEt.topology X) CommRingCat.{u + 1}).map
    (X := CommRingCat.of (ULift.{u + 1, u} (A (n + 1))))
    (Y := CommRingCat.of (ULift.{u + 1, u} (A n)))
    (CommRingCat.ofHom ((τ n).hom.ulift))

/-- Strict semilinear systems on the actual ringed sequence site.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystems (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X)

/-- Ordinary unbounded derived systems, rather than diagrams of derived modules.
Source: Stacks 05RU (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X)

/-- Exact evaluation at a coefficient level.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemEvaluation (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X) n

/-- Base change of the vertical sequence site retains its horizontal arrows.
Source: Stacks 0941, 09A5 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ℕ × Y.ProEt) ⥤ (ℕ × X.ProEt) :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Continuity of sequence-site base change.
Source: Stacks 0941, 09A5 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: a vertical cover at n is sent to the base change of that cover at n.
Continuity of pro-etale base change therefore gives the sheaf condition on every
vertical slice, which defines the sequence topology. -/
theorem finiteSystemBaseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteSystemBaseChange.{u} f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact AlgebraicGeometry.ProEtale.VaryingRing.baseChange_continuous f

attribute [instance] finiteSystemBaseChange_continuous

/-- The constant-section coefficient map at an actual sequence-site object.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemRingComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : (ℕ × Y.ProEt)ᵒᵖ) :=
  (proEtaleCoefficientDirectImageMap f (A U.unop.1)).hom.app (op U.unop.2)

/-- Coefficient maps commute with both semilinear transitions and site restrictions.
Source: Stacks 03D3, 03D7 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: the horizontal square sends a constant a to the constant τ(a) on both paths.
Uniqueness of extension from the constant presheaf proves the square. The vertical
square is naturality of the coefficient map. Factor every product-site arrow into
a horizontal arrow and a vertical arrow and paste the two squares. -/
theorem finiteSystemRingComponent_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (g : U ⟶ V) :
    (ringPresheaf.{u + 1, u, u + 1} (ProEt.topology Y) (finiteSystemRings.{u} A Y)
        (finiteSystemRingTransition.{u} A τ Y)).map g ≫ finiteSystemRingComponent.{u} A f V =
      finiteSystemRingComponent.{u} A f U ≫
        (ringPresheaf.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
          (finiteSystemRingTransition.{u} A τ X)).map
          ((finiteSystemBaseChange.{u} f).op.map g) := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
  change
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology Y))
      (systemRing.{u + 1, u, u + 1} (ProEt.topology Y)
        (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R Y)
        (AlgebraicGeometry.ProEtale.VaryingRing.coefficientTransition R φ Y))).obj.map g ≫
      (forget₂ CommRingCat RingCat).map
        ((proEtaleConstantDirectImageMap f CommRingCat
          (CommRingCat.of (ULift.{u + 1, u} (A V.unop.1)))).hom.app (op V.unop.2)) =
    (forget₂ CommRingCat RingCat).map
        ((proEtaleConstantDirectImageMap f CommRingCat
          (CommRingCat.of (ULift.{u + 1, u} (A U.unop.1)))).hom.app (op U.unop.2)) ≫
      (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology X))
        (systemRing.{u + 1, u, u + 1} (ProEt.topology X)
          (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R X)
          (AlgebraicGeometry.ProEtale.VaryingRing.coefficientTransition R φ X))).obj.map
        ((AlgebraicGeometry.ProEtale.VaryingRing.baseChange f).map g.unop).op
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringMapApp_naturality R φ f g


/-- The ring-sheaf map on the entire sequence site, including all coefficient maps.
Source: Stacks 03D3, 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemRing.{u + 1, u, u + 1} (ProEt.topology Y) (finiteSystemRings.{u} A Y)
    (finiteSystemRingTransition.{u} A τ Y) ⟶
      ((finiteSystemBaseChange.{u} f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (systemRing.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
            (finiteSystemRingTransition.{u} A τ X)) where
  hom :=
    { app := finiteSystemRingComponent.{u} A f
      naturality := fun {_ _} g ↦ finiteSystemRingComponent_naturality.{u} A τ f g }

/-- Sectionwise direct image with its specified constant-section scalar action.
Source: Stacks 03D3, 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystems.{u} A τ X ⥤ finiteSystems.{u} A τ Y :=
  SheafOfModules.pushforward.{u + 1} (F := finiteSystemBaseChange.{u} f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := ring.{u + 1, u, u + 1} _ (systemRing.{u + 1, u, u + 1} (ProEt.topology Y)
      (finiteSystemRings.{u} A Y)
      (finiteSystemRingTransition.{u} A τ Y)))
    (R := ring.{u + 1, u, u + 1} _ (systemRing.{u + 1, u, u + 1} (ProEt.topology X)
      (finiteSystemRings.{u} A X)
      (finiteSystemRingTransition.{u} A τ X)))
    ⟨Functor.whiskerRight (finiteSystemRingMap.{u} A τ f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Existence of the universal system pullback adjunction.
Source: Stacks 03D3, 03D7 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: take module Kan extension followed by sheafification on small models of the
sequence sites. Its Hom correspondence is the componentwise module adjunction.
Naturality of the constant-section coefficient maps makes this correspondence
restrict to transition-compatible families. Transport back along the site equivalences. -/
theorem finiteSystemPushforward_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteSystemPushforward.{u} A τ f).IsRightAdjoint := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  change (AlgebraicGeometry.ProEtale.VaryingRing.push R φ f).IsRightAdjoint
  infer_instance

attribute [instance] finiteSystemPushforward_isRightAdjoint

/-- The universal left adjoint of the explicit sectionwise system direct image.
Its universal property determines it up to the unique adjunction-compatible iso.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (finiteSystemPushforward.{u} A τ f).leftAdjoint

/-- The actual system adjunction, fixing its units and all conjugate comparisons.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Adjunction.ofIsRightAdjoint (finiteSystemPushforward.{u} A τ f)

/-- Finite-coefficient inverse image on systems is componentwise exact.
Source: Stacks 03D3, 0941 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: the componentwise adjunction identifies each evaluation with the finite
constant-coefficient module inverse image. That inverse image is exact by
prop-weil-pbc-proetale-constant-exact. Kernels, cokernels and addition of strict
systems are componentwise by lem-coef-semilinear-derived-sections. -/
theorem finiteSystemPullback_exact [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteSystemPullback.{u} A τ f).Additive ∧
      PreservesFiniteLimits (finiteSystemPullback.{u} A τ f) ∧
      PreservesFiniteColimits (finiteSystemPullback.{u} A τ f) := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  exact AlgebraicGeometry.ProEtale.VaryingRing.pull_exact R φ f

/-- Additivity of the actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackAdditive [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (finiteSystemPullback.{u} A τ f).Additive :=
  (finiteSystemPullback_exact.{u} A τ f).1

/-- Preservation of finite limits by actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackLimits [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (finiteSystemPullback.{u} A τ f) :=
  (finiteSystemPullback_exact.{u} A τ f).2.1

/-- Preservation of finite colimits by actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackColimits [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (finiteSystemPullback.{u} A τ f) :=
  (finiteSystemPullback_exact.{u} A τ f).2.2

/-- The stipulated exact, termwise functor on ordinary unbounded derived systems.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerivedPullback [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemDerived.{u} A τ Y ⥤ finiteSystemDerived.{u} A τ X :=
  (finiteSystemPullback.{u} A τ f).mapDerivedCategory

/-- The unique ordinary comparison with the sectionwise fibre-product conjugate.
Source: Stacks 03D8, 0B65 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: restriction along the fibre-product isomorphism is natural in sections,
linear because the coefficient maps preserve constants, and commutes with every
horizontal transition. It fixes d uniquely. Conjugation through the actual system
adjunctions gives the unique a; the conjugation bijection proves uniqueness. -/
theorem finiteSystemComposition_existsUnique
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    ∃! a : finiteSystemPullback.{u} A τ (h ≫ k) ≅
        finiteSystemPullback.{u} A τ k ⋙ finiteSystemPullback.{u} A τ h,
      ∃ d : finiteSystemPushforward.{u} A τ h ⋙ finiteSystemPushforward.{u} A τ k ≅
          finiteSystemPushforward.{u} A τ (h ≫ k),
        conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
          (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k)) a = d ∧
        ∀ (M : finiteSystems.{u} A τ Z) (n : ℕ) (U : V.ProEt)
          (x : ((finiteSystemPushforward.{u} A τ h ⋙
            finiteSystemPushforward.{u} A τ k).obj M).val.obj (op (n, U))),
          (d.hom.app M).val.app (op (n, U)) x =
            M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
              ((MorphismProperty.Over.pullbackComp h k (h ≫ k) rfl).hom.app U)).op x := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  obtain ⟨d, hd, huniq⟩ :=
    AlgebraicGeometry.ProEtale.VaryingRing.modulePComp_existsUnique R φ h k
  let e := conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
    (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k))
  refine ⟨e.symm d, ⟨d, e.apply_symm_apply d, hd⟩, ?_⟩
  intro a ha
  obtain ⟨d', he, hd'⟩ := ha
  apply e.injective
  rw [e.apply_symm_apply]
  exact he.trans (huniq d' hd')

/-- Select the comparison determined uniquely by the full system adjunction.
Source: Stacks 03D8 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemComposition {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :=
  (finiteSystemComposition_existsUnique.{u} A τ h k).exists.choose

/-- The comparison on complexes, before localization, applied degreewise.
Source: Stacks 0D6D (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemComplexComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :=
  NatIso.mapHomologicalComplex (finiteSystemComposition.{u} A τ h k) (ComplexShape.up ℤ)

/-- The derived comparison is the localization of the specified whole-system map.
Source: Stacks 0D6D, 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemDerivedComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemDerivedPullback.{u} A τ (h ≫ k) ≅
      finiteSystemDerivedPullback.{u} A τ k ⋙ finiteSystemDerivedPullback.{u} A τ h :=
  Functor.mapDerivedCategoryNatIso (finiteSystemComposition.{u} A τ h k) ≪≫
    Functor.mapDerivedCategoryCompIso (finiteSystemPullback.{u} A τ k)
      (finiteSystemPullback.{u} A τ h)

/-- Exact evaluation on the ordinary derived system category.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :=
  e.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X) n

/-- The component identification is uniquely fixed on adjunction-unit generators.
Source: Stacks 03D3, 03D7 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: restrict the componentwise Hom adjunction to compatible system maps.
Evaluation of the system unit is the level unit. The level pullback is generated
locally by these unit sections and their scalar multiples, so a module map
satisfying this formula is unique. The componentwise construction gives its
inverse. No test for equality of derived maps is used. -/
theorem finiteSystemPullbackEvaluation_existsUnique [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! q : finiteSystemPullback.{u} A τ f ⋙ finiteSystemEvaluation.{u} A τ X n ≅
        finiteSystemEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingPullback (A n) f,
      ∀ (M : finiteSystems.{u} A τ Y) (U : Y.ProEt)
        (m : ((finiteSystemEvaluation.{u} A τ Y n).obj M).val.obj (op U)),
        (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
            (((finiteSystemAdjunction.{u} A τ f).unit.app M).val.app (op (n, U)) m) =
          (((proEtaleConstantRingAdjunction (A n) f).unit.app
            ((finiteSystemEvaluation.{u} A τ Y n).obj M)).val.app (op U)) m := by
  sorry

/-- The unit-normalized ordinary component identification.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (finiteSystemPullbackEvaluation_existsUnique.{u} A τ f n).exists.choose

/-- The derived evaluation identification is exactly the termwise localization.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemDerivedPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemDerivedPullback.{u} A τ f ⋙ finiteSystemDerivedEvaluation.{u} A τ X n ≅
      finiteSystemDerivedEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingDerivedPullback (A n) f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteSystemPullbackEvaluation.{u} A τ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The existing canonical module comparison, fixed by its fibre-product conjugate.
The property in the published existence theorem determines its map uniquely:
sectionwise restriction fixes the right comparison, and conjugation is bijective.
Source: Stacks 03D8 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemModuleComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :=
  (proEtaleConstantRingModulePullbackComposition h k (A n)).choose

/-- Complex pullback is termwise on arbitrary unbounded complexes.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemComplexPullback [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (finiteSystemPullback.{u} A τ f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The finite-system comparisons have their specified levelwise realizations and
satisfy associativity before and after ordinary localization.
Source: Stacks 03D3, 03D7, 03D8, 0B65, 015F, 0D6D
(blueprint: lem-pod-finite-system-pullback-coherence).
Proof: (1) Constant-section naturality gives compatibility with coefficient maps,
including the adjoint coefficient square for direct image. Restrict the level
module adjunctions to transition-compatible families to obtain the system
adjunction with its componentwise unit. (2) The fibre-product restriction maps
commute with every sheaf map and scalar action, giving whole-system right-adjoint
comparisons. Their two triple composites have equal fibre-product projections,
hence agree. (3) Conjugate these maps under the system adjunctions. Evaluation of
the unit equation is the level unit equation, so conjugation uniqueness identifies
each evaluated map with the published canonical module comparison. In particular
these maps commute with semilinear transitions before deriving. (4) Apply
leftAdjointCompIso_assoc to the six adjunctions and invert the resulting equation.
Apply it degreewise to complexes: naturality in the differential makes these
chain maps, and the equation is an equation of natural transformations of complex
functors. (5) Exactness permits ordinary termwise localization. The localization
universal property transports the equation to derived systems. (6) Evaluation is
exact and termwise. On a flat-term K-flat resolution the published finite derived
comparison is the localization of precisely the same module map, by Tag 0D6D.
Exactness preserves the resolution quasi-isomorphisms, so naturality extends this
identification to every complex. No transition is tensored along a coefficient
map, and no normalization or boundedness is used. -/
theorem finiteSystemPullbackCoherence [∀ n, Finite (A n)]
    {Y Z W V : Scheme.{u}} (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) :
    (∀ (M : finiteSystems.{u} A τ V) (n : ℕ),
      (finiteSystemEvaluation.{u} A τ Z n).map ((finiteSystemComposition.{u} A τ h k).hom.app M) ≫
          (finiteSystemPullbackEvaluation.{u} A τ h n).hom.app
            ((finiteSystemPullback.{u} A τ k).obj M) ≫
          (proEtaleConstantRingPullback (A n) h).map
            ((finiteSystemPullbackEvaluation.{u} A τ k n).hom.app M) =
        (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app M ≫
          (finiteSystemModuleComposition.{u} A h k n).hom.app
            ((finiteSystemEvaluation.{u} A τ V n).obj M)) ∧
    (∀ (S : finiteSystemDerived.{u} A τ V) (n : ℕ),
      (finiteSystemDerivedEvaluation.{u} A τ Z n).map
          ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) ≫
          (finiteSystemDerivedPullbackEvaluation.{u} A τ h n).hom.app
            ((finiteSystemDerivedPullback.{u} A τ k).obj S) ≫
          (proEtaleConstantRingDerivedPullback (A n) h).map
            ((finiteSystemDerivedPullbackEvaluation.{u} A τ k n).hom.app S) =
        (finiteSystemDerivedPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app S ≫
          (proEtaleConstantRingPullbackComposition h k (A n)).inv.app
            ((finiteSystemDerivedEvaluation.{u} A τ V n).obj S)) ∧
    (eqToHom (congrArg (finiteSystemComplexPullback.{u} A τ) (Category.assoc j h k)) ≫
        (finiteSystemComplexComposition.{u} A τ j (h ≫ k)).hom ≫
        Functor.whiskerRight (finiteSystemComplexComposition.{u} A τ h k).hom
          (finiteSystemComplexPullback.{u} A τ j) =
      (finiteSystemComplexComposition.{u} A τ (j ≫ h) k).hom ≫
        Functor.whiskerLeft (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexComposition.{u} A τ j h).hom ≫
        (Functor.associator (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexPullback.{u} A τ h) (finiteSystemComplexPullback.{u} A τ j)).inv) ∧
    (∀ S : finiteSystemDerived.{u} A τ V,
      (eqToHom (congrArg (finiteSystemDerivedPullback.{u} A τ) (Category.assoc j h k))).app S ≫
          (finiteSystemDerivedComposition.{u} A τ j (h ≫ k)).hom.app S ≫
          (finiteSystemDerivedPullback.{u} A τ j).map
            ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) =
        (finiteSystemDerivedComposition.{u} A τ (j ≫ h) k).hom.app S ≫
          (finiteSystemDerivedComposition.{u} A τ j h).hom.app
            ((finiteSystemDerivedPullback.{u} A τ k).obj S)) := by
  sorry

end WeilConjectures
