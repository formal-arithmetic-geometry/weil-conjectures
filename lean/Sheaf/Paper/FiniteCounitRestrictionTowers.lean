/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Finite.Stalk
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.Paper.DiscreteExchangeSiteComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Sheaf.AlgebraicGeometry.FiniteFpProEtalePushforwardExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Finite exchange and point-counit maps on strict coefficient systems

Source: Stacks Project, etale-cohomology.tex, Tags 0959 and 03QP;
proetale.tex, Tags 09A8 and 09AL
(blueprint: lem-zl-finite-counit-restriction-towers).

The sequence-site category retains quotient transitions before localization.
The natural-number level n denotes coefficient exponent n+1. Finite products
below are the canonical finite direct sums, including the empty zero object.

## Main definitions

* `exchange`, `restriction`, `b`, `r`: the actual system and chain maps.
* `fixedPull`, `proExchange`, `etExchange`: unit-normalized finite evaluation.
* `Descent`: localization of both transformations with their chain factorizations.

## Main statements

* `transitionSquares`: strict quotient compatibility before localization.
* `fixedExchange`, `fixedComponent`, `comparisonArrows`: identification of actual arrows.
* `finiteCounitRestrictionTowers`: finite exactness, quasi-isomorphisms and derived limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.FiniteCounitTowers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The already constructed inverse image of whole strict quotient systems.
Source: Stacks 03D7, 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralComparisonSequencePullback l E f

/-- The sectionwise direct image of whole strict quotient systems.
Source: Stacks 03D7, 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralComparisonSequenceDirectImage l E f

/-- The actual system adjunction, retaining its specified unit and counit.
Source: Stacks 03D7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull l E f ⊣ push l E f :=
  Adjunction.ofIsRightAdjoint _

/-- The geometric lifts over the fixed geometric point, with no nonemptiness assumption.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev Points {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  { x : s ⟶ X // x ≫ f = y }

/-- The unique fibre-product lift of a point of the fibre.
Source: Stacks 0959 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def lift {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (x : Points f y) :
    s ⟶ Limits.pullback f y :=
  pullback.lift x.val (𝟙 s) (x.property.trans (Category.id_comp y).symm)

/-- The square comparison is the compositor fixed by fibre-product pasting and mates.
Source: Stacks 03D8, 0959 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def square {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    pull l E y ⋙ pull l E (pullback.snd f y) ≅
      pull l E f ⋙ pull l E (pullback.fst f y) :=
  (integralComparisonSequenceComposition l E (pullback.snd f y) y).symm ≪≫
    eqToIso (congrArg (pull l E) (pullback.condition (f := f) (g := y)).symm) ≪≫
      integralComparisonSequenceComposition l E (pullback.fst f y) f

/-- The exchange map is the unit--square--counit mate, on whole strict systems.
Source: Stacks 0959, 07A7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def exchange {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    push l E f ⋙ pull l E y ⟶
      pull l E (pullback.fst f y) ⋙ push l E (pullback.snd f y) :=
  (mateEquiv (adj l E f) (adj l E (pullback.snd f y))
    (TwoSquare.mk _ _ _ _ (square l E f y).hom)).natTrans

/-- The point restriction is obtained by pulling back the actual counit at h.
Source: Stacks 03QP, 03D7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def pointRestriction {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (x : Points f y) :
    push l E (pullback.snd f y) ⟶ pull l E (lift f y x) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerLeft (push l E (pullback.snd f y))
      (integralComparisonSequenceUnit l E s).inv ≫
    Functor.whiskerLeft (push l E (pullback.snd f y))
      (eqToIso (congrArg (pull l E) (pullback.lift_snd x.val (𝟙 s)
        (x.property.trans (Category.id_comp y).symm)))).inv ≫
    Functor.whiskerLeft (push l E (pullback.snd f y))
      (integralComparisonSequenceComposition l E (lift f y x) (pullback.snd f y)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (adj l E (pullback.snd f y)).counit (pull l E (lift f y x)) ≫
    (Functor.leftUnitor _).hom

/-- The x-component, identified with x* by the normalized composition comparison.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
def component {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (x : Points f y) :
    pull l E (pullback.fst f y) ⋙ push l E (pullback.snd f y) ⟶ pull l E x.val :=
  Functor.whiskerLeft (pull l E (pullback.fst f y)) (pointRestriction l E f y x) ≫
    (integralComparisonSequenceComposition l E (lift f y x) (pullback.fst f y)).inv ≫
    (eqToIso (congrArg (pull l E) (pullback.lift_fst x.val (𝟙 s)
      (x.property.trans (Category.id_comp y).symm)))).hom

/-- The finite point-restriction target, formed in the functor category.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
def pointSum {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  ∏ᶜ (fun x : Points f y ↦ pull l E x.val)

/-- The tuple of counit restrictions; its projections are exactly the individual germs.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
def restriction {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    pull l E (pullback.fst f y) ⋙ push l E (pullback.snd f y) ⟶ pointSum l E f y :=
  Pi.lift (fun x ↦ component l E f y x)

/-- The fibre index is finite, including the empty fibre.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: apply the finite geometric stalk formula to f at y; its indexing points
are exactly Points f y, by the universal property of the scheme fibre product. -/
theorem finitePoints (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Spec (.of k) ⟶ Y) :
    Finite (Points f y) := by
  infer_instance

/-- Finite locally finitely presented direct image is exact on strict systems.
Source: Stacks 09A8, 03QP (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: finite_fp_proEtale_pushforward_exact gives exactness at every finite
coefficient level. Kernels and cokernels on the vertical sequence site are
computed levelwise, hence the system direct image is additive and exact. -/
theorem pushExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [LocallyOfFinitePresentation f] :
    (push l E f).Additive ∧ PreservesFiniteLimits (push l E f) ∧
      PreservesFiniteColimits (push l E f) := by
  have : (push l E f).Additive :=
    Functor.additive_of_preserves_binary_products (push l E f)
  have : PreservesFiniteLimits (push l E f) := inferInstance
  let RX := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X)
  let RY := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y)
  let TX := SheafOfModules.toSheaf.{u + 1} RX
  let TY := SheafOfModules.toSheaf.{u + 1} RY
  have : PreservesFiniteColimits TX := (moduleSheaves_colimits_forgetful RX).2.2.1
  let P := Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}
  have : PreservesFiniteColimits P :=
    (Scheme.finite_fp_proEtale_pushforward_exact f).2.1
  have : (push l E f).PreservesEpimorphisms := by
    constructor
    intro M N a ha
    apply TY.epi_of_epi_map
    have hlevel (n : ℕ) :
        Sheaf.IsLocallySurjective
          (P.map (((Prod.sectR n X.ProEt).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1} (Scheme.ProEt.topology X)
              (coefficientSequenceTopology (Scheme.ProEt.topology X))).map (TX.map a))) := by
      let : (Prod.sectR n X.ProEt).IsCocontinuous (Scheme.ProEt.topology X)
          (coefficientSequenceTopology (Scheme.ProEt.topology X)) := ⟨fun hS ↦ hS⟩
      have : PreservesColimitsOfSize.{0, 0}
          ((Prod.sectR n X.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Scheme.ProEt.topology X)
              (coefficientSequenceTopology (Scheme.ProEt.topology X))) :=
        ((Prod.sectR n X.ProEt).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (Scheme.ProEt.topology X)
            (coefficientSequenceTopology (Scheme.ProEt.topology X))).leftAdjoint_preservesColimits
      exact (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
    have : Sheaf.IsLocallySurjective (TY.map ((push l E f).map a)) := by
      refine ⟨fun {U} z ↦ ?_⟩
      change (Presheaf.imageSieve (TY.map ((push l E f).map a)).hom z).functorPullback
        (Prod.sectR U.1 Y.ProEt) ∈ Scheme.ProEt.topology Y U.2
      have hn := (hlevel U.1).imageSieve_mem z
      exact hn
    exact Sheaf.epi_of_isLocallySurjective _
  have : (push l E f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (push l E f)
  exact ⟨inferInstance, inferInstance,
    Functor.preservesFiniteColimits_of_preservesHomology (push l E f)⟩

/-- Additivity of the actual direct image, needed for its termwise complex functor.
Source: Stacks 03D7 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: direct image acts by the same linear maps on each section, hence preserves sums. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (push l E f).Additive := by
  exact Functor.additive_of_preserves_binary_products (push l E f)

/-- The direct-image additive instance uses its separately named theorem.
Source: Stacks 03D7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
instance pushAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) : (push l E f).Additive :=
  push_additive l E f

/-- The source strict-system complex functor Q ↦ y* f_* Q.
Source: Stacks 0959 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev B {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  (push l E f ⋙ pull l E y).mapHomologicalComplex (.up ℤ)

/-- The middle strict-system complex functor Q ↦ h_* v* Q.
Source: Stacks 0959 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev C {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  (pull l E (pullback.fst f y) ⋙ push l E (pullback.snd f y)).mapHomologicalComplex (.up ℤ)

/-- Addition in the point sum is computed componentwise.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: compose with every product projection. Each point inverse image is additive,
so it preserves sums; the projections jointly detect equality. -/
theorem pointSum_additive {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    (pointSum l E f y).Additive := by
  constructor
  intro M N a b
  apply (cancel_mono (piObjIso (fun x : Points f y ↦ pull l E x.val) N).hom).1
  apply Pi.hom_ext
  intro x
  simp only [Preadditive.add_comp, Category.assoc, piObjIso_hom_comp_π]
  change (pointSum l E f y).map (a + b) ≫
      (Pi.π (fun x : Points f y ↦ pull l E x.val) x).app N = _
  rw [NatTrans.naturality]
  simp only [Functor.map_add, Preadditive.comp_add]
  rw [NatTrans.naturality, NatTrans.naturality]

/-- The point-sum additive instance uses its separately named theorem.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
instance pointSumAdditive {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    (pointSum l E f y).Additive := pointSum_additive l E f y

/-- The degreewise finite point sum, with its own quotient transitions.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev D {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  (pointSum l E f y).mapHomologicalComplex (.up ℤ)

/-- The strict exchange chain map, natural in the whole representative.
Source: Stacks 0959 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def b {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    B l E f y ⟶ C l E f y :=
  NatTrans.mapHomologicalComplex (exchange l E f y) (.up ℤ)

/-- The strict germ chain map, natural in the whole representative.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers). -/
def r {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    C l E f y ⟶ D l E f y :=
  NatTrans.mapHomologicalComplex (restriction l E f y) (.up ℤ)

/-- Evaluation at coefficient n+1, before derived localization.
Source: Stacks 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev level (W : Scheme.{u}) (n : ℕ) :=
  (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)

/-- Sections at the identity object of the point's small pro-etale site.
Source: Stacks 03QU, 099B (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev sections (k : Type u) [Field k] (n : ℕ) :=
  (SheafOfModules.evaluation (integralCoefficientSheaf l E (Spec (.of k)) n)
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).mapHomologicalComplex (.up ℤ)

/-- Restriction of a whole strict system to completed coefficient modules.
Source: Stacks 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev restricted (W : Scheme.{u}) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)


attribute [local irreducible] b r exchange restriction square pointRestriction component

/-- The positive finite coefficient ring, with the same shift as the sequence site.
Source: Stacks 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev Ring (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- The section-preserving fixed-scalar presentation of a finite-level module sheaf.
Source: Stacks 00YV, 09A6 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def fixed (W : Scheme.{u}) (n : ℕ) :
    normalizedDVRModules l E W n ⥤
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) where
  obj M := ⟨ProEtale.moduleSectionPresheaf (Ring l E n) M,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) AddCommGrpCat.{u + 1})
      M.isSheaf⟩
  map φ := { hom :=
    { app := fun U ↦ (ModuleCat.restrictScalars
        ((ProEtale.finiteCoefficientIntrinsicScalarMap W (Ring l E n)).app U).hom).map
          (φ.val.app U)
      naturality := fun _ _ g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply φ.val g x } }

/-- Evaluation of strict systems as sheaves of modules over the discrete quotient ring.
Source: Stacks 0941, 00YV (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev fixedEvaluation (W : Scheme.{u}) (n : ℕ) :=
  coefficientSequenceEvaluation l E W n ⋙ fixed l E W n

attribute [local irreducible] fixed

/-- Direct-image evaluation is the very same sectionwise fixed-scalar functor.
Source: Stacks 03D6, 0941 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: at (n,U), both sides are the sections at (n,X ×_Y U). Restricting the
constant scalar action commutes with the constant-section coefficient homomorphism.
The maps on these sections and on all vertical arrows are identical. -/
theorem fixedDirect_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    push l E f ⋙ fixedEvaluation l E Y n =
      fixedEvaluation l E X n ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f := by
  sorry

/-- Inverse-image evaluation is uniquely fixed by the evaluated ordinary unit.
Source: Stacks 03D7, 0941 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: the inverse-image generator and its relations give the finite-level
inverse image. The displayed unit equation fixes its value on every generator.
Sheafification extends it uniquely; the inverse generator construction gives an
inverse. This also proves naturality and uniqueness of the normalized comparison. -/
theorem fixedPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! ξ : pull l E f ⋙ fixedEvaluation l E X n ≅
      fixedEvaluation l E Y n ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f,
      ∀ M : coefficientSequenceModules l E Y,
        (fixedEvaluation l E Y n).map ((adj l E f).unit.app M) ≫
          (eqToIso (fixedDirect_eq l E f n)).hom.app ((pull l E f).obj M) ≫
          (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).map
            (ξ.hom.app M) =
        (ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).unit.app
            ((fixedEvaluation l E Y n).obj M) := by
  sorry

/-- The canonical evaluation comparison, selected by its unique unit normalization.
Source: Stacks 03D7, 0941 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def fixedPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (fixedPull_existsUnique l E f n).choose

/-- The ProEtale exchange uses the ordinary composition comparison and its counit mate.
Source: Stacks 0959, 07A7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def proExchange {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (n : ℕ) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) y ⟶
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y) ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y) :=
  (mateEquiv
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y))
    (TwoSquare.mk _ _ _ _
      ((ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.snd f y) y).inv ≫
        eqToHom (congrArg (ProEtale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))))
          (pullback.condition (f := f) (g := y)).symm) ≫
        (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.fst f y) f).hom))).natTrans

/-- The ProEtale point component is pullback of the specified h-counit.
Source: Stacks 03QP, 03D7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def proComponent {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (n : ℕ)
    (x : Points f y) :
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y) ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y) ⟶
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) x.val :=
  Functor.whiskerLeft
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y))
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerLeft
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y))
        ((ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) s).inv ≫
          eqToHom (congrArg (ProEtale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))))
            (pullback.lift_snd x.val (𝟙 s)
              (x.property.trans (Category.id_comp y).symm)).symm) ≫
          (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
            (lift f y x) (pullback.snd f y)).hom) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y)).counit
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (lift f y x)) ≫
      (Functor.leftUnitor _).hom) ≫
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
      (lift f y x) (pullback.fst f y)).inv ≫
    eqToHom (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))))
      (pullback.lift_fst x.val (𝟙 s) (x.property.trans (Category.id_comp y).symm)))

/-- The existing canonical etale finite exchange, with its recorded counit normalization.
Source: Stacks 0959, 07A7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
abbrev etExchange {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (n : ℕ) :=
  Etale.baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
    (CommSq.mk (pullback.condition (f := f) (g := y)))

/-- The Etale point component is pullback of the specified h-counit.
Source: Stacks 03QP, 03D7 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def etComponent {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (n : ℕ)
    (x : Points f y) :
    Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y) ⋙
      Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y) ⟶
    Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) x.val :=
  Functor.whiskerLeft
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y))
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerLeft
        (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y))
        ((Etale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) s).inv ≫
          eqToHom (congrArg (Etale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))))
            (pullback.lift_snd x.val (𝟙 s)
              (x.property.trans (Category.id_comp y).symm)).symm) ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
            (lift f y x) (pullback.snd f y)).hom) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.snd f y)).counit
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (lift f y x)) ≫
      (Functor.leftUnitor _).hom) ≫
    (Etale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
      (lift f y x) (pullback.fst f y)).inv ≫
    eqToHom (congrArg (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))))
      (pullback.lift_fst x.val (𝟙 s) (x.property.trans (Category.id_comp y).symm)))

attribute [local irreducible] proExchange proComponent etComponent

/-- The evaluated exchange is precisely the canonical fixed-scalar exchange.
Source: Stacks 0959, 07A7 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: transpose both sides under the finite-level h-adjunction. The unit
normalization of fixedPull identifies the two transposes with v* of the actual
f-counit. The normalized composition comparison identifies the two square maps.
Injectivity of the adjunction correspondence gives the displayed equality. -/
theorem fixedExchange {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (n : ℕ) (M : coefficientSequenceModules l E X) :
    (fixedEvaluation l E s n).map ((exchange l E f y).app M) ≫
      (eqToIso (fixedDirect_eq l E (pullback.snd f y) n)).hom.app
        ((pull l E (pullback.fst f y)).obj M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
        (pullback.snd f y)).map ((fixedPull l E (pullback.fst f y) n).hom.app M) =
    (fixedPull l E y n).hom.app ((push l E f).obj M) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) y).map
        ((eqToIso (fixedDirect_eq l E f n)).hom.app M) ≫
      (proExchange l E f y n).app ((fixedEvaluation l E X n).obj M) := by
  sorry

/-- Evaluation retains each specified point counit, not merely its endpoints.
Source: Stacks 03QP, 03D7 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: apply the unit normalization of fixedPull to the h-adjunction and take
its counit equation. Pull back by i_x. The identity and composition normalizations
identify h i_x and v i_x with the identity and x, respectively. -/
theorem fixedComponent {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (n : ℕ) (x : Points f y) (M : coefficientSequenceModules l E X) :
    (fixedEvaluation l E s n).map ((component l E f y x).app M) ≫
      (fixedPull l E x.val n).hom.app M =
    (eqToIso (fixedDirect_eq l E (pullback.snd f y) n)).hom.app
        ((pull l E (pullback.fst f y)).obj M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
        (pullback.snd f y)).map ((fixedPull l E (pullback.fst f y) n).hom.app M) ≫
      (proComponent l E f y n x).app ((fixedEvaluation l E X n).obj M) := by
  sorry

open ProEtale in
/-- The ordinary comparison direct image has the counit-mate normalization.
Source: Stacks 09A6, 07A7 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: take mates of the canonical inverse-image comparison. The composition
comparison on direct images is fibre-product pasting; the two successive mate
identities give exactly lowerStarComparisonUpperStarBaseChange and this counit equation. -/
theorem comparisonCounit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))) :
    (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).obj M) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).map
        ((ProEtale.lowerStarComparisonUpperStarBaseChange f
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))).app M) ≫
      (ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).counit.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) X).obj M) =
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) X).map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).counit.app M) := by
  let Λ := ULift.{u + 1} (Ring l E n)
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) M
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj M) ≫ t) h

/-- Both actual finite arrows agree with their etale counterparts under comparison.
Source: Stacks 09A6, 0959, 03QP (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: transpose the exchange square and apply comparisonCounit for f and h.
The comparison pullback coherence identifies the resulting square maps. Apply
the same counit equation to h and pull back by each i_x; identity and composition
coherence identify its source and target. These are equalities of natural sheaf
maps, so termwise application and localization retain the specified arrows. -/
theorem comparisonArrows {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (n : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))) :
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) s).map
      ((etExchange l E f y n).app M) ≫
      (ProEtale.lowerStarComparisonUpperStarBaseChange (pullback.snd f y)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))).app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.fst f y)).obj M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
        (pullback.snd f y)).map
        ((ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y)).inv.app M) =
    (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) y).inv.app
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f).obj M) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) y).map
        ((ProEtale.lowerStarComparisonUpperStarBaseChange f
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))).app M) ≫
      (proExchange l E f y n).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) X).obj M)) ∧
    (∀ x : Points f y,
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) s).map
        ((etComponent l E f y n x).app M) ≫
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) x.val).inv.app M =
      (ProEtale.lowerStarComparisonUpperStarBaseChange (pullback.snd f y)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))).app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.fst f y)).obj M) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.snd f y)).map
          ((ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
            (pullback.fst f y)).inv.app M) ≫
        (proComponent l E f y n x).app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) X).obj M)) := by
  sorry

/-- Exactness on the two finite-level sites and on whole strict systems.
Source: Stacks 03QP, 09A8 (blueprint: lem-zl-finite-counit-restriction-towers). -/
def DirectExact {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  PreservesFiniteLimits (push l E f) ∧ PreservesFiniteColimits (push l E f) ∧
  PreservesFiniteLimits
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f) ∧
  PreservesFiniteColimits
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f) ∧
  PreservesFiniteLimits
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f) ∧
  PreservesFiniteColimits
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) f)

/-- Both quotient squares commute as actual chain maps, with semilinearity explicit.
Source: Stacks 03D7, 0941 (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: a map of module sheaves on the sequence site is natural on horizontal
arrows as well as vertical arrows. Apply that naturality in every cochain degree
and then the definition of coefficientSequenceTransition. Its restricted target
action is exactly normalizedDVRModuleRes; no localization is involved. -/
theorem transitionSquares {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (T : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (m n : ℕ) (h : n ≤ m) :
    (level l E s m).map ((b l E f y).app T) ≫
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E s h) (.up ℤ)).app
        ((C l E f y).obj T) =
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E s h) (.up ℤ)).app
        ((B l E f y).obj T) ≫
      ((normalizedDVRModuleRes l E s h).mapHomologicalComplex (.up ℤ)).map
        ((level l E s n).map ((b l E f y).app T)) ∧
    (level l E s m).map ((r l E f y).app T) ≫
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E s h) (.up ℤ)).app
        ((D l E f y).obj T) =
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E s h) (.up ℤ)).app
        ((C l E f y).obj T) ≫
      ((normalizedDVRModuleRes l E s h).mapHomologicalComplex (.up ℤ)).map
        ((level l E s n).map ((r l E f y).app T)) := by
  constructor
  · apply HomologicalComplex.hom_ext
    intro j
    exact (coefficientSequenceTransition l E s h).naturality
      (((b l E f y).app T).f j)
  · apply HomologicalComplex.hom_ext
    intro j
    exact (coefficientSequenceTransition l E s h).naturality
      (((r l E f y).app T).f j)

/-- The actual germ at the identity point of an algebraically closed field.
Source: Stacks 03QU (blueprint: lem-zl-finite-counit-restriction-towers). -/
def etGerm (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (M : Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))) :=
  (Scheme.pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber
    (Scheme.Etale.mk (𝟙 (Spec (.of k)))) (Over.homMk (𝟙 _) (Category.comp_id _)) M.obj

/-- Sections on the etale point are identified with its stalk by the actual germ.
Source: Stacks 03QT, 03QU (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: the absolute Galois group of an algebraically closed field is trivial.
Its etale topos is sets; the sections-to-stalk germ is the identity under this
equivalence. This remains true for addition and the finite coefficient action. -/
theorem etGerm_isIso (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (M : Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))) : IsIso (etGerm l E k n M) := by
  let p := Scheme.pointSmallEtale (𝟙 (Spec (.of k)))
  let I := Scheme.Etale.mk (𝟙 (Spec (.of k)))
  let z : p.fiber.Elements := ⟨I, Over.homMk (𝟙 _) (Category.comp_id _)⟩
  have hz : IsInitial z := by
    apply IsInitial.ofUniqueHom
      (fun a ↦ CategoryOfElements.homMk z a
        (MorphismProperty.Over.homMk a.2.left a.2.w) (by
          apply Over.OverMorphism.ext
          exact Category.id_comp _))
    intro a g
    apply Subtype.ext
    apply MorphismProperty.Over.Hom.ext
    have h := congrArg (fun t ↦ t.left) g.property
    exact (Category.id_comp _).symm.trans h
  exact isIso_ι_of_isTerminal hz.op ((CategoryOfElements.π p.fiber).op ⋙ M.obj)

/-- The etale point component on stalks is the actual finite stalk restriction.
Source: Stacks 03QP (blueprint: lem-zl-finite-counit-restriction-towers).
Proof: stalkRestrict_eq_counit' identifies restriction with the stalk of the
h-counit. Apply upperStarCompSheafFiberIso to i_x and v and use h i_x = id,
v i_x = x. Naturality and the normalized inverse-image composition give this equation. -/
theorem etComponent_stalk (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Spec (.of k) ⟶ Y) (n : ℕ)
    (x : Points f y)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))) :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.map
        ((etComponent l E f y n x).app M) ≫
      (Etale.upperStarCompSheafFiberIso
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) x.val
        (𝟙 (Spec (.of k)))).hom.app M ≫
      eqToHom (congrArg (fun z ↦ (Scheme.pointSmallEtale z).sheafFiber.obj M)
        (Category.id_comp x.val)) =
    Etale.stalkRestrict (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
        (pullback.snd f y) (𝟙 (Spec (.of k)))
        ⟨lift f y x, pullback.lift_snd _ _ _⟩
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n)))
          (pullback.fst f y)).obj M) ≫
      (Etale.upperStarCompSheafFiberIso
        (ModuleCat.{u + 1} (ULift.{u + 1} (Ring l E n))) (pullback.fst f y)
        (lift f y x)).hom.app M ≫
      eqToHom (congrArg (fun z ↦ (Scheme.pointSmallEtale z).sheafFiber.obj M)
        (pullback.lift_fst _ _ _)) := by
  sorry

/-- Descent includes the factorization on every complex, not just an isomorphism
between unspecified endpoints. Source: Stacks 04VG, 04VK
(blueprint: lem-zl-finite-counit-restriction-towers). -/
def Descent {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) : Prop :=
  ∃ (B' C' D' : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E s)
    (β : B' ⟶ C') (ρ : C' ⟶ D')
    (eB : B l E f y ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ B')
    (eC : C l E f y ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ C')
    (eD : D l E f y ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D'),
    (∀ T : CochainComplex (coefficientSequenceModules l E X) ℤ,
      DerivedCategory.Q.map ((b l E f y).app T) ≫ eC.hom.app T =
        eB.hom.app T ≫ β.app (DerivedCategory.Q.obj T)) ∧
    (∀ T : CochainComplex (coefficientSequenceModules l E X) ℤ,
      DerivedCategory.Q.map ((r l E f y).app T) ≫ eD.hom.app T =
        eC.hom.app T ≫ ρ.app (DerivedCategory.Q.obj T))

end WeilConjectures.FiniteCounitTowers

namespace WeilConjectures.FiniteCounitTowers

attribute [local irreducible] b r exchange restriction square pointRestriction component
  CoefficientReductionPresentation

/-- Finite exchange and counit restrictions form strict isomorphism towers.
Source: Stacks Project, etale-cohomology.tex, Tags 0959 and 03QP; proetale.tex,
Tags 09A8 and 09AL (blueprint: lem-zl-finite-counit-restriction-towers).

Proof:
1. Finite base change makes h finite. Schemes of finite type over the field k are
locally Noetherian, so f and h are locally finitely presented. Their geometric
lifts are the finite set in the finite stalk formula
(lem-weil-pbc-finite-stalk-formula-restriction).
2. lem-zl-finite-fp-proetale-pushforward-exact and
lemma-weil-pbc-finite-direct-image-exact make both finite direct images exact.
prop-weil-pbc-proetale-constant-exact makes all finite inverse images exact.
Thus termwise operations compute the derived operations, on unbounded models too.
3. The exchange is the transpose of v* applied to the f-counit; each point
component applies i_x* to the h-counit. The formula on an inverse-image generator
is a tensor [V,phi,m] mapped to a times the restriction of m along phi. It is
additive and linear. Naturality in the differential gives precisely b and r.
4. The quotient map sends a times a restricted section to the reduced scalar
times the restricted image section. Hence both quotient squares commute as chain
maps. This holds for all successive quotients, and exact scalar restriction
makes the resulting maps linear over the completed coefficient sheaf.
5. Each reduction of K is bounded constructible. The constructible comparison
(sk-thm-pe-constructible-comparison) supplies an etale antecedent. This is used
only to prove invertibility, not as a hypothesis on the individual terms of Q.
6. lem-weil-pbc-discrete-exchange-site-comparison identifies localized b with
the canonical etale finite exchange, normalized as the counit mate.
lem-pur-exact-derived-mate identifies the derived mate with the actual termwise
one. Tag 0959 makes that exchange invertible.
7. lem-pe-direct-image-mate-compatibility identifies the actual h-counit under
site comparison; lem-pe-inverse-image-comparison-coherence identifies its point
pullbacks. lem-sc-derived-adjunction-from-underived reads these counits termwise.
8. The finite stalk formula and the equivalence of the etale topos of Spec k
with sets identify this map with the product of the point germs. Sections and
the identity geometric stalk agree. A finite product of modules is its direct
sum, including the empty zero product. Thus r is a quasi-isomorphism.
9. The same restriction formula commutes with all maps of representatives.
Change of rings preserves quasi-isomorphisms between flat-term K-flat models
(lem-pur-change-of-rings-kflat-quasi-iso). Exact geometric operations and scalar
restriction preserve these quasi-isomorphisms. K-flat replacement and
lem-pur-kflat-map-factorization compute roofs with these models; localization
therefore gives natural maps independent of the representative.
10. Cohomology of strict systems is levelwise. Thus b and r are quasi-isomorphisms
of system complexes and of their restricted towers. Exact point sections gives
the evaluated assertion. Localization and total derived inverse limit preserve
the resulting isomorphisms.
-/
theorem finiteCounitRestrictionTowers
    (F : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of F.k)) (aY : Y ⟶ Spec (.of F.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsFinite f] (hf : f ≫ aY = aX)
    (y : Spec (.of F.k) ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q)
    (hflat : ∀ j : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
        (Q.X j))
    (eQ : DerivedCategory.Q.obj Q ≅ K) :
    Finite (Points f y) ∧
    (∀ n : ℕ, DirectExact l E f n ∧ DirectExact l E (pullback.snd f y) n) ∧
    Descent l E f y ∧
    (∃ (T : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (κ : ∀ n : ℕ,
        (level l E X n).obj T ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (eT : (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj T),
        CoefficientReductionPresentation l E X
          (CoefficientDerivedSystemFibers.toCoefficientDerivedSystemReduction
            (CoefficientDerivedSystemCalculus.toCoefficientDerivedSystemFibers
              (coefficientDerivedSystemEvaluationCalculus l E X).choose))
          Q hQ T eT κ) ∧
    (∀ (T : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (κ : ∀ n : ℕ,
        (level l E X n).obj T ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (eT : (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj T),
      CoefficientReductionPresentation l E X
        (CoefficientDerivedSystemFibers.toCoefficientDerivedSystemReduction
            (CoefficientDerivedSystemCalculus.toCoefficientDerivedSystemFibers
              (coefficientDerivedSystemEvaluationCalculus l E X).choose))
        Q hQ T eT κ →
      (∀ n : ℕ,
        QuasiIso ((level l E (Spec (.of F.k)) n).map ((b l E f y).app T)) ∧
        QuasiIso ((level l E (Spec (.of F.k)) n).map ((r l E f y).app T)) ∧
        QuasiIso ((sections l E F.k n).map
          ((level l E (Spec (.of F.k)) n).map ((b l E f y).app T))) ∧
        QuasiIso ((sections l E F.k n).map
          ((level l E (Spec (.of F.k)) n).map ((r l E f y).app T)))) ∧
      QuasiIso ((b l E f y).app T) ∧ QuasiIso ((r l E f y).app T) ∧
      QuasiIso ((restricted l E (Spec (.of F.k))).map ((b l E f y).app T)) ∧
      QuasiIso ((restricted l E (Spec (.of F.k))).map ((r l E f y).app T)) ∧
      IsIso (DerivedCategory.Q.map ((b l E f y).app T)) ∧
      IsIso (DerivedCategory.Q.map ((r l E f y).app T)) ∧
      IsIso (DerivedCategory.Q.map
        ((restricted l E (Spec (.of F.k))).map ((b l E f y).app T))) ∧
      IsIso (DerivedCategory.Q.map
        ((restricted l E (Spec (.of F.k))).map ((r l E f y).app T))) ∧
      (IsEmpty (Points f y) → IsZero ((D l E f y).obj T)) ∧
      IsIso ((coefficientSequenceLimit l E (Spec (.of F.k))).map
        (DerivedCategory.Q.map ((b l E f y).app T))) ∧
      IsIso ((coefficientSequenceLimit l E (Spec (.of F.k))).map
        (DerivedCategory.Q.map ((r l E f y).app T)))) := by
  sorry

end WeilConjectures.FiniteCounitTowers
