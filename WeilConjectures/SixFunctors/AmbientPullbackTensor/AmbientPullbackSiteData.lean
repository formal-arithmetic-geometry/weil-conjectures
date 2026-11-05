/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BundledTensorComparison
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryTensorPullbackData
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ambient constant-coefficient pullback and tensor coherence

Source: Stacks Project, sites-modules.tex, Tags 03D3 and 03EL; sites.tex, Tag 03CB;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-sf-ambient-pullback-site-constructions).

`some n` denotes the positive finite exponent n+1; `none` denotes the entire
semilinear system on the ringed sequence site. All system morphisms below live
on that site, including their horizontal restriction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor

/-- The original small site is small relative to the coefficient universe.
Source: Stacks 0941 (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: the pro-etale site has object universe t+1 and Hom universe t. Its product
with the countable poset has the same bound; take its small model and enlarge
only the coefficient universe. -/
@[instance] theorem siteSmall (X : Scheme.{t}) (s : Option ℕ) :
    EssentiallySmall.{max u (t + 1)} (Site X s) := by
  cases s <;> exact essentiallySmallSelf _

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Base change is continuous for vertical covers. Source: Stacks 03CB and 0941
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: pull back a vertical covering sieve at the same index, using continuity
of pro-etale base change. This works also on horizontal arrows by stability
of vertical covers under pullback. -/
@[instance] theorem baseContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (base f s).IsContinuous (topology Y s) (topology X s) := by
  cases s with
  | some n =>
    change (Scheme.proEtaleBaseChange f).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)
    infer_instance
  | none => exact ProEtale.VaryingRing.baseChange_continuous f

/-- The ring-sheaf inverse-image adjunction exists without identifying universes.
Source: Stacks 00VC and 03CB (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: use left Kan extension followed by sheafification on a coefficient-sized
small model of the site, and transport the adjunction back to the original site.
The product sequence site has the same size bound. -/
@[instance] theorem ringPushRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (ringPush.{t, u} f s).IsRightAdjoint := by
  have : PreservesFilteredColimitsOfSize.{max u (t + 1), max u (t + 1)}
      (CategoryTheory.forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink _
  let K := (equivSmallModel.{max u (t + 1)} (Site X s)).inverse.inducedTopology
    (topology X s)
  have : HasSheafify K CommRingCat.{max u (t + 1)} := by infer_instance
  have : HasSheafify (topology X s) CommRingCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite (topology X s) CommRingCat.{max u (t + 1)}
  have : ∀ P : (Site Y s)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)},
      (base f s).op.HasLeftKanExtension P := by
    intro P
    have : ∀ U : (Site X s)ᵒᵖ,
        HasColimitsOfShape (CostructuredArrow (base f s).op U)
          CommRingCat.{max u (t + 1)} := fun _ ↦
      hasColimitsOfShape_of_essentiallySmall _ _
    infer_instance
  unfold ringPush
  infer_instance

/-- The ordinary adjoint exists on the same ringed site. Source: Stacks 03D7
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: apply module pullback existence in the coefficient universe containing
both site universes, using free presentations followed by module sheafification.
The unit is the usual insertion m ↦ m tensor 1. -/
@[instance] theorem pushRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (push ell E f s).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (moduleRingUnit ell E f s)

attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

attribute [local irreducible] sequencePushEvaluation

attribute [local irreducible] sequencePullEvaluation

end WeilConjectures.AmbientPullbackTensor
