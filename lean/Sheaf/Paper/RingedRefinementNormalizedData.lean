/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedRefinementAssembly
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! Normalized ringed refinement construction and comparison obligations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

private def ordinaryOperation {T : Scheme.{u}} (c : Coefficients .ordinary T)
    {U V : Over T} (f : U ⟶ V) (R : Rings .ordinary T) :
    Operation.{u} (baseChange .ordinary f.left) ((c.rings V).obj R) ((c.rings U).obj R) := by
  letI : (proEtaleBaseChange f.left).IsContinuous
      (topology .ordinary V.left) (topology .ordinary U.left) :=
    baseChange_continuous .ordinary f.left
  let RV : Rings .ordinary V.left := (c.rings V).obj R
  let RU : Rings .ordinary U.left := (c.rings U).obj R
  let rc := (c.pull f).app R
  let ψ := (⟨Functor.whiskerRight
    (proEtaleRingDirectImageMap f.left RV RU rc).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
    (sheafCompose (ProEt.topology V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV ⟶
    ((proEtaleBaseChange f.left).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology V.left) (ProEt.topology U.left)).obj
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
  let adj := (proEtaleRingModuleOperations_properties.{u} f.left RV RU rc).2.2.2.2.some
  let : (SheafOfModules.pushforward.{u + 1} ψ).IsRightAdjoint := adj.isRightAdjoint
  let e := (SheafOfModules.pullbackPushforwardAdjunction.{u + 1} ψ).leftAdjointUniq adj
  let : (SheafOfModules.pushforward.{u + 1} ψ).Additive :=
    inferInstanceAs (proEtaleRingModuleDirectImage f.left RV RU rc).Additive
  let : (SheafOfModules.pullback.{u + 1} ψ).Additive :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1} ψ).left_adjoint_additive
  let : PreservesFiniteLimits (proEtaleRingModulePullback f.left RV RU rc) :=
    (proEtaleRingModuleOperations_properties f.left RV RU rc).2.2.1
  let : PreservesFiniteLimits (SheafOfModules.pullback.{u + 1} ψ) :=
    preservesFiniteLimits_of_natIso e.symm
  let : Abelian.HasKInjectiveResolutions (Mod ((c.rings U).obj R)) :=
    proEtaleRingModules_hasKInjectiveResolutions U.left RU
  exact { coefficient := ψ }

private theorem ordinaryOperation_coefficient {T : Scheme.{u}} (c : Coefficients .ordinary T)
    {U V : Over T} (f : U ⟶ V) (R : Rings .ordinary T) :
    (ordinaryOperation c f R).coefficient =
      ⟨Functor.whiskerRight (c.structural f R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
  rfl

/-- Existence of the normalized operations and comparison data, before asserting
any refinement or coefficient coherence.
Source: Stacks 03D7, 03DI, 06YY, 07A6; Bhatt--Scholze 6.7.6--6.7.7 supplement,
construction steps 2--4 (blueprint: lem-pur-ringed-refinement-normalized-data).

Proof: use canonical sheaf inverse image for the rings. The adjoint of its
composition isomorphism is the structural ring map in `canonicalCoefficients`.
The module Kan extension and sectionwise direct image give the module adjunction;
exact inverse image and K-injective resolutions give `Calculus.operation`.
For an open immersion, transport localized exact extension along the canonical
restriction comparison; the ordinary open unit is invertible. Choose the scalar
universal pairs from derived change of rings and normalize their ordinary units
by `1 tensor x`. Sectionwise associativity of direct image gives `Spatial` and
its conjugate pullback comparisons. The identity-on-sections scalar restriction
square gives the ordinary scalar/pullback comparison by conjugation. On common
flat-term K-flat resolutions, its termwise tensor comparison descends to `pull`
with the required representative equation. The balanced scalar associators and
units are those of successive derived quotient normalization. Construct beta and
delta by the open-unit transposes of open tensor normalization. Finally the exact
product decomposition for the two clopen components gives pi as (identity, zero).
All constructions take place on the vertical site as well as the ordinary site;
no evaluation is used to detect equality of derived maps. -/
theorem exists_normalizedRefinementData (m : Mode) (T : Scheme.{u}) :
    ∃ (o : Calculus (canonicalCoefficients m T)) (p : Spatial o)
      (_sc : ScalarComparisons o) (_ac : ScalarComposition o),
      Nonempty (OpenComparisons p) := by sorry

end SheafOfModules.RingedRefinement
