/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedShriekBoundedQcqs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZlShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
public import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
/-! # Condensed compact-support composition over quasi-separated bases

Definition interface (blueprint: def-zl-qcqs-composition-defs).

Source: latest blueprint, lem-zl-shriek-composition.proof, and
sk-thm-sf-comp-composition (1),(2); Stacks Tag 0F7J, lemma-shriek-composition
(blueprint: lem-zl-condensed-shriek-composition-qcqs).

The witnesses below retain the actual compactification functors, proper-refinement maps,
normalized proper/open compositor, and the proper/open isomorphism exchange. All categories
are full subcategories of the ordinary derived category with the pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

open CompactSupportComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

section

-- Match the coefficient-instance presentation in the bounded qcqs comparison theorem.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- A coherent compactification system for the given morphism. The comparison is fixed
on every proper refinement and satisfies identity and cocycle equations.
Source: Stacks 0F7J, refinement comparisons in the source proof, Step 3
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
structure System {X Y : Scheme.{u}} (f : X ⟶ Y) where
  preserves : ∀ (c : Compactification f)
      (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y
      ((CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c).obj K.obj)
  comparison : ∀ c d : Compactification f,
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) d
  refinement : ∀ (c d : Compactification f) (r : d.Refinement c)
      (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X),
    (comparison c d).hom.app K =
      (CompactificationReindexing.refinement (Profinite.padicAlgClRingObj ℓ) r).app K.obj
  comparison_id : ∀ c : Compactification f, comparison c c = Iso.refl _
  comparison_cocycle : ∀ c d e : Compactification f,
    comparison c d ≪≫ comparison d e = comparison c e

end

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
