/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import Sheaf.Paper.OpenExtensionConstantModelConstructible
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.SixFunctors.OpenImmersionTensorProjection
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.ProperBaseChangeRational

/-! # Boundary vanishing of proper direct image of open extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
det-sf-comp-composition-interchange.proof.md, proof (3), closed-complement calculation
(blueprint: lem-sfb-proper-open-boundary-zero).

All functors act on ordinary unbounded derived categories of internal modules. The
input belongs to the bounded constructible finite-Tor full subcategory. The conclusion
is vanishing of the target object in the ambient derived category on the boundary.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The finite discrete ell-primary rings, ell-adic integers, finite ell-adic fields,
their integer rings, and the finite-subextension condensed algebraic closure, up to
isomorphism of ring objects. The separate rational and integral ground-field clauses
include Q_ell and Z_ell explicitly.

Source: blueprint main-20261015, sk-def-localizing-closure, coefficient list, with the
algebraic-closure convention of sk-def-sfb-qlbar-condensed. This item-owned specialization
is not the dependency's interface: it omits the all-continuous-map algebraic-closure case
of `IsLocalizingAdmissibleCoefficient`, as the item statement requires
(blueprint: lem-sfb-proper-open-boundary-zero). -/
def IsFiniteSubextensionLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image of extension by zero from the inverse image of an open has zero
restriction to the reduced closed complement.

Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, proof (3)
(blueprint: lem-sfb-proper-open-boundary-zero).

Proof plan (the six steps of this DAG node):
1. Form T = W times_{Ybar} Z, with closed projection a to W and proper projection r_Z
   to Z. Base change of open immersions and quasi-compact maps identifies the other
   open projection with j : U to W. The ranges of a and j are complementary. Closed
   immersions are proper, so Z and T stay separated and finite type over k. T need
   not be reduced. Use lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-open-immersion-base-change, lem-pc-quasi-compact-base-change,
   lem-weil-pbc-proper-fp-permanence and lem-sfb-finite-type-composition-base-change.
2. Mixed restriction vanishing in lem-sfb-condensed-support-derived-localization gives
   a^* j_! A = 0, with no reducedness requirement on T.
3. Exact termwise j_! commutes with cohomology by
   lem-weil-pbc-exact-functor-complex-cohomology. Extend the finite constant-model
   stratification by the zero model on the complement, using
   lem-sf-open-extension-zero-constant-model-constructible. These models are locally
   finitely presented by det-def-sfb-constructible-local-model, so both bounded
   constructibility conventions apply (sk-def-sfb-bounded-constructible and
   sk-def-sfb-constructible). The projection formula of
   lem-sfb-open-immersion-derived-tensor-projection and exact pullback from
   sk-prop-sfb-cartesian-coefficients preserve the Tor interval under j_!.
4. For finite ell-primary coefficients, det-thm-sfb-proper-base-change-finite, clause
   (2), identifies c^* Rr_* j_! A with R(r_Z)_* a^* j_! A.
5. For integer rings use det-thm-sfb-proper-base-change-integral, clause (3); for finite
   fields and the finite-subextension condensed algebraic closure use
   det-thm-sfb-proper-base-change-rational, clause (3). The ground field and its integer
   ring are the degree-one cases. This exhausts sk-def-localizing-closure.
6. Substitute step 2. The adjunction of sk-def-sfb-module-derived-pushpull makes the
   right derived pushforward preserve the terminal, hence zero, object. Thus the
   object on the boundary vanishes. No comparison map or localizing extension is asserted. -/
theorem proper_open_boundary_zero
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsFiniteSubextensionLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (W Ybar Y Z : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (r : W ⟶ Ybar) [IsProper r.left]
    (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (c : Z ⟶ Ybar) [IsClosedImmersion c.left] [IsReduced Z.left]
    (hc : Set.range c.left.base = (Set.range i.left.base)ᶜ)
    (A : ConstantModelConstructibleFiniteTor Λ (pullback r.left i.left)) :
    IsZero ((moduleObjectDerivedPullback Λ c.left).obj
      ((moduleObjectDerivedPushforward Λ r.left).obj
        ((openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory.obj
          A.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
