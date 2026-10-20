/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Paper.ModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.Paper.CompletedCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Sheaf.Paper.StratifiedLattice
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CoefficientHeartFiltration
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.Paper.CartesianCoefficients
import Sheaf.SixFunctors.ScalarSixPullback

/-!
# Reduction of a proper direct-image bound to integral lattices on strata

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-reduction.md and its proof
(blueprint: det-proper-heart-bound-reduction).

The auxiliary predicates only spell out this node's hypotheses and conclusion. All modules,
locally closed extensions, scalar extensions and higher direct images use existing definitions.
The bound is tested in nonnegative degrees; negative right derived functors are zero by the
node's convention, so this includes every integer c, including negative c.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The assertion `R^q p_* M = 0` for every integer q > c. Nonnegative q use Mathlib's
right derived functors; the negative ones are zero by convention and impose no condition.
In particular, c < 0 still tests degree zero.
Source: blueprint sk-lem-proper-heart-bound-reduction, definition of R^q p_*
(blueprint: det-proper-heart-bound-reduction). -/
def ProperHeartHigherVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ)
    (M : pulledBackModuleObjects Λ X) : Prop :=
  ∀ q : ℕ, c < (q : ℤ) → IsZero (((CondensedRing.lowerStar Λ p).rightDerived q).obj M)

/-- Ordinary localization of an integral coefficient module, along the actual pulled-back
inclusion O_F → F of condensed coefficient rings. This is F_X ⊗_{O_F,X} M.
Source: blueprint sk-lem-proper-heart-bound-reduction, notation N[1/ell]
(blueprint: det-proper-heart-bound-reduction). -/
def properHeartRationalization (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) :=
  Mod.extendScalars (coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ F)) X)

/-- This node's reduction assertion, before supplying the standing geometric hypotheses.
Its premise tests all locally closed immersions, every finite F containing E (also F = E),
and every pro-etale locally finite free integral lattice, in all three coefficient categories.
Its conclusion tests every constructible module over E or the finite-subextension-valued
condensed algebraic closure. Source: blueprint sk-lem-proper-heart-bound-reduction, all clauses
(blueprint: det-proper-heart-bound-reduction). -/
def ProperHeartBoundReductionAssertions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X Y : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Y) (c : ℤ) : Prop :=
  (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F →
    ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L₀ : pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ F) S),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F) L₀ →
      ProperHeartHigherVanishing (Profinite.padicIntegersRingObj ℓ F) p c
        ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
          a ha).obj L₀) ∧
      ProperHeartHigherVanishing (Profinite.continuousMapRingObj F) p c
        ((properHeartRationalization ℓ F X).obj
          ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
            a ha).obj L₀)) ∧
      ProperHeartHigherVanishing (Profinite.padicAlgClRingObj ℓ) p c
        ((Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X)).obj
          ((properHeartRationalization ℓ F X).obj
            ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
              a ha).obj L₀)))) →
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)],
    (Λ = Profinite.padicSubfieldCondensedRing ℓ E ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) →
    ∀ M : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ProperHeartHigherVanishing (coefficientHeartRingObj Λ) p c M.obj

/-- A uniform proper direct-image bound for integral lattices extended from strata, their
localizations, and their algebraic-closure scalar extensions implies the same bound for
every constructible E- or Qbar_l-module. The Noetherian instance in the assertion is derived
from finite type over k, without imposing any additional geometric hypothesis.

Source: blueprint sk-lem-proper-heart-bound-reduction.md and its proof, Extensions, Strata,
Lattices (blueprint: det-proper-heart-bound-reduction).

Proof plan (the seven steps of the DAG node):
1. Module categories over the actual coefficient sheaves are Grothendieck abelian
(prop-pur-kinjective-resolutions-exist) and have enough injectives
(lem-sp-grothendieck-enough-injectives). The additive left exact lower star
(def-sfb-module-lower-star) has the long exact sequence of
lem-weil-pbc-derived-functor-long-exact. Thus the bound is stable under extensions and,
by induction, finite filtrations. Negative derived degrees vanish by convention.
2. Finite type over the Noetherian field makes X Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Every locally closed stratum and its closure
is again separated and finite type over k: use quotient charts and finitely many
localization charts, since Noetherian opens are quasi-compact
(lem-weil-pbc-noetherian-open-subscheme-noetherian). The diagonal criterion gives
separatedness; lem-weil-pbc-locally-noetherian-quasi-separated gives qcqs.
3. sk-prop-sfb-qlbar-colimit-x identifies F_X with O_F,X[1/ell]. The balanced tensor
universal property identifies tensoring with F_X with the filtered ell-localization
colimit, hence it is exact. lem-sfb-subfield-flat and lem-sfb-qlbar-flat give exactness
of field scalar change. def-sfb-left-derived-exact identifies derived and ordinary
scalar change, allowing det-prop-scalar-six-pullback to be used on sheaves.
4. sk-lem-coefficient-heart gives a finite adapted lisse stratification. For Qbar_l,
sk-thm-sfb-qlbar-two-colimit descends each lisse restriction to a finite field F0.
Replace F0 by its finite compositum with E; scalar transitivity identifies the
extension with the original lisse sheaf. For E-coefficients take F = E.
5. sk-lem-stratified-lattice gives integral lisse lattices after finite stratification.
Composition of locally closed immersions follows from their quotient descriptions.
det-lem-coefficient-heart-common-stratification orders a refinement with open prefixes.
Restriction preserves local free bases by sk-prop-sfb-cartesian-coefficients and
preserves scalar comparisons by det-prop-scalar-six-pullback.
6. Factor each stratum through its closure as open followed by closed. These maps
and the complementary opens are quasi-compact by step 2. Apply
det-sf-open-closed-sequence-ring-sheaf to both pairs: open extension and closed
pushforward are exact for O_F, F and Qbar_l. Hence locally closed extension is exact.
det-prop-scalar-six-pullback now gives ordinary sheaf-level scalar comparisons.
7. det-lem-coefficient-heart-filtration gives quotients b_!(M|T) along the ordered
strata. Step 6 identifies them with localized extended lattices for E, and their
Qbar_l scalar extensions otherwise. The premise applies to every quotient;
the finite-filtration induction of step 1 proves the conclusion. -/
theorem properHeartBoundReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (r : ℕ) [Fact r.Prime] [CharP k r] (_hrℓ : r ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (c : ℤ) :
    @ProperHeartBoundReductionAssertions ℓ _ E X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
      p c := by
  sorry

end AlgebraicGeometry.ProEtale
