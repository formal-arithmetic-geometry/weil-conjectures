/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Admissible integral lattices for smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest,
`sbc-def-admissible-lattices`
(blueprint: sbc-def-admissible-lattices).
The integral object and its rationalization isomorphism are data. Both admissibility
conditions are properties, and the output condition uses one interval for every level
and all four ambient operations, with intrinsic constructibility at each cohomology sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (T : Scheme.{u}) [IsNoetherian T]
variable (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
variable (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- An integral object with a chosen isomorphism in the raw rational category.
There are no retained finite-level origins. Source: blueprint,
`sbc-def-admissible-lattices`, integral lattice clause
(blueprint: sbc-def-admissible-lattices). -/
structure IntegralLattice (K : PbcRationalDerivedCategory l E T hdim hl) where
  /-- The integral constructible derived-complete object. -/
  integral : PbcIntegralCategory l E T hdim hl
  /-- The specified identification after raw scalar localization. -/
  rationalization : (pbcRationalization T (pbcIntegralDatum l E)
    (pbcUniformizer l E)).obj integral ≅ K

/-- The derived reduction along the actual completed-ring projection, transported
through the canonical associated-module-sheaf equivalence. The index is n+1.
Source: blueprint, `sbc-def-admissible-lattices`, finite-level reduction clause
(blueprint: sbc-def-admissible-lattices). -/
def IntegralLattice.reduction {K : PbcRationalDerivedCategory l E T hdim hl}
    (L : IntegralLattice l E T hdim hl K) (n : ℕ) :
    PbcWitnessAmbient T (pbcIntegralDatum l E) n :=
  ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence).inverse.obj
    ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj L.integral.obj)

/-- Each reduction has a bounded constructible étale origin, asserted only as a
property. The origin and its isomorphism are existential witnesses.
Source: blueprint, `sbc-def-admissible-lattices`, finite-level-etale-admissible clause
(blueprint: sbc-def-admissible-lattices). -/
def IntegralLattice.IsFiniteLevelEtaleAdmissible
    {K : PbcRationalDerivedCategory l E T hdim hl}
    (L : IntegralLattice l E T hdim hl K) : Prop :=
  ∀ n : ℕ, ∃ M : Etale.BoundedConstructibleDerivedCategory
      (PbcQuotient (pbcIntegralDatum l E) n) T,
    Nonempty ((comparisonUpperStar
      (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj
        M.obj ≅ L.reduction l E T hdim hl n)

/-- Intrinsic constructibility of every cohomology sheaf and vanishing outside [a,b].
The stratification is allowed to depend on the individual degree and object.
Source: blueprint, `sbc-def-admissible-lattices`, four-output condition
(blueprint: sbc-def-admissible-lattices). -/
def sbcIntrinsicConstructibleIn (Z : Scheme.{u}) (P : Type (u + 1))
    [CommRing P] [Finite P] (a b : ℤ)
    (K : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} P))) : Prop :=
  ∀ i : ℤ,
    IsConstructibleProEtaleFixedModuleSheaf Z P
      ((DerivedCategory.homologyFunctor _ i).obj K) ∧
    ((i < a ∨ b < i) → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))

/-- Finite-level étale admissibility together with one nonempty cohomological window
for Rg_*, Lf* Rg_*, Le*, and Rh_* Le*, at all positive coefficient levels.
Constructibility is intrinsic on the four output schemes, with no common strata.
Source: blueprint, `sbc-def-admissible-lattices`, square-constructibly admissible clause
(blueprint: sbc-def-admissible-lattices). -/
def IntegralLattice.IsSquareConstructiblyAdmissible
    {X Y S : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S}
    (_sq : ChosenCartesianSquare h e f g) [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    {K : PbcRationalDerivedCategory l E T hdim hl}
    (L : IntegralLattice l E T hdim hl K) : Prop :=
  L.IsFiniteLevelEtaleAdmissible l E T hdim hl ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      sbcIntrinsicConstructibleIn S (PbcQuotient (pbcIntegralDatum l E) n) a b
        ((pbcWitnessDirectImage g (pbcIntegralDatum l E) n).obj
          (L.reduction l E T hdim hl n)) ∧
      sbcIntrinsicConstructibleIn X (PbcQuotient (pbcIntegralDatum l E) n) a b
        ((pbcWitnessPullback f (pbcIntegralDatum l E) n).obj
          ((pbcWitnessDirectImage g (pbcIntegralDatum l E) n).obj
            (L.reduction l E T hdim hl n))) ∧
      sbcIntrinsicConstructibleIn Y (PbcQuotient (pbcIntegralDatum l E) n) a b
        ((pbcWitnessPullback e (pbcIntegralDatum l E) n).obj
          (L.reduction l E T hdim hl n)) ∧
      sbcIntrinsicConstructibleIn X (PbcQuotient (pbcIntegralDatum l E) n) a b
        ((pbcWitnessDirectImage h (pbcIntegralDatum l E) n).obj
          ((pbcWitnessPullback e (pbcIntegralDatum l E) n).obj
            (L.reduction l E T hdim hl n)))

end AlgebraicGeometry.Scheme
