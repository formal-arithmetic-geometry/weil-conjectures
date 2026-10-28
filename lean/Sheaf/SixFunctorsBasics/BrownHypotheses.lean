/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.SixFunctorsBasics.BrownHypothesesDefinitions

/-!
# Hypotheses of Brown representability

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses/_section.md.
The original arbitrary-field compactness assertion remains disputed. The bundle lives
in `BrownHypothesesDefinitions`; proved criteria and conditional obstructions live in
`BrownHypothesesCriteria`, which this unresolved assertion does not import.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

-- STATEMENT-DISPUTED: The arbitrary-field compactness assertion lacks a finiteness
-- hypothesis on the base field. The finite/rational compactness dependencies require
-- FiniteFieldDatum; the integral one requires an Ext bound. Finite type over an arbitrary
-- positive-characteristic field does not supply finite ℓ-cohomological dimension.
-- Concrete mathematical obstruction: take ell = 2, p = 3, X = Spec k for
-- k = algebraicClosure(F_3)(t_1,t_2,...) and Lambda the constant finite ring F_2.
-- The constant rank-one object is constructible of Tor amplitude [0,0]. Kummer cup
-- symbols in t_1,...,t_n are nonzero in H^n(k,F_2), detected by iterated residues.
-- Exact countable products make the coproduct of its positive shifts also their
-- product. The resulting map with every projection nonzero violates compactness.
-- This is a natural-language counterexample, not a claimed Lean field-cohomology proof.
-- Generation itself is proved without this finiteness assumption by the helpers above.
-- The supplied compactness theorem specifically uses D.k, the algebraic closure of a
-- finite field. Its algebraic-closure coefficient is finite-subextension-valued.
-- The supported geometric finite-field Brown bundle is proved in BrownHypothesesFiniteField;
-- its proof does not assert the original arbitrary-field claim.

/-- Brown representability hypotheses for a separated finite-type scheme in positive
characteristic different from the coefficient prime, for exactly the admissible rings.
`IsLocalizingAdmissibleCoefficient` specifies the six concrete coefficient objects up to
ring-object isomorphism, including the discrete finite rings killed by a power of `ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md and sk-lem-brown-hypotheses.proof.md
(blueprint: sk-lem-brown-hypotheses).

Proof: First unpack sk-def-sfb-dc-setting: the datum is a prime ℓ, a field of
characteristic p > 0 distinct from ℓ, and a separated finite-type k-scheme X.
Unpack sk-def-localizing-closure: Λ is one of the six specified condensed rings;
the ambient category is the unbounded derived category of modules over Λ_X;
S is the bounded constructible finite-Tor property and L is its replete localizing
intersection, with coproducts in the fixed universe and no completeness restriction.
Second apply det-brown-hypotheses-ambient to this datum to obtain local smallness,
triangulation, arbitrary sums and split idempotents of L. Apply
 det-brown-hypotheses-small to obtain thickness and essential smallness of S.
Choosing one representative per isomorphism class gives a small skeleton.
Third let G be any such skeleton and apply det-brown-hypotheses-generation:
each representative is compact in L, and vanishing of Hom(C[n], K) for all
representatives C and all integers n forces K to be zero. Compactness is exactly
def-pc-compact-object. To identify the second conclusion with def-pc-generators,
use Hom(coproduct C, K[-n]) = product Hom(C[n], K). If every morphism from the
coproduct into every shift of K is zero, the component Hom groups vanish,
so K is zero; contrapositively every nonzero K receives a nonzero map from the
coproduct into some shift. This is IsTriangulatedGeneratingFamily. All these
arguments apply to every small skeleton, with the inherited shift and any chosen
coproduct universal properties. -/
-- The final compactness input required by this unrestricted statement is unavailable
-- over an arbitrary positive-characteristic field; this remains the original named
-- obligation rather than importing the retired false witness.
theorem brownHypotheses
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  sorry

end CategoryTheory
