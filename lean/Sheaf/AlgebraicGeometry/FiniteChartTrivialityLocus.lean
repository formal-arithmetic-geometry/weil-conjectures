/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.Algebra.Group.Submonoid.Operations

/-!
# Triviality locus of a fine saturated log structure

The geometric chart argument in the extracted criterion of ILO VI 1.4 and
VIII 3.4.1--3.4.3 (blueprint: lem-trf-finite-chart-triviality-locus).
This statement concerns only openness, chart equations, and restrictions of sections;
it makes no domain or monoidal ideal contraction assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The triviality locus of an fs log structure is open, is the principal open of
any finite chart generating list, and all log sections restrict there to units.
Source: the geometric chart argument underlying ILO VI 1.4, printed p. 69, and
VIII 3.4.1--3.4.3, printed p. 110; parent proof steps 3, 4, and 6
(blueprint: lem-trf-finite-chart-triviality-locus).

Proof: at a geometric point a chart presents the stalk as the pushout of its
monoid with the ring units. Its characteristic is trivial if and only if every
chart generator maps to a unit. Indeed the chart with units generates the stalk;
conversely trivial characteristic means every element is associated to 1, hence
is a unit, whose structural image is a ring unit. A finite additive generating
list reduces this condition to its entries. A germ of a regular function is a
unit at a geometric point if and only if its residue is nonzero. Locality of the
germ maps and the injective extension of residue fields prove this criterion.
Thus on the chart the locus is D of the product of those entries, including
D(1) for the empty list. Étale maps are open, so the images of these principal
opens, taken over the fs chart cover, show that the locus is open in X. The
canonical comparison between ring-valued stalks and the affine pointed colimit
respects every ring germ; the structural morphism factors through each pointed
affine chart. Pullback of its principal open therefore gives D of the product
of the strict-henselization chart images. Finally, on this locus every log germ
is a unit. The log axiom identifies its structural image with a unit of the
local ring. The inverses of a restricted section exist locally, agree by
uniqueness, and glue to a global inverse on the pullback of the locus. -/
theorem FineSaturatedLogScheme.finiteChart_trivialityLocus
    (X : FineSaturatedLogScheme.{u}) :
    ∃ U : X.scheme.Opens,
      (U : Set X.scheme) = X.logStructure.trivialityLocus ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
        (P : Type u) [AddCancelCommMonoid P] (W : X.scheme.Etale)
        (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (c : Multiplicative P →* X.logStructure.monoidSheaf.obj.obj (op W)),
        IsAffine W.left → X.logStructure.IsChart W c →
        ∀ (r : ℕ) (p : Fin r → P), AddSubmonoid.closure (Set.range p) = ⊤ →
          W.hom ⁻¹' (U : Set X.scheme) =
            (W.left.basicOpen (∏ i : Fin r,
              X.logStructure.alpha.app (op W) (c (Multiplicative.ofAdd (p i)))) :
                Set W.left) ∧
          Scheme.strictHenselizationStructuralMap t ⁻¹' (U : Set X.scheme) =
            ((PrimeSpectrum.basicOpen (∏ i : Fin r,
              X.logStructure.chartStrictHenselizationMap t W w c
                (Multiplicative.ofAdd (p i)))).carrier :
                Set (Spec (Scheme.strictHenselizationRing t)))) ∧
      ∀ (W : X.scheme.Etale) (m : X.logStructure.monoidSheaf.obj.obj (op W)),
        IsUnit ((pullback.fst W.hom U.ι).appTop (X.logStructure.alpha.app (op W) m)) := by
  sorry

end AlgebraicGeometry
