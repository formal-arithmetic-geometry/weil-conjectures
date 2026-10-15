/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constructibility and vanishing in the proper case

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-proper-case.md` (blueprint: thm-fin-proper-case).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- For a proper morphism to a finite-type scheme over a field, higher direct images
of a constructible sheaf with finite allowable coefficients are constructible. If all
geometric fibres have dimension at most `d`, these sheaves vanish in degrees above `2 * d`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-proper-case.md`
(blueprint: thm-fin-proper-case).

Proof:
1. Properness includes finite type (def-weil-proper-morphism). Compose finite affine
   covers of the base and source to see that X is finite type over k
   (def-weil-finite-type-morphism). No separatedness of S over k is needed.
2. Pull the inverse of N back from S to X. Apply
   thm-fin-proper-constructibility-complete and def-finrepair-property-c to obtain
   constructibility of every nonnegative higher direct image of F.
3. For every geometric point s, pull back the finite affine cover. The rings of the
   fibre charts are tensor products (lem-weil-pbc-fibre-product-affine-spectra), finitely
   generated over the algebraically closed field. The fibre has dimension at most d
   by hypothesis, and N remains invertible on it.
4. Pull back the constructible stratification of F (prop-constructible-pullback).
   Constructible preimages (lem-pur-scheme-constructible-preimage) ensure that its
   pulled-back parts remain constructible, so F restricted to the fibre is constructible
   in the sense of def-weil-pbc-constructible-complexes.
5. Constructibility implies finite geometric stalks (def-constructible-finite).
   The sheaf clause of cor-weil-pbc-geometric-fiber-finite identifies each geometric
   stalk of the higher direct image with the corresponding fibre cohomology group.
6. Apply fin4-lem-fibrewise-cohomological-dimension to the restricted sheaf to make
   these groups zero above 2d.
7. Geometric stalk conservativity (lemma-weil-pbc-geometric-stalk-conservative) makes
   the underlying abelian sheaf zero; the inverse of its zero map is automatically
   linear, so the module sheaf itself is zero. -/
theorem properCase_constructible_and_vanishing
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProper f]
    (d : ℕ)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)) ∧
    (∀ q : ℕ, 2 * d < q → IsZero (higherDirectImage Λ f (q : ℤ) F)) := by
  sorry

end AlgebraicGeometry.Etale
