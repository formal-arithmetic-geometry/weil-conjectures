/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison

/-!
# Finiteness of proper direct images on the small etale site

Source: Stacks Project, Tag 095U (vanishing) and Tag 0GL0 (constructibility), with
identity compactification in the proper case.
(blueprint: lem-weil-pbc-etale-proper-direct-image-finiteness)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Proper direct images of constructible module sheaves are constructible and vanish
above twice the geometric fibre dimension. The Noetherian hypotheses mean finite affine
covers by spectra of Noetherian rings; finite dimensionality permits the empty scheme.
Source: Stacks Project, Tags 095U and 0GL0.
(blueprint: lem-weil-pbc-etale-proper-direct-image-finiteness)

Proof:
1. Finite affine Noetherian covers make X and Y locally Noetherian and quasi-compact
   (pqf-def-locnoeth, lem-sc-affine-noetherian-underlying-space); they are quasi-separated
   by lem-weil-pbc-locally-noetherian-quasi-separated. Properness gives separatedness and
   finite type, hence finite presentation over the locally Noetherian base
   (pqf-lem-lft-fp-locnoeth). The finite ring is Noetherian and annihilated by a positive N.
2. Choose the identity compactification (def-weil-pbc-projection-compactification).
   Identity extension by zero is the identity (def-weil-pbc-extension-by-zero).
   F in degree zero has bounded below constructible cohomology
   (def-weil-pbc-derived-categories, def-weil-pbc-etale-constructible-sheaf).
3. Apply lem-weil-pbc-etale-compactification-constructibility to this compactification.
   Since Rf_! is Rf_*, all higher direct images are constructible
   (def-weil-pbc-direct-image).
4. Every geometric fibre is finite type over an algebraically closed field
   (lem-pod-separated-finite-type-base-change). Embed an algebraic closure of the residue
   field in the geometric field (lem-weil-pbc-algebraic-extension-embeds-algebraically-closed).
   Dimension is unchanged by field extension (lem-sc-fibre-dimension-after-base-change).
   Apply lem-sf-separably-closed-torsion-cd and thm-sc-finite-type-torsion-cd to its
   N-torsion abelian sheaf: cohomology vanishes above 2e (def-sc-etale-torsion-cd).
   Transfer this to module cohomology by lem-weil-pbc-etale-module-cohomology-forget.
   On an empty fibre every module sheaf and all cohomology are zero.
5. Proper base change (cor-weil-pbc-geometric-fiber-finite) identifies geometric stalks
   with fibre cohomology. Sections on an algebraically closed point are stalks
   (lem-weil-pbc-geometric-point-cohomology), hence exact
   (prop-weil-pbc-geometric-stalks-exact). Exactness commutes with cohomology
   (lem-sp-exact-functor-preserves-homology); a pushed-forward injective resolution
   computes the fibre cohomology (def-weil-pbc-direct-image).
6. For q > 2e the underlying abelian higher direct image
   (lem-sbc-higher-direct-image-forget-comparison) has zero geometric stalks, so is zero
   by lemma-weil-pbc-geometric-stalk-conservative. Its module sheaf is therefore zero. -/
theorem proper_directImage_finiteness
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hXdim : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hYdim : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hfib : ∀ y : Y,
      topologicalKrullDim ↥(pullback f (Y.algClosurePoint y)) ≤ (e : WithBot ℕ∞))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℤ, 0 ≤ q → Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f q F)) ∧
    (∀ q : ℤ, (2 * e : ℤ) < q → IsZero (higherDirectImage Λ f q F)) := by
  sorry

end AlgebraicGeometry.Etale
