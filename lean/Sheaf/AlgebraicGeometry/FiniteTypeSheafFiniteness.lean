/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons

import Sheaf.AlgebraicGeometry.CompactifiableOverField
/-!
# Finiteness of finite-type direct images of constructible etale sheaves

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`sbc-thm-finiteness-finite-type.md` (blueprint: sbc-thm-finiteness-finite-type).

The ordinary direct image requires no separatedness. For the compact-support clauses,
use the Nagata compactification already supplied by `compactSupportAmplitudeCompactification`.
On the degree-zero input this candidate agrees with compactification-independent compact
support by `lem-amb-etale-compact-comparisons`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Direct image of a finite constructible etale module sheaf along a finite-type map of
finite-type schemes over a field is bounded constructible. For a separated map the compact
support direct image is also bounded constructible, and its cohomology vanishes above twice
a bound on the dimensions of the original geometric fibres.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/sbc-thm-finiteness-finite-type.md`
(blueprint: sbc-thm-finiteness-finite-type).

Proof, following the node's five steps:
1. The coefficient convention gives a finite commutative ring killed by positive N invertible
in k, hence on every k-scheme. Place F in degree zero; it is bounded constructible by
`def-weil-pbc-constructible-complexes`. Apply `thm-dg-finite-type-constructibility` to obtain
the ordinary direct-image assertion, including nonseparated maps.
2. For separated f, finite type over the Noetherian field makes X and Y Noetherian
(`lem-weil-pbc-finite-type-over-noetherian`); local Noetherianity makes Y quasi-separated
(`lem-weil-pbc-locally-noetherian-quasi-separated`). Use `thm-nagata-compactification` and
`def-nagata-compactification` to factor f as an open immersion j followed by a proper r.
Properness includes finite type (`def-weil-proper-morphism`). Finite affine covers and the
union of algebra generators show the compactification is finite type over k, hence Noetherian.
All three schemes admit finite Noetherian affine covers. No bound on the compactified fibres
is required.
3. By `lem-fin-extension-by-zero`, j_!F is constructible. Place it in degree zero and apply
`lem-fin-proper-bounded-constructible` to r to obtain bounded constructibility of Rr_*(j_!F).
4. By `def-amb-etale-compact-support`, the chosen candidate is Rr_* Dj_!. Its localization
normalization identifies Dj_!(F[0]) with (j_!F)[0]. The bounded-below comparison of
`lem-amb-etale-compact-comparisons` identifies this with compactification-independent Rf_!F.
Isomorphisms preserve cohomology, constructibility, and vanishing, giving the second clause.
5. The additive order m of 1 in the finite ring is positive, divides N, and is its additive
exponent: multiplication by m kills each ring element, and any annihilator kills 1. This
also holds for the zero ring with m = 1. Since N is invertible, so is m on Y. Apply
`lem-dg-compact-support-amplitude` to F and the original geometric-fibre bound to obtain
R^q f_! F = 0 for q > 2d. -/
theorem finiteType_directImages_finiteConstructible
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    DerivedCategory.isBoundedConstructible Λ Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((_root_.DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)) ∧
    ∀ [IsSeparated f],
      DerivedCategory.isBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (compactSupportAmplitudeCompactification k Y f)).obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)) ∧
      ∀ (d : ℕ),
        (∀ y : Y, topologicalKrullDim
          (↑(pullback f (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
              Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞)) →
        ∀ (q : ℤ), 2 * (d : ℤ) < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
              ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
                (compactSupportAmplitudeCompactification k Y f)).obj
                ((_root_.DerivedCategory.singleFunctor
                  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
