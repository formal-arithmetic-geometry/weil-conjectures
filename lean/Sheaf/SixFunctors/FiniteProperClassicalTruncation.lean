/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage

import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.SixFunctors.UnboundedClassicalTruncation
import Sheaf.AlgebraicGeometry.ProperHeartContinuitySections
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# A uniform truncation window for proper classical direct images

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, paragraphs "Etale statements" and "Transfer"
(blueprint: lem-sfb-finite-proper-classical-truncation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical good-truncation map induces an isomorphism on degree-`m` total proper
pushforward, with the same window after every base change. The coefficient category is
ordinary, uncompleted, unbounded constant-ring modules; classicality concerns every
cohomology sheaf, without any boundedness assumption.

Source: blueprint main-20261015, sk-prop-ctf-finite-proper-localizing.proof.md,
"Etale statements" and "Transfer" (blueprint: lem-sfb-finite-proper-classical-truncation).

Proof plan:
1. Fix `S -> Y` and an affine weakly contractible `W -> S`. The scheme
   `Z = X_S ×_S W` is an object over `X_S` by det-pe-topos-functoriality-inverse-image.
   Properness survives base change by lem-pc-proper-base-change, and the fibre bound
   remains `e`. Apply lem-sfb-finite-proper-classical-neighborhood-vanishing to obtain
   vanishing above `2e` for every classical module sheaf on `Z`.
2. Restrict `J` to `L` on `Z`. The arbitrary discrete-coefficient inverse-image comparison
   sk-thm-pe-direct-image-comparison and det-pe-classical-sheaves-modules make `L`
   classical. By lem-sfb-proetale-object-inverse-image-restriction this inverse image is
   exact restriction, so kernels, cokernels and the canonical maps of def-kun-truncations
   identify the restriction of the good truncation with the good truncation of `L`.
3. Evaluation at `W` is exact by det-proper-heart-continuity-sections. Choose a
   K-injective representative `I` using sk-def-sfb-derived-categories. The sectionwise
   direct-image formula def-weil-pbc-proetale-operations gives `(f_* I)(W) = I(Z)`.
   By lem-sfb-unbounded-sections-localization and lem-weil-proetale-weakly-etale-localization
   this computes derived sections of `L`. Thus evaluation of output cohomology is
   `H^m RΓ(Z,L)`, naturally in `J` and in its canonical truncation map.
4. Apply clause (2) of det-pe-unbounded-classical-truncation on `Z` at its terminal object,
   using the bound `2e` from step 1 and classicality from step 2. The inequality is
   precisely `N < m - 2e - 1`. The evaluated map is therefore invertible. Clause (3) of
   det-pe-sections-conservative makes the sheaf map invertible. Its naturality follows
   from the truncation natural transformation and the two functors applied to it.
   Since `S` was arbitrary, the same `e` and inequality work after every base change. -/
theorem finiteProper_classical_truncation
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (S : Scheme.{u}) (g : S ⟶ Y)
    (J : Scheme.proEtaleDerivedCategory (pullback f g) A)
    (_hJ : IsClassicalModuleComplex J)
    (m N : ℤ) (_hN : N < m - 2 * (e : ℤ) - 1) :
    IsIso ((DerivedCategory.homologyFunctor _ m).map
      ((Scheme.proEtaleConstantDerivedDirectImage (pullback.snd f g) A).map
        ((CategoryTheory.Triangulated.TStructure.truncGEπ
          DerivedCategory.TStructure.t N).app J))) := by
  sorry

end AlgebraicGeometry.ProEtale
