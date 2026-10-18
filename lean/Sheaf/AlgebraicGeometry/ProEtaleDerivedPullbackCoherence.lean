/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Associativity of canonical finite-coefficient derived pro-etale pullback comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
`lemma-derived-pullback-composition`, its K-flat representative computation and the
associativity of inverse-image comparisons
(blueprint: lem-trf-derived-pullback-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Canonical derived pullback comparisons for three scheme morphisms are associative.
The inverse of `proEtaleConstantRingPullbackComposition` is the comparison `c` in the
node: the selected `proEtaleCanonicalPullbackComposition`, transported along the equality
between composite and canonical constant-section coefficient identifications. Thus its
termwise K-flat normalization is retained. The displayed transport identifies the two
parenthesizations of the triple scheme morphism; the functor associator has identity
components, so the target objects in the two paths agree definitionally.
Source: Stacks Project, Tag 0D6D and Modules on Sites, Tag 03D8
(blueprint: lem-trf-derived-pullback-coherence).
Proof: (1) Apply `lem-trf-constant-coefficient-composition` to all four pairs
(j,h), (h,k), (j,hk), and (hj,k). The canonical coefficient identification of each
composite is therefore the one required by the composition lemma, even on an empty
source (`prop-weil-pbc-proetale-constant-ring-map`).
(2) Construct the ordinary direct-image comparisons by restriction along canonical
fibre-product pasting isomorphisms (`def-pc-fibre-product` and
`def-weil-pbc-proetale-operations`). The two triple expansions preserve the same
projections and agree by the fibre-product universal property. Their scalar actions
agree by step (1), giving the right-adjoint coherence equation.
(3) Conjugate these comparisons under the normalized module adjunctions, using
`def-weil-pbc-composite-adjunction` and `lem-weil-pbc-conjugate-iso-unit-equation`.
The unit equation characterizes the ordinary comparison, whose tensor formula sends
m tensor r to (m tensor 1) tensor r; balancing gives its inverse.
(4) Apply `lem-trf-adjoint-composition-coherence` to the six adjunctions and invert
its equality. This gives the ordinary pullback comparison cocycle, with associator.
(5) Resolve M by a K-flat complex P with flat terms (`lem-pc-kflat-resolution`).
Successive pullbacks remain K-flat with flat terms by
`lem-weil-pbc-ringed-pullback-preserves-kflat`. The normalization in
`lem-weil-pbc-proetale-derived-pullback-composition` identifies each derived comparison
with its termwise ordinary comparison. Apply step (4) degreewise and localize to obtain
the equality on Q(P); naturality makes these degree maps complex maps.
(6) Both paths are natural in M. Apply naturality to the resolution isomorphism
Q(P) to M and cancel its image under the triple pullback to obtain the claimed equality.
No boundedness or flatness hypothesis on the scheme morphisms is used. -/
theorem proEtaleConstantRingDerivedPullback_composition_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A] (M : proEtaleDerivedCategory X A) :
    (proEtaleConstantRingPullbackComposition j (h ≫ k) A).inv.app M ≫
        (proEtaleConstantRingDerivedPullback A j).map
          ((proEtaleConstantRingPullbackComposition h k A).inv.app M) =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (proEtaleConstantRingPullbackComposition (j ≫ h) k A).inv.app M ≫
        (proEtaleConstantRingPullbackComposition j h A).inv.app
          ((proEtaleConstantRingDerivedPullback A k).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
