/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Spectral.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality
import Sheaf.AlgebraicGeometry.InvariantClosedSubstackDescent
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus

/-! # Spectral point spaces of quasi-compact stacks with quasi-compact diagonal

Source: Stacks Project, Morphisms of Stacks, Tag 0DQN
(blueprint: lem-sfb-qc-stack-spectral-point-space).

The base is affine. The diagonal is relative to this base, using the canonical
projection to the based category of the identity functor on `Over S`. Points and
their topology are the existing field-object quotient and smooth-atlas topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry

namespace CategoryTheory

/-- A quasi-compact algebraic stack over an affine scheme, with quasi-compact relative
 diagonal, has a spectral point space, including when it is empty.
Source: Stacks Project, Morphisms of Stacks, Tag 0DQN
(blueprint: lem-sfb-qc-stack-spectral-point-space).

Proof:
1. By lem-sfb-algebraic-stack-quasicompact-surjection choose an affine smooth
surjective atlas A. Its point map is continuous and surjective by
lem-sfb-stack-point-topology, and open by
lem-sfb-stack-chartwise-smooth-etale-calculus (smooth implies flat and locally finitely
presented) and lem-sfb-stack-point-topology-flat-lfp-open. A is quasi-compact by
lem-weil-pbc-affine-scheme-qcqs, so pulling back open covers and using surjectivity
shows that the stack point space is quasi-compact.
2. By lem-pc-fppf-affine-open-cover, affine opens B in A form a basis. Their images
are open, quasi-compact, and form a basis of the stack topology. Every quasi-compact
open is a finite union of such images; the corresponding open substacks exist by
lem-sfb-smooth-atlas-open-image.
3. For affine opens B and C, the scheme B ×_S C is affine since S is affine, by
lem-weil-pbc-fibre-product-affine-spectra, and quasi-compact by
lem-weil-pbc-affine-scheme-qcqs. By def-trf-scheme-algebraic-space and
lem-sfb-stack-diagonal-space-source-representability, B ×_F C is an algebraic space
and a base change of the relative diagonal. Its quasi-compact atlas supplied by
def-sfb-stack-qcqs-morphism makes its point space quasi-compact. Its image is exactly
the intersection of the two images: equal field-point classes become isomorphic over
a common extension and give an object of the 2-fibre product. Finite unions now give
quasi-compactness of intersections of arbitrary quasi-compact opens.
4. For a nonempty irreducible closed T, use lem-sfb-space-reduced-closed-support to
construct the reduced closed subscheme D of A over T. On A ×_F A its two pullbacks
are reduced by lem-sfb-space-smooth-reduced-locality and have equal support, so are
equal by uniqueness. By lem-sfb-invariant-closed-substack-descent they descend to a
reduced closed substack Z. Its point space is T by lem-sfb-stack-point-topology and
lem-sfb-stack-closed-immersion-calculus.
5. The diagonal of a full substack is a base change of the original diagonal, so
Z has quasi-compact diagonal and inertia. By
lem-sfb-reduced-qc-inertia-dense-open-gerbe choose a dense open gerbe U over a space Q.
Its relative diagonal is again quasi-compact; U need not be quasi-compact.
6. By lem-sfb-gerbe-smooth-universal-homeomorphism the point spaces of U and Q are
homeomorphic. By lem-sfb-gerbe-qc-diagonal-descent, Q has quasi-compact diagonal, so
lem-sfb-quasiseparated-space-sober applies. Its nonempty irreducible point space has
a unique generic point, giving one in U.
7. Density makes that point generic in T. Every other generic point of T lies in
the nonempty open U and is generic there, so uniqueness in U proves uniqueness in T.
Together with steps 1--3 this is def-weil-spectral-space. For the empty stack the
compact-open basis and sobriety conditions hold vacuously, and compactness also holds. -/
theorem qcStack_spectral_pointSpace {S : Scheme.{u}} [IsAffine S]
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (hqc : IsQuasiCompactModuli F)
    (hdiag : IsQuasiCompactAlgebraicModuliMap.{u, v, w, v, max w u, v', w'}
      (moduliRelativeDiagonal
        (G := BasedCategory.ofFunctor (𝟭 (Over S))) ⟨F.p, rfl⟩)) :
    SpectralSpace (ModuliPoints F) := by
  sorry

end CategoryTheory
