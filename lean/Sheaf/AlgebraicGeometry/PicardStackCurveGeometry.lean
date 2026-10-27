/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.LineBundleModuli
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CoherentStackAlgebraicLfp
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.SquareZeroPicardObstruction
import Sheaf.AlgebraicGeometry.StackInfinitesimalSmoothCriterion
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Algebraicity and smoothness of the stack of line bundles

Source: Stacks Project, quot.tex, Tag 0D04 (proposition-pic); moduli.tex,
Tags 0DMB (lemma-pic-qs-lfp) and 0DPJ (lemma-pic-curves-smooth)
(blueprint: lem-sfb-picard-stack-curve-geometry).

The stack is the actual category of invertible modules and tensor-pullback
isomorphisms. Algebraicity holds without a fibre-dimension restriction;
smoothness is conditional on the bound on every scheme-theoretic fibre.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The stack of line bundles of a proper flat finitely presented scheme family is
algebraic; it is smooth over the base if every fibre has dimension at most one.
No section, universal equality of structure-sheaf direct images, smoothness of the
family, reducedness of its fibres, or Noetherian hypothesis is assumed.
Source: Stacks, quot.tex, Tag 0D04; moduli.tex, Tags 0DMB and 0DPJ
(blueprint: lem-sfb-picard-stack-curve-geometry).

Proof:
1. Properness gives separatedness (def-weil-proper-morphism). By
   lem-sfb-coherent-stack-algebraic-lfp the coherent-family stack is algebraic
   and locally of finite presentation. The same pullback-isomorphism arrows
   define the open inclusion of line bundles given by
   lem-sfb-invertible-open-in-coherent-stack. Apply
   lem-sfb-open-stack-algebraic-lfp to get algebraicity and a locally finitely
   presented atlas composite for the line-bundle category.
2. Assume the fibre bound. For an affine first order thickening T into T', pull
   the family back to T and T'. Flatness, properness and finite presentation
   persist by lem-sfb-space-flat-proper-fp-locality and
   def-trf-scheme-algebraic-space. Local fibre dimensions agree by
   lem-sc-fibre-dimension-after-base-change. They are at most one, since the
   entire original fibre is a neighbourhood of each point (def-kun-dimension).
   Intersect a chain of irreducible closed subsets of a new fibre with any
   neighbourhood of a point in its smallest member. Each intersection is dense
   in its member, so strictness persists. Thus every chain has length at most
   one. The pullback thickening has square-zero ideal I by
   lem-weil-pbc-first-order-thickening-base-change. Its ideal is quasi-coherent
   (def-sbc-closed-immersion-ideal-sheaf), also over the closed fibre, since
   locally J tensor_B B/J = J/J² = J.
3. Apply lem-sfb-proper-quasicoherent-fibre-dimension-vanishing with d=1 to
   obtain R²g_*I=0. The affine-base comparison
   lem-pc-cohomology-sections-affine-base gives H²(X_T,I)=0. Properness supplies
   its quasi-compactness and separatedness hypotheses.
4. By lem-sfb-square-zero-picard-obstruction, vanishing of this obstruction
   implies that every line-bundle class extends. Choose a representative of
   a preimage class; equality of Picard classes supplies the required actual
   restriction isomorphism. This is an arrow in the line-bundle category.
5. This proves essential surjectivity for every affine first order restriction.
   Apply lem-sfb-stack-infinitesimal-smooth-criterion, with local finite
   presentation from step 1. It gives precisely a smooth surjective scheme
   atlas with smooth composite to S. -/
theorem picard_stack_curve_geometry {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f] :
    IsAlgebraicModuliStack (LineBundleModuli.category f) ∧
      ((∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) →
        IsSmoothModuliStack (LineBundleModuli.category f)) := by
  sorry

end AlgebraicGeometry
