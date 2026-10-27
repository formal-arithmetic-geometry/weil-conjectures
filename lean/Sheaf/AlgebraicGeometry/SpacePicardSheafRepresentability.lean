/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.SpacePicardPresentation
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # The unpointed Picard sheaf of a proper flat algebraic space

Source: Stacks Project, quot.tex, Situation 0D25 and Proposition 0D2C;
moduli.tex, Lemma 0DNI, with the standing hypotheses of section-picard-functor
(blueprint: lem-sfb-space-picard-sheaf-representability).

The representative presentation identifies Q with the fppf sheafification of
T ↦ Pic(X_T). No section or geometric-integrality hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fppf sheafification of line classes is a quasi-separated, locally finitely
presented commutative group algebraic space.
Source: Stacks, Tags 0D25, 0D2C and 0DNI
(blueprint: lem-sfb-space-picard-sheaf-representability).

Proof:
1. By lem-sfb-space-coherent-stack-general, coherent families form an algebraic
   stack locally of finite presentation. Its line-module substack is representable
   open by lem-sfb-space-invertible-open-coherent. Apply
   lem-sfb-open-stack-algebraic-lfp; properness supplies separatedness.
2. Automorphisms of a line are multiplication by global units. The universal
   structure-map hypothesis identifies these with units on T, so inertia is G_m,T.
   Affine locally it is Spec A[z,w]/(zw-1), finitely presented and formally smooth:
   across a square-zero ideal, lifts a,b with ab=1+i have corrected inverse b(1-i).
   By lem-sfb-stack-chartwise-smooth-etale-calculus inertia is flat and locally
   of finite presentation.
3. Apply lem-sfb-flat-inertia-algebraic-space-quotient. Its isomorphism-class
   sheaf is exactly the fppf sheafification of T ↦ Pic(X_T). By
   lem-weil-pbc-site-sheafification-sections-local, sections have local line
   representatives and equal classes are locally isomorphic; these are exactly
   the locally_represented and locally_equal fields of SpacePicardPresentation.
   Thus the Picard stack is a gerbe over Q, without choosing a section of f.
4. A smooth surjective scheme atlas U of the Picard stack has U → S locally
   finitely presented. By lem-sfb-gerbe-smooth-universal-homeomorphism the composite
   U → Q is surjective, flat and locally finitely presented. Source locality in
   lem-sfb-representable-fppf-etale-open-descent gives local finite presentation
   of Q → S.
5. Base change preserves finite presentation by lem-sfb-space-flat-proper-fp-locality.
   Apply lem-sfb-space-module-isom-affine to each pair of line families on X_T:
   their isomorphism space is affine and finitely presented over T. This makes
   the Picard stack diagonal quasi-compact. Apply lem-sfb-gerbe-qc-diagonal-descent
   to obtain quasi-compactness of the relative diagonal of Q → S.
6. Tensor local line representatives and glue their classes. Local equality of
   representatives makes this independent of choices, and the sheaf condition
   gives a unique glued section. The trivial module and duals give identity and
   inversion. All group laws hold on representatives and hence locally everywhere.
   Restriction is canonical tensor pullback. Natural operations on a representing
   space are space morphisms, and lem-trf-space-fibre-products-etale-covers
   identifies the product sheaf with Q ×_S Q. These give CommutativeSpaceGroup,
   with its operations pinned by tensor_class, unit_class and inverse_class. -/
theorem space_picard_sheaf_representability {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ groupSpaceBase S) (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : ProperQuotFinitePresentation f)
    (hO : ∀ T : ProperQuotTest (groupSpaceBase S),
      IsIso (moduleStructureMap (properQuotSnd f T))) :
    ∃ (Q : AlgebraicSpace S) (G : CommutativeSpaceGroup Q),
      Nonempty (SpacePicardPresentation f Q G) ∧
      MapIsQuasiCompact (pullback.diagonal (groupSpaceProjection Q).hom.hom) ∧
      MapIsLocallyOfFinitePresentation (groupSpaceProjection Q) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
