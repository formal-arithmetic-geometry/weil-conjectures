/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceEventualClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension

/-! # Finite finitely presented envelopes of separated étale morphisms

Source: Stacks Project, More on Morphisms of Spaces, Tags 082K and 0874
(blueprint: lem-sfb-space-etale-finite-fp-envelope).

Étaleness is tested on compatible étale scheme charts. Finiteness and open immersion
are representable properties on all scheme tests. Finite presentation includes both
quasi-compactness and quasi-separatedness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact separated étale map to a qcqs algebraic space factors through a
finite finitely presented algebraic space by a quasi-compact representable open immersion.
Source: Stacks Project, More on Morphisms of Spaces, Tags 082K and 0874
(blueprint: lem-sfb-space-etale-finite-fp-envelope).

Proof, following the seven steps of the node:
1. The chartwise calculus [lem-sfb-stack-chartwise-smooth-etale-calculus] makes f locally
   finitely presented and preserves its étaleness under scheme base change. Separatedness
   persists by [lem-sfb-space-separated-fp-composition]. Apply
   [lem-a1-separated-etale-space-scheme] to these base changes: f is representable.
2. Étale scheme charts are unramified [def-weil-etale-morphism] and locally quasi-finite
   [lem-weil-pbc-unramified-quasi-finite-at-points]. Apply
   [lem-sfb-space-relative-integral-factorization] and
   [lem-sfb-space-normalization-quasifinite-locus] to identify W with an open of its
   relative normalization N. The integral map N to T has qcqs source by
   [lem-sfb-space-integral-qcqs-permanence]. The inclusion is quasi-compact by
   [lem-sfb-space-qc-cancellation].
3. Write N as a directed limit of finite finitely presented spaces N_i over T using
   [lem-sfb-integral-space-finite-presentation-limit]. Its sheaf limit agrees by
   [lem-sfb-space-affine-limits-schematic-stages]. A quasi-compact atlas of N pulls back
   to a quasi-compact atlas of W, using [lem-sfb-space-quasicompact-affine-tests] and
   the chartwise calculus. Apply [lem-sfb-space-limit-open-cover-descent] to the cover
   (W,N), obtaining a quasi-compact open V_i of N_i whose inverse image is W.
4. On the directed tail, the pullbacks V_k of V_i are qcqs with affine transitions by
   open-cover descent. Their sheaf limit is W by affine limits. Apply
   [lem-sfb-space-eventual-closed-immersion] to the identity of W: the projection
   b : W to V_k is a closed immersion for some k. Put C = N_k and V = V_k.
5. The open V to C is quasi-compact by [lem-sfb-space-qcqs-permanence] and finitely
   presented by [lem-sfb-space-qc-open-finite-presentation]. Composition and the chartwise
   calculus make V to T locally of finite type. By [lem-sfb-space-relative-lfp-permanence],
   b is locally finitely presented. Its quasi-coherent ideal I, from
   [lem-sfb-space-ideal-closed-subspace-correspondence], is of finite type by
   [lem-sfb-space-closed-structure-finite-presentation].
6. Extend I to a finite-type quasi-coherent submodule J of O_C by
   [lem-sfb-space-finite-type-submodule-extension]. Scalar multiplication makes J an ideal.
   Form Y = V(J) inside C using the ideal/closed-subspace correspondence. Its pullback
   over V has ideal I and is W. Thus j : W to Y is a representable open immersion,
   and its composite into C is the fixed map over T.
7. The closed immersion Y to C is finitely presented by the closed-structure criterion;
   composition gives finite presentation of pi : Y to T. On affine scheme tests, pi is
   Spec(A/J) to Spec(R) with A a finite R-module, so A/J is finite too
   [def-weil-closed-immersion, def-weil-finite-integral-morphism]. Hence pi is finite,
   affine and separated [lem-sfb-space-affine-locality]. Since j followed by pi equals
   f, [lem-sfb-space-qc-cancellation] makes j quasi-compact. -/
theorem exists_finite_finitePresentation_envelope_of_etale
    {S : Scheme.{u}} {W T : AlgebraicSpace S} (f : W ⟶ T)
    (hTqc : IsQuasiCompact T.obj) (hTqs : IsAbsolutelyQuasiSeparated T)
    (hfqc : MapIsQuasiCompact f.hom.hom) (hfsep : MapIsSeparated f)
    (hfet : MapIsLocally (@Etale) f) :
    ∃ (Y : AlgebraicSpace S) (j : W ⟶ Y) (π : Y ⟶ T),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom ∧
      MapIsQuasiCompact j.hom.hom ∧
      IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) π.hom.hom ∧
      MapIsLocallyOfFinitePresentation π ∧ MapIsQuasiCompact π.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal π.hom.hom) ∧ j ≫ π = f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
