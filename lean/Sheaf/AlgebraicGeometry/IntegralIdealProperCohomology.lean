/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Proper cohomology for integral-ideal filtration factors

Source: Stacks Project, Tags 02O5 and 01YH.
(blueprint: lem-pc-e2-integral-ideal-proper-cohomology)
 -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Proper cohomology is finite for a filtration factor supported on an integral
closed subscheme of the source.

Source: Stacks Project, Cohomology of Schemes, proof of Proposition 30.19.1, Tag 02O5,
and Lemmas 30.12.5 and 30.12.6, Tags 01YH and 01YI.
(blueprint: lem-pc-e2-integral-ideal-proper-cohomology)

Proof: First X is Noetherian: the affine Noetherian base is Noetherian, and f is
proper, hence of finite type and quasi-compact. Closed subschemes of X are Noetherian,
so the quasi-coherent ideal specified by IdealSheafData is coherent. Induct on closed
integral supports, simultaneously in every cohomological degree. Smaller-support
coherent modules reduce by the support-preserving filtration of 01YF to integral
ideals on strictly smaller closed subschemes. Finiteness in all degrees has the
two-out-of-three property by the long exact sequence over the Noetherian base ring:
for the left term use the segment starting in degree q - 1 (zero when q = 0), and
for the right term use the segment ending in degree q + 1. For Z closed in X, Chow's
lemma gives a
projective modification pi : Z' -> Z, an isomorphism on a dense open, together with a
closed immersion into projective space over the affine base. Choose a large common twist
L^n that kills positive higher direct images both for pi and for Z' -> T. Projective
cohomology finiteness, proved independently from the projective-space case, makes
G = pi_* L^n coherent with finite cohomology over T. Derived composition and the vanishing
identify its cohomology with that of L^n. Push G into X along the closed immersion; affine
pushforward is exact, so its cohomology remains finite. Its support is all of Z and its
generic stalk is one-dimensional over the residue field. The irreducible-support
argument of 01YH compares any nonzero ideal I on Z with this generic-rank-one module:
clear denominators to embed a nonzero ideal into G, then intersect with I. The cokernels
of these inclusions miss the generic point and have smaller support, so induction and
the long exact sequence give finiteness for i_* I. The zero ideal has zero cohomology.
All scalar actions are induced by f.appTop; all comparisons are linear for this action.
Empty integral schemes are excluded by IsIntegral, and the zero ideal is allowed. -/
theorem finite_H_pushforward_integral_ideal {X T : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) (q : ℕ) :
    letI : Module Γ(T, ⊤) (((pushforward i).obj I.toModules).H q) :=
      Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (((pushforward i).obj I.toModules).H q) := by sorry

end AlgebraicGeometry.Scheme.Modules
