/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Source-coordinate naturality of the derived comparison

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-derived-base-change-source-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Changing both source coordinates, and transporting the coefficient arrow, conjugates
its derived comparison by isomorphisms. This statement concerns arbitrary commutative
squares, not open restrictions or the invertibility of the comparison.
Source: Stacks Project, cohomology.tex, Tag 08HY (counit definition of base change)
and Tag 0D5S (composition of derived pullback).
(blueprint: lem-pc-derived-base-change-source-iso).

Proof: Use the composition comparisons c selected by exists_derivedPullbackComposition
and the adjunctions pinned to their derived counits by exists_schemeDerivedAdjunction.
For a scheme isomorphism e, the comparisons for e.hom followed by e.inv, and conversely,
together with the identity comparison, exhibit pullback as an equivalence. Its pinned
adjunction therefore has invertible unit and counit. The right-adjoint mate of c e.hom f
identifies R(e.hom f) with R(e.hom) followed by Rf. Insert the unit for e.hom to identify
Rf E with R(e.hom f) L(e.hom) E, and then apply the image of alpha. Applying Lg gives
the source isomorphism a. Perform the same construction for e' and beta to obtain b.
Transpose the claimed equation under the adjunction for e'.hom followed by f'.
Naturality of its counit identifies the right-hand transpose with the pullback of the
original transpose, after the comparison c for the source-coordinate square. The
associativity law for c identifies its square comparison with that for t; equality
transports agree by ht and proof irrelevance. Substitute hphi to identify the final
coefficient factors. The triangle identities cancel the units inserted in a and b.
The Hom equivalence is injective, proving the equation. All these identities apply to
zero coefficients, identity coordinates and empty schemes; no cartesian, affine or
quasi-coherent hypothesis is used. -/
theorem exists_derivedBaseChange_source_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' T T' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (e : T ≅ X) (e' : T' ≅ X') (t : T' ⟶ T)
    (ht : t ≫ e.hom = e'.hom ≫ g')
    (h0 : t ≫ (e.hom ≫ f) = (e'.hom ≫ f') ≫ g)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory X')
    (N : schemeDerivedCategory T) (N' : schemeDerivedCategory T')
    (phi : (derivedPullback g').obj E ⟶ E')
    (phi0 : (derivedPullback t).obj N ⟶ N')
    (alpha : (derivedPullback e.hom).obj E ≅ N)
    (beta : (derivedPullback e'.hom).obj E' ≅ N')
    (hphi :
      (derivedPullback t).map alpha.hom ≫ phi0 =
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))) t e.hom).hom.app E ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj E) ht) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))) e'.hom g').inv.app E ≫
        (derivedPullback e'.hom).map phi ≫ beta.hom) :
    ∃ (a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
          (derivedPullback g).obj ((schemeDerivedDirectImage (e.hom ≫ f)).obj N))
      (b : (schemeDerivedDirectImage f').obj E' ≅
          (schemeDerivedDirectImage (e'.hom ≫ f')).obj N'),
      (schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map phi) ≫ b.hom =
      a.hom ≫ (schemeDerivedBaseChangeMap (e.hom ≫ f) (e'.hom ≫ f') g t h0 N ≫
        (schemeDerivedDirectImage (e'.hom ≫ f')).map phi0) := by sorry

end AlgebraicGeometry
