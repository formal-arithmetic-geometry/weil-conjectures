/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison

/-! # Affine depth-two hull of a finite etale pushforward

Source: Stacks Project, Tags 0EY6, 0G41 and 0E9I; the double-dual kernel
calculation underlying Tags 0EBI and 0EBJ.
(blueprint: lem-sbc-affine-depth-two-pushforward-hull)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- On an affine chart the actual pushforward is the coherent depth-two hull.

Source: Stacks Project, Tag 0EY6 proof of (1), Tag 0G41(2), and Tag 0E9I.
The local kernel argument expands the depth calculation of Tag 0EBI and does
not require the integrality hypotheses of Tags 0EBI and 0EBJ.
(blueprint: lem-sbc-affine-depth-two-pushforward-hull)

Proof: Write the chart as Spec A. Its intersection with U is quasi-compact,
since A is Noetherian. The finite etale algebra on that intersection is finite
locally free. Extend its underlying module to a finite A-module M using
0G41(2) and put N = Hom_A(Hom_A(M,A),A). Finite presentation makes duals
commute with localization, so N restricts to the original locally free module.
A finite free presentation of the first dual expresses N as the kernel of a
map between finite free modules. At a boundary prime, choose a regular pair
x,y in the base local ring. The element x acts injectively on the free modules
and hence on N. If y*n = x*n' in N, regularity in the free source gives n=x*m;
applying the presentation map and cancelling x in the free target shows m is
in N. Thus y is injective modulo x. Nakayama gives properness when N is nonzero;
if N is zero, its depth is infinity. This proves boundary depth at least two.
The associated sheaf is quasi-coherent with finite affine sections and finite
stalks. Hartogs 0E9I identifies it with the direct image of its restriction.
Direct images compose and commute with restriction to an open chart, identifying
this sheaf with the displayed restriction of B.toModule. These identifications
preserve scalar actions on sections and stalks. Transport quasi-coherence,
finiteness and depth across them. The empty intersection gives the zero module,
and an empty affine chart has no boundary points. -/
theorem affine_depth_two_pushforward_hull
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f]
    (V : L.Opens) (hV : IsAffineOpen V) :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    let N := Modules.restrict B.toModule hV.fromSpec
    N.IsQuasicoherent ∧
      Module.Finite (L.presheaf.obj (op V)) Γ(N, ⊤) ∧
      (∀ x : Spec (L.presheaf.obj (op V)), hV.fromSpec x ∉ U →
        ∃ hfinite : Module.Finite ((Spec (L.presheaf.obj (op V))).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth
            (R := (Spec (L.presheaf.obj (op V))).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x)) := by sorry

end AlgebraicGeometry.Scheme
