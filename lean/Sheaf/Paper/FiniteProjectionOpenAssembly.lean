/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.Paper.FiniteProjectionExchangeData

/-! # Open restrictions and assembly of the compact projection diamond -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Open-factor restriction identities and assembly with a supplied proper-factor equality.
Source: prop-sf-pf-coherence.proof.md, open-factor and base-change paragraphs.
(blueprint: lem-sf-finite-projection-open-assembly).

Proof: restrict the two open routes by j'^*. The open-unit normalization of beta,
gamma and gamma' replaces their restrictions by the canonical units. Naturality of
mu and tensor_square for (a,j',j,h) identify each remaining composite with
openSource. Both open routes are isomorphisms onto an object in the image of j'_!,
so full faithfulness of j'_! turns equality of their restrictions into equality of
these routes. Expand PF^c as the proper projection followed by the proper image of
gamma and the pullback-composition comparison. Expand Ex_!^c as proper exchange
followed by the proper image of beta. Naturality of proper exchange moves the image
of gamma through exchange; naturality of proper projection moves beta through the
projection. Substitute the supplied proper-factor equality and the open-route equality.
The pullback composition associativity identifies the two remaining target comparisons
with the one for the outside square. This gives the diamond equality. All maps are
actual fixed-scalar maps; no constructibility, absolute separatedness, or invertibility
of proper projection or exchange is used. -/
theorem open_factor_assembly
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y)
    (_hp : properFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq
        ((ext A c.i).obj K) L =
      exchangeFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq
        ((ext A c.i).obj K) L) :
    diamondLeft A s c K L = diamondRight A s c K L ∧
    (pull A (c.ofIsPullback s).i).map
        (openFirst A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
        openUnitInv A (c.ofIsPullback s).i _ =
      openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) ∧
    (pull A (c.ofIsPullback s).i).map
        (openSecond A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
        openUnitInv A (c.ofIsPullback s).i _ =
      openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) := by sorry

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
