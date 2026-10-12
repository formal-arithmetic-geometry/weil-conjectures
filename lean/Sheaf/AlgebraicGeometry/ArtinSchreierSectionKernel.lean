/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The kernel of a specified Artin--Schreier morphism

Source: Stacks Project, Tag 0A3J, opening exact sequence.
(blueprint: lem-sc-artin-schreier-section-kernel)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The specified constant-sheaf map is a kernel of Frobenius minus identity.
Source: Stacks Project, Tag 0A3J, exactness at the constant sheaf and the function sheaf.
(blueprint: lem-sc-artin-schreier-section-kernel)

Proof: A geometric stalk of the sheaf of functions is the strict local ring at the
point: the natural section equivalences identify its filtered colimit with that ring.
The restriction formula transports the ring operations and the characteristic-p
relation from global sections. The equation for `wp` therefore becomes `r^p-r=0`.
The local-ring Artin--Schreier kernel theorem identifies every such root with a
unique prime-field element. The constant-sheaf geometric-stalk isomorphism identifies
the source stalk with `ULift (ZMod p)`, and the formula for `iota` identifies its
map with the canonical prime-field inclusion. It follows that the induced map
from the constant sheaf to the categorical kernel is an isomorphism on every
geometric stalk. Stalk functors preserve finite limits, so these are the stalks
of the kernel itself. Conservativity gives an isomorphism of sheaves, hence
`iota` is a kernel arrow. On the empty scheme the conservative family is empty
and the same reflection argument applies. No surjectivity of `wp` is used. -/
theorem artinSchreier_section_data_isKernel (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G) (iota : X.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0)
    (hrestr : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hiota : ∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    Nonempty (Limits.IsLimit (Limits.KernelFork.ofι iota hzero)) := by
  sorry

end AlgebraicGeometry.Scheme
