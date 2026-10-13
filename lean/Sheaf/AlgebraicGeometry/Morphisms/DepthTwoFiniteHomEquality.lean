/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.RingTheory.Depth

/-! # Equality detected on the open of a finite depth-two source

Source: Stacks Project, Tags 0EY6, 0AUK and 0E9I.
(blueprint: lem-sbc-depth-two-finite-hom-equality)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Two morphisms to an affine L-scheme agree when they agree on the open
of a finite source whose boundary local rings have depth at least two.

Source: Stacks Project, Tags 0AUK and 0E9I, as used in the converse of
Tag 0EY6(2); affine structure algebras, Tag 01SA.
(blueprint: lem-sbc-depth-two-finite-hom-equality)

Proof: The finite algebra r_*O_F is coherent. At a boundary point its
stalk depth is the minimum of the source local-ring depths by 0AUK, hence
at least two. Hartogs 0E9I makes its restriction-adjunction unit invertible,
in particular injective. Each of the two L-morphisms gives an O_L-algebra
map p_*O_E -> r_*O_F. Their restrictions agree by the supplied equality
on the source open. Naturality of the restriction unit, followed by its
injectivity for r_*O_F, shows that the original algebra maps agree.
Faithfulness for the affine target (01SA), checked on affine opens of L,
shows the morphisms agree. No target depth bound is needed. If the source
open is empty the same Hartogs injectivity forces the finite source algebra
to vanish, so the source is empty. If U=L the conclusion is immediate. -/
theorem hom_eq_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (f g : F ⟶ E) (hf : f ≫ p = r) (hg : g ≫ p = r)
    (hfg : (r ⁻¹ᵁ U).ι ≫ f = (r ⁻¹ᵁ U).ι ≫ g) : f = g := by sorry

end AlgebraicGeometry.Scheme
