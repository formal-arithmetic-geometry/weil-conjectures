module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Finite etale model across a regular codimension-two boundary

Source: Stacks Project, Tags 0BMA and 0EY7.
(blueprint: lem-sbc-regular-codimension-two-finite-etale-model)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite etale restriction extends across a regular codimension-two boundary.

Source: Stacks Project, Tags 0BMA, 0EY7, and 0EY6(2).
(blueprint: lem-sbc-regular-codimension-two-finite-etale-model)

Proof: Cover L by Noetherian affine opens W. On W apply 0BMA to each missing
regular stalk: purity holds since its dimension is at least two. Tag 0EY7
then extends the restriction of p to a finite etale cover of W. Its proof
uses Noetherian induction: at a generic point of the missing closed subset,
the pullback of the current open is the punctured local spectrum. Extend
there by purity, spread the finite presentation using 32.20.3, and shrink
using 32.20.4 to keep the spread finite etale while enlarging the current open.
For a missing target point, a regular system of parameters is a regular
sequence, so its stalk has depth at least two. A finite etale source stalk
is Noetherian and flat over this target stalk; the flat local depth formula
gives source depth at least two. On overlaps, the two finite extensions
therefore satisfy 0EY6(2): their direct-image algebras are the direct images
of the common algebra on V, by the depth-two Hartogs identity. This gives
unique isomorphisms extending the prescribed identification on V. Uniqueness
forces their cocycle identity, so glue the covers and restriction isomorphisms.
Finiteness and etaleness are local on the target, hence the glued r is finite
etale, and the local source-depth bounds give the asserted global bound.
No global quasi-compactness or quasi-separatedness is used. For an empty
cover use the empty scheme; for V = L use p itself. The regular boundary
hypothesis excludes a nonempty open-and-closed component of L disjoint from V,
since any generic point of that component has a zero-dimensional stalk. -/
theorem exists_finite_etale_depth_two_model
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hboundary : ∀ y : L, y ∉ V → IsRegularLocalRing (L.presheaf.stalk y) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk y))
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)] :
    ∃ (F : Scheme.{u}) (r : F ⟶ L), IsFinite r ∧ Etale r ∧
      (∀ z : F, r z ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ (r ⁻¹ᵁ V).toScheme,
        e.hom ≫ r ∣_ V = p ∣_ V := by
  sorry

end AlgebraicGeometry.Scheme
