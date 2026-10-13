/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.RingTheory.Depth

/-! # Boundary depth transferred from a finite structure algebra

Source: Stacks Project, Tag 0AUK, applied as in the proof of Tag 0EY6(2).
(blueprint: lem-sbc-finite-structure-algebra-depth)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Depth two of the stalks of a finite direct image algebra implies depth two
at the points of its relative spectrum above those stalks.

Source: Stacks Project, Tag 0AUK; Tag 0EY6, proof of (2).
(blueprint: lem-sbc-finite-structure-algebra-depth)

Proof: At y in the boundary choose an affine Noetherian neighbourhood Spec R.
Its inverse image under p is Spec S, with S finite over R. For the prime q of R
corresponding to y, the stalk of p_* O_E is S localized at R minus q. The algebra
isomorphism identifies it, as an R_q-module, with the supplied stalk of A.
A point z over y corresponds to a maximal ideal of this finite R_q-algebra:
finite ring maps are integral, so primes over the maximal ideal are maximal.
The local ring O_E,z is the localization at that maximal ideal. Tag 0AUK says
that the depth of the finite algebra as an R_q-module is the minimum of the
depths of these localizations. Each localization therefore has depth at least
two. The base is locally Noetherian, so R_q is Noetherian as required. If the
algebra stalk is zero there are no points over y; the assertion is vacuous.
No property of a chosen cover, or etaleness, is used in this transfer. -/
theorem depth_two_of_finite_structure_algebra
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (A : L.CommAlgebraSheaf)
    (hdepth : ∀ y : L, y ∉ U →
      letI : Algebra (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj) :=
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map A.hom.hom).hom.toAlgebra
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj))
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p]
    (α : A ≅ Under.mk
      (⟨p.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj E.sheaf)) :
    ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) := by
  sorry

end AlgebraicGeometry.Scheme
