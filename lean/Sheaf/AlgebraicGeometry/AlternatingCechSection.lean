/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Ordered restriction admits a cochain section

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Ordered restriction admits a cochain section.

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ and 01FK.
(blueprint: lem-pc-alternating-cech-section)

Proof: Extend a function on increasing tuples by zero to arbitrary tuples. The
restriction formula and the isomorphisms e therefore show that every component of r
is surjective. Apply the chain-map equation to such lifts: in e coordinates the
differential of A is the signed face differential on increasing tuples.
For each injective tuple, sort its entries increasingly, multiply by the sign of the
sorting permutation, and transport the section along the unique isomorphism between
its chosen intersection and the sorted intersection. Set the value to zero on tuples
with repeated entries. The product universal properties provide these isomorphisms;
since opens form a poset, all their composites with face maps agree.
The signed extension is additive. For distinct entries, deleting an entry changes
its sorting sign by exactly the quotient of the two face signs, so extension commutes
with the differential. With one repeated pair only the two faces deleting an
occurrence survive, and their coefficients are opposite. With further repetitions
every face is zero. Transport through e gives a cochain map i. On increasing tuples
the sorting permutation is the identity, so hr gives i followed by r equal to the
identity, componentwise. Empty I gives zero products and the same construction. -/
theorem alternatingCechRestrictionHomotopy_map (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (A : CochainComplex AddCommGrpCat.{max v w} ℕ)
    (e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))))
    (r : S.complex F ⟶ A)
    (hr : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (e p).hom ((r.f p) s) t = s t.1) :
    ∃ i : A ⟶ S.complex F, i ≫ r = 𝟙 A := by sorry

end AlgebraicGeometry.Scheme
