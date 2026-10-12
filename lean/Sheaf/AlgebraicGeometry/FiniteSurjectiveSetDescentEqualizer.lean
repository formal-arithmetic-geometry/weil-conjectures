/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
/-! # Lifting compatible sections along a finite surjective morphism

Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-equalizer).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Source: Stacks Project, Étale Cohomology, Remark 09Z3, following Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent-equalizer).
Every compatible section is in the image of the unit.

Proof:
1. Write D = X' ×_X X', with projections p and q and composite h = p ≫ f = q ≫ f.
   Both p and h are finite, by finite base change and composition.
2. Let A = f_* f⁻¹G and B = h_* h⁻¹G. At U, the two maps A(U) → B(U)
   are pullback by p or q, followed by the chosen inverse-image comparison and
   the canonical fibre-product pasting isomorphism. Naturality of units and of
   the comparisons makes these maps morphisms of sheaves.
3. Their sectionwise equalizer E is a sheaf. The composition-unit equation shows
   the unit G → A equalizes these two morphisms, hence factors as ψ : G → E.
4. Fix a geometric point x : Spec Ω → X. Its set P of lifts to X' is nonempty:
   lift the underlying point using surjectivity, then use finite geometric-point
   lifting. Lifts to D correspond to P × P by the pullback universal property.
5. Finite pushforward stalks and the inverse-image germ bijection identify A_x
   with the product of G_x over P, and B_x with its product over P × P.
6. Under these identifications the unit is the diagonal. Indeed, restriction of
   the germ of a unit-pulled-back section to a lift is its pulled-back germ, and
   the inverse-image stalk bijection sends it to the original germ. Every stalk
   element is represented by a section, so this verifies the diagonal on all elements.
7. The composition comparisons respect the inverse-image stalk identifications:
   both composites send every iterated unit-pulled-back germ to the original germ,
   by the composition-unit equation. The germ theorem says these germs generate
   the inverse-image stalk and uniquely determine that map. Thus the composites agree.
8. A germ of a section of A is represented over some U ×_X X'. Pulling it to D
   through p or q, the pointed fibre-product pasting identifies its germ with
   the restriction at the corresponding lift. Step 7 then says the maps on
   stalks are the two coordinate projections from the P-indexed product.
9. Stalks preserve the equalizer E. By step 8, its stalk consists of constant
   families. Since P is nonempty, the diagonal is a bijection G_x → E_x.
10. Geometric stalks detect isomorphisms, so ψ is an isomorphism. At U = X this
    makes G(X) → E(X) bijective. Compatibility is membership in E(X), so the
    inverse supplies a preimage of every compatible section. Conversely every
    unit section is compatible by step 3. If X is empty, the empty sheaf covering
    supplies the unique section and the compatibility equation is automatic. -/
theorem finiteSurjectiveSetDescent_compatible_lift
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') →
          ∃ s : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
            etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s = s' := by
  sorry

end AlgebraicGeometry
