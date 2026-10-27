/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Whiskering
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Fppf descent and Isom spaces for families of curves

Source: Stacks Project, quot.tex, Situation 0D4Z and Lemmas 0D51--0D53
(blueprint: lem-sfb-curve-descent-isom-spaces).

The families and their cartesian arrows are those of `ProperCurveModuli`. Descent is
expressed by colimiting cocones over covering sieves, with the projection to the base
specified. The Isom functor uses restriction to slices of the big site: restriction of
an algebraic space over `T` to schemes over `U` is precisely its base change to `U`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProperCurveFamily

/-- Isomorphisms of the two families after base change to `U`. The slice of `Over T`
over `U` is the category of schemes over `U.left`, and natural isomorphisms on it are
exactly isomorphisms of the base-changed algebraic spaces over `U.left`.
Source: Stacks Project, quot.tex, Tag 0D53 via Tag 0D1F
(blueprint: lem-sfb-curve-descent-isom-spaces). -/
abbrev isomorphisms {T : Scheme.{u}}
    (X Y : ProperCurveFamily (Over.mk (𝟙 T))) (U : Over T) :=
  ((Over.forget U).op ⋙ X.space.obj.obj) ≅ ((Over.forget U).op ⋙ Y.space.obj.obj)

/-- Pullback of an isomorphism is its restriction along composition of test-scheme maps.
Source: Stacks Project, quot.tex, Tag 0D53 via Tag 0D1F
(blueprint: lem-sfb-curve-descent-isom-spaces). -/
def isomorphismBaseChange {T : Scheme.{u}}
    (X Y : ProperCurveFamily (Over.mk (𝟙 T))) {U V : Over T}
    (a : U ⟶ V) (α : isomorphisms X Y V) : isomorphisms X Y U :=
  Functor.isoWhiskerLeft (Over.map a).op α

end AlgebraicGeometry.ProperCurveFamily

namespace AlgebraicGeometry.ProperCurveModuli

/-- The category of flat proper finitely presented algebraic-space families with
geometric fibres of dimension at most one is an fppf stack in groupoids. Its Isom
functor for any two families over any scheme is represented by an algebraic space.
The representing bijections commute with every base change, so they also assert the
sheaf condition for isomorphisms. The lifted integer ring only fixes the size of Spec Z.

Source: Stacks Project, quot.tex, Situation 0D4Z and Tags 0D51--0D53
(blueprint: lem-sfb-curve-descent-isom-spaces).

Proof:
1. By lem-trf-space-fibre-products-etale-covers every base change exists as an algebraic
space. By lem-sfb-space-flat-proper-fp-locality its structure map is flat, proper and
finitely presented. By lem-sfb-space-relative-dimension-base-change its geometric
fibres have dimension at most one. The universal property of fibre products supplies
cartesian lifts and shows that every arrow is strongly cartesian, hence fibres are
 groupoids.
2. Apply lem-sfb-space-hom-representability to (X,Y), (Y,X), (X,X) and (Y,Y). Properness
supplies separatedness of each target. Compose the two universal maps in both orders
and form the fibre product over the identity sections in Hom(X,X) times Hom(Y,Y).
By lem-trf-space-fibre-products-etale-covers it is an algebraic space. Its sections are
pairs of mutually inverse morphisms; uniqueness of the inverse identifies them with
Isom. Composition, identity and this identification commute with arbitrary base change.
The fppf sheaf property of algebraic spaces gives descent of arrows.
3. For a compatible family on an arbitrary fppf cover, properness gives finite type.
Apply lem-sfb-space-finite-type-fppf-effectivity, with no countability restriction, to
descend the algebraic spaces and the specified transition isomorphisms. Apply the
three separate assertions of lem-sfb-space-flat-proper-fp-locality to recover flatness,
properness and finite presentation. Properness gives quasi-separatedness, so covering
detection in lem-sfb-space-relative-dimension-base-change recovers the dimension bound.
This produces an effective object in the curve category. Descent of arrows gives the
unique factorizations of cocones, hence the asserted colimiting cocone over each
covering sieve, with exactly its canonical base cocone. -/
theorem fppf_stack_and_isom_spaces :
    (forget (Spec (.of (ULift.{u} ℤ)))).IsFibered ∧
    (∀ {X Y : ProperCurveModuli (Spec (.of (ULift.{u} ℤ)))} (a : X ⟶ Y),
      (forget (Spec (.of (ULift.{u} ℤ)))).IsStronglyCartesian a.base a) ∧
    (∀ (T : Over (Spec (.of (ULift.{u} ℤ)))) (R : Sieve T),
      R ∈ (Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ)))) T →
      ∀ (D : R.arrows.category ⥤ ProperCurveModuli (Spec (.of (ULift.{u} ℤ))))
        (hD : D ⋙ forget (Spec (.of (ULift.{u} ℤ))) = R.arrows.diagram),
        ∃ (c : Cocone D) (hc : c.pt.base = T), Nonempty (IsColimit c) ∧
          ∀ i : R.arrows.category,
            (c.ι.app i).base ≫ eqToHom hc =
              eqToHom (Functor.congr_obj hD i) ≫ i.obj.hom) ∧
    ∀ (T : Scheme.{u}) (X Y : ProperCurveFamily (Over.mk (𝟙 T))),
      ∃ (I : AlgebraicSpace T)
        (θ : ∀ U : Over T, I.obj.obj.obj (op U) ≃ ProperCurveFamily.isomorphisms X Y U),
        ∀ (U V : Over T) (a : U ⟶ V) (z : I.obj.obj.obj (op V)),
          θ U (I.obj.obj.map a.op z) =
            ProperCurveFamily.isomorphismBaseChange X Y a (θ V z) := by
  sorry

end AlgebraicGeometry.ProperCurveModuli
