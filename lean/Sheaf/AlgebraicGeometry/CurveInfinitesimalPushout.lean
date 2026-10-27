/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Infinitesimal pushout gluing of proper curves

Source: Stacks Project, quot.tex, Tag 0D56, lemma-curves-RS-star
(blueprint: lem-sfb-curve-infinitesimal-pushout).

The equivalence is expressed by preservation of the family condition, essential
surjectivity on specified gluing triples, and bijectivity on isomorphisms. All pullbacks
and the comparison of iterated pullbacks are the canonical presheaf constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveFamily

/-- The existing family's actual presheaf morphism, bundled in the slice category.
Source: Stacks, Tag 0D56 (blueprint: lem-sfb-curve-infinitesimal-pushout). -/
def presentation {B : Scheme.{u}} {T : Over B} (X : ProperCurveFamily T) :
    Over (yoneda.obj T) :=
  Over.mk X.projection

/-- Pullback preserves the curve-family objects, with the canonical presheaf pullback.
The isomorphism is in the slice, so it fixes the base projection.
Source: Stacks, Tag 0D56 (blueprint: lem-sfb-curve-infinitesimal-pushout). -/
def HasCurvePullback {B : Scheme.{u}} {T U : Over B} (f : T ⟶ U) : Prop :=
  ∀ X : ProperCurveFamily U, ∃ Y : ProperCurveFamily T,
    Nonempty (Y.presentation ≅ (Over.pullback (yoneda.map f)).obj X.presentation)

/-- The canonical identification of the two iterated restrictions in a commuting square.
It is the composite of pullback associativity, the square equation, and associativity.
Source: Stacks, Tag 0D56 (blueprint: lem-sfb-curve-infinitesimal-pushout). -/
def restrictionComparison {B : Scheme.{u}} {T S T' P : Over B}
    (a : T ⟶ S) (i : T ⟶ T') (j : S ⟶ P) (b : T' ⟶ P)
    (h : a ≫ j = i ≫ b) :
    Over.pullback (yoneda.map j) ⋙ Over.pullback (yoneda.map a) ≅
      Over.pullback (yoneda.map b) ⋙ Over.pullback (yoneda.map i) :=
  (Over.pullbackComp (yoneda.map a) (yoneda.map j)).symm ≪≫
    eqToIso (congrArg (fun f : yoneda.obj T ⟶ yoneda.obj P ↦ Over.pullback f)
      (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ≪≫
    Over.pullbackComp (yoneda.map i) (yoneda.map b)

/-- A specified compatible pair of isomorphisms between the restrictions of two families.
The equation retains the gluing identification, rather than just isomorphism classes.
Source: Stacks, Tag 0D56 (blueprint: lem-sfb-curve-infinitesimal-pushout). -/
def CompatibleRestrictionIsos {B : Scheme.{u}} {T S T' P : Over B}
    (a : T ⟶ S) (i : T ⟶ T') (j : S ⟶ P) (b : T' ⟶ P)
    (h : a ≫ j = i ≫ b) (X Y : ProperCurveFamily P)
    (s : (Over.pullback (yoneda.map j)).obj X.presentation ≅
      (Over.pullback (yoneda.map j)).obj Y.presentation)
    (t : (Over.pullback (yoneda.map b)).obj X.presentation ≅
      (Over.pullback (yoneda.map b)).obj Y.presentation) : Prop :=
  (Over.pullback (yoneda.map a)).mapIso s ≪≫
      (restrictionComparison a i j b h).app Y.presentation =
    (restrictionComparison a i j b h).app X.presentation ≪≫
      (Over.pullback (yoneda.map i)).mapIso t

/-- Restriction from the pushout is an equivalence on the groupoids of proper curves,
written as well-defined restriction, essential surjectivity, and full faithfulness.
No connectedness, nonempty-fibre, reducedness, or finite-order hypothesis is imposed.
Source: Stacks, quot.tex, Tag 0D56, lemma-curves-RS-star
(blueprint: lem-sfb-curve-infinitesimal-pushout).

Proof: (1) The scheme affine-thickening pushout lemma identifies S with a thickening
of P and T with its cartesian pullback; corresponding residue fields of S and P agree.
(2) Flat locally finitely presented algebraic spaces glue by
lem-sfb-flat-lfp-space-pushout-gluing. Proper base change and the geometric-fibre
base-change dimension lemma show restriction preserves curve families. Properness gives
quasi-compactness and a closed, hence quasi-compact, diagonal, giving finite presentation.
(3) Apply essential surjectivity of flat-lfp gluing to the specified triple and its
specified isomorphism phi, obtaining W with compatible identifications of restrictions.
(4) W_S is a thickening of W. The thickening topological-properties lemma transfers
quasi-compactness, quasi-separatedness, separatedness and universal closedness from W_S
back to W. Together with local finite presentation these give properness and finite
presentation, without a finite-order assumption.
(5) Each geometric fibre of W equals the corresponding fibre of W_S, by the residue
field identification and fibre-product pasting, so its dimension is at most one.
(6) Full faithfulness of flat-lfp gluing lifts any compatible pair of isomorphisms
uniquely. Lift their inverses too; faithfulness makes both composites identities.
Thus the unique lift is an isomorphism. This is precisely full faithfulness of the
restriction on the groupoids, and proves the asserted equivalence. -/
theorem infinitesimalPushout
    {T S T' P : Over (Spec (.of (ULift.{u} ℤ)))}
    (a : T ⟶ S) (i : T ⟶ T') (j : S ⟶ P) (b : T' ⟶ P)
    [IsClosedImmersion i.left] (hi : Function.Bijective i.left.base)
    [IsAffineHom a.left] (h : a ≫ j = i ≫ b)
    (hp : IsPushout a.left i.left j.left b.left) :
    (HasCurvePullback j ∧ HasCurvePullback b ∧
      HasCurvePullback a ∧ HasCurvePullback i) ∧
    (∀ (X : ProperCurveFamily S) (Y : ProperCurveFamily T')
      (φ : (Over.pullback (yoneda.map a)).obj X.presentation ≅
        (Over.pullback (yoneda.map i)).obj Y.presentation),
      ∃ (W : ProperCurveFamily P)
        (s : (Over.pullback (yoneda.map j)).obj W.presentation ≅ X.presentation)
        (t : (Over.pullback (yoneda.map b)).obj W.presentation ≅ Y.presentation),
        (restrictionComparison a i j b h).app W.presentation ≪≫
            (Over.pullback (yoneda.map i)).mapIso t =
          (Over.pullback (yoneda.map a)).mapIso s ≪≫ φ) ∧
    (∀ (X Y : ProperCurveFamily P)
      (s : (Over.pullback (yoneda.map j)).obj X.presentation ≅
        (Over.pullback (yoneda.map j)).obj Y.presentation)
      (t : (Over.pullback (yoneda.map b)).obj X.presentation ≅
        (Over.pullback (yoneda.map b)).obj Y.presentation),
      CompatibleRestrictionIsos a i j b h X Y s t →
      ∃! e : X.presentation ≅ Y.presentation,
        (Over.pullback (yoneda.map j)).mapIso e = s ∧
          (Over.pullback (yoneda.map b)).mapIso e = t) := by
  sorry

end AlgebraicGeometry.ProperCurveFamily
