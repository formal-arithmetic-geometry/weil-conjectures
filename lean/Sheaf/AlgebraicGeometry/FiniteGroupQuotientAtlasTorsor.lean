/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.FiniteGroupSheafQuotient
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Finite constant-group quotient atlas pullbacks

Source: Stacks Project, examples-stacks.tex, Tags 0371, 04WM and 0BLZ;
spaces-groupoids.tex, Tag 04M9
(blueprint: lem-sfb-finite-group-quotient-atlas-torsor).

The statement uses the sheaf torsor definition, before representability is known.
For every test object the iso-comma groupoid is equivalent to the discrete groupoid
of torsor sections, by evaluation at the identity. Its inverse is characterized
on every constant group label after every restriction. These formulas specify the
base-change identifications, including their identity and composite cases.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ConstantGroupSheafQuotient

/-- The sheaf of maps to the specified action scheme, on the big fppf site of `T`.
Source: Stacks 0371 (blueprint: lem-sfb-finite-group-quotient-atlas-torsor). -/
def schemeActionSheaf {S : Scheme.{u}} {H : Type (u + 1)} [Group H]
    (Z : Action (Over S) H) (T : Over S) :
    Action (Sheaf (Scheme.fppfTopology.over T.left) (Type (u + 1))) H :=
  ((((Over.map T.hom).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.fppfTopology.over T.left) (Scheme.fppfTopology.over S)).mapAction H).obj
      (((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.mapAction H).obj Z))

/-- The atlas pullback is the original sheaf torsor, canonically, and that sheaf
is represented by a finite étale surjective scheme. The equivalences retain the
actual specified isomorphisms, rather than only their isomorphism classes.
Source: Stacks 0371, 04WM, 0BLZ and 04M9
(blueprint: lem-sfb-finite-group-quotient-atlas-torsor).

Proof:
1. Over `U`, the two outer fibres in `GroupoidTwoFiberProduct` are discrete.
   Hence its objects are exactly `(z,eta)` and it has only identity arrows.
   Evaluate `eta` at `1` to obtain `p`. Equivariance gives `eta(h)=h*p` and
   compatibility with the map to `Z` gives `z=v(p)`.
2. Conversely a section `p` defines `z=v(p)` and `eta(h)=h*p`. Locally where
   the torsor is regular, this is right multiplication by the coordinate of `p`;
   its inverse is right multiplication by the inverse coordinate, even for a
   noncommutative group. The inverses glue by the sheaf axiom
   (def-weil-pbc-sites-and-cohomology). These two operations are mutually inverse.
3. On an fppf trivializing covering the torsor is the coproduct of copies of
   the base indexed by `H` (lem-weil-pbc-scheme-coproduct-family). Over an affine
   open it is the spectrum of the finite product of the coordinate ring
   (lem-weil-pbc-finite-affine-coproduct-spectrum), finite free over that ring.
   Every summand is étale, so the coproduct is étale
   (lem-sc-etale-coproduct-etale).
4. The local schemes and their overlap comparisons give the descent datum of
   lem-trf-fppf-sheaf-representability-descent-data. Finite étale fppf descent
   (lem-sfb-finite-etale-fppf-descent) produces its finite étale realization.
   Effectivity in the sheaf/descent equivalence identifies its represented sheaf
   with precisely the original torsor, giving its natural representing bijections.
5. Joint surjectivity of the covering and the identity summand give surjectivity
   of the representing scheme. For every restriction, `eta(1)` restricts to
   `eta|_V(1)` and `h*p` restricts to `h*(p|_V)`. This gives the last displayed
   formula on all labels, hence on the entire constant sheaf by sheafification.
   Yoneda and the fibre-product universal property identify the representing
   scheme after base change with the ordinary scheme pullback. No freeness on
   `Z`, invertibility of the order, or finite-type condition is used. -/
theorem finiteGroupQuotientAtlasTorsor
    (S : Scheme.{u}) (H : Type (u + 1)) [Group H] [Finite H]
    (Z : Action (Over S) H) (T : Over S)
    (xi : Over (schemeActionSheaf Z T))
    (hxi : IsLocallyRegular (Scheme.fppfTopology.over T.left) H xi.left) :
    ∃ X : Over T.left, Nonempty (xi.left.V.obj.RepresentableBy X) ∧
      IsFinite X.hom ∧ Etale X.hom ∧ Surjective X.hom ∧
      ∃ E : ∀ U : Over T.left,
        fiberAt (Scheme.fppfTopology.over T.left) (schemeActionSheaf Z T) xi U ≌
          Discrete (xi.left.V.obj.obj (op U)),
        (∀ (U : Over T.left)
          (L : fiberAt (Scheme.fppfTopology.over T.left) (schemeActionSheaf Z T) xi U),
          ((E U).functor.obj L).as =
            evaluateAt (Scheme.fppfTopology.over T.left) (schemeActionSheaf Z T) xi U L ∧
          xi.hom.hom.hom.app (op U) (((E U).functor.obj L).as) = L.of.left.as) ∧
        (∀ (U V : Over T.left) (b : V ⟶ U) (p : xi.left.V.obj.obj (op U)) (h : H),
          (comparison ((Scheme.fppfTopology.over T.left).over U) Over.mkIdTerminal
            (onSlice (Scheme.fppfTopology.over T.left) (schemeActionSheaf Z T) U)
            ((E U).inverse.obj ⟨p⟩)).hom.hom.app (op (Over.mk b))
                (label ((Scheme.fppfTopology.over T.left).over U) H (Over.mk b) h) =
            (xi.left.ρ h).hom.app (op V) (xi.left.V.obj.map b.op p)) := by
  sorry

end AlgebraicGeometry.ConstantGroupSheafQuotient
