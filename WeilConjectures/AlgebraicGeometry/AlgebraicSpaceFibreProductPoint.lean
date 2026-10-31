/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Points of a scheme fibre product over an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 03BU and 03H4; Morphisms, Tag 01RZ
(blueprint: lem-a1-space-fibre-product-point).

Equality of the two image point classes is expanded using a common field-valued
representative, as in `AlgebraicSpace.IsJointlySurjective`. The base scheme structure
is retained by taking all test maps in `Over S`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Schemes mapping to an algebraic space have a scheme representing their sheaf fibre
product. Every pair of points with the same image point class has a point above it.
The point-class condition is expanded as maps from one field spectrum, agreeing in `E`,
whose underlying point has images `x` and `y`. This is equivalent to agreement of any
chosen field-valued representatives after a common extension (Tag 03BU).
If the image of `C` is contained in the image of `U`, the first projection is surjective.
Source: Stacks, Properties of Spaces, Tag 03H4 and the point relation of Tag 03BU;
Morphisms, Tag 01RZ (blueprint: lem-a1-space-fibre-product-point).
Proof: (1) Form `C ×_S U` using [def-pc-fibre-product]. Pull back the representable
 diagonal of `E` [def-trf-algebraic-space] along its map to `E ×_S E`. The resulting
scheme `P` and projections represent the sheaf fibre product, by its universal property.
(2) For points `x` and `y` with equal image classes, choose representatives over fields
`K` and `L` [def-weil-field]. The relation of
[def-trf-algebraic-space-jointly-surjective-family] gives a common field extension `M`
where the two maps to `E` agree. The compatible maps from `Spec M` lift to `P` by the
representing property. The unique point of `Spec M` then gives a point above `x` and `y`.
Finally, if every image point from `C` occurs in the image of `U`, choose such a `y` for
each `x` and apply the preceding construction. This is surjectivity of the first
projection by [def-weil-surjective-morphism]. -/
theorem exists_scheme_fibreProduct_point {S : Scheme.{u}} (E : AlgebraicSpace S)
    (C U : Over S) (c : yoneda.obj C ⟶ E.obj.obj) (f : yoneda.obj U ⟶ E.obj.obj) :
    ∃ (P : Over S) (p : P ⟶ C) (q : P ⟶ U),
      IsPullback (yoneda.map p) (yoneda.map q) c f ∧
      (∀ (x : C.left) (y : U.left),
        (∃ (K : Type u) (_ : Field K) (s : Spec (CommRingCat.of K) ⟶ S)
          (a : Over.mk s ⟶ C) (b : Over.mk s ⟶ U) (t : Spec (CommRingCat.of K)),
          a.left t = x ∧ b.left t = y ∧
            c.app (op (Over.mk s)) a = f.app (op (Over.mk s)) b) →
        ∃ z : P.left, p.left z = x ∧ q.left z = y) ∧
      ((∀ x : C.left, ∃ (y : U.left) (K : Type u) (_ : Field K)
          (s : Spec (CommRingCat.of K) ⟶ S) (a : Over.mk s ⟶ C)
          (b : Over.mk s ⟶ U) (t : Spec (CommRingCat.of K)),
          a.left t = x ∧ b.left t = y ∧
            c.app (op (Over.mk s)) a = f.app (op (Over.mk s)) b) →
        Surjective p.left) := by
  classical
  let : CategoryTheory.Limits.HasBinaryProducts (Over S) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hd : yoneda.relativelyRepresentable
      (CategoryTheory.Limits.diag E.obj.obj) := by
    intro T a
    obtain ⟨P, p, q, h, _⟩ := E.property.1 T a
    exact ⟨P, p, q, h⟩
  have hc := CategoryTheory.Functor.relativelyRepresentable.of_diag hd c
  let P := hc.pullback f
  let p : P ⟶ C := hc.fst' f
  let q : P ⟶ U := hc.snd f
  have hp : IsPullback (yoneda.map p) (yoneda.map q) c f := hc.isPullback' f
  have hl : ∀ (x : C.left) (y : U.left),
      (∃ (K : Type u) (_ : Field K) (s : Spec (CommRingCat.of K) ⟶ S)
        (a : Over.mk s ⟶ C) (b : Over.mk s ⟶ U) (t : Spec (CommRingCat.of K)),
        a.left t = x ∧ b.left t = y ∧
          c.app (op (Over.mk s)) a = f.app (op (Over.mk s)) b) →
      ∃ z : P.left, p.left z = x ∧ q.left z = y := by
    rintro x y ⟨K, hK, s, a, b, t, ha, hb, hab⟩
    obtain ⟨l, hlp, hlq⟩ := CategoryTheory.Limits.Types.exists_of_isPullback
      (hp.app (op (Over.mk s))) a b hab
    refine ⟨l.left t, ?_, ?_⟩
    · exact (congrArg (fun r : Over.mk s ⟶ C ↦ r.left t) hlp).trans ha
    · exact (congrArg (fun r : Over.mk s ⟶ U ↦ r.left t) hlq).trans hb
  refine ⟨P, p, q, hp, hl, ?_⟩
  intro h
  constructor
  intro x
  obtain ⟨y, K, hK, s, a, b, t, ha, hb, hab⟩ := h x
  obtain ⟨z, hz, _⟩ := hl x y ⟨K, hK, s, a, b, t, ha, hb, hab⟩
  exact ⟨z, hz⟩

end AlgebraicGeometry.AlgebraicSpace
