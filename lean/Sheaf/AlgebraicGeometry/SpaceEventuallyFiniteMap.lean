/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finiteness descends to a stage of an algebraic-space inverse system

Source: Stacks Project, Limits of Spaces, Situation 084W and Lemma 084Z
(`situation-descent-property`, `lemma-descend-finite`); persistence by Tag 03ZS
(blueprint: lem-sfb-space-eventually-finite-map).

Quasi-separatedness is absolute: we use its equivalent affine-pair criterion from
Properties of Spaces, `lemma-characterize-quasi-separated`, as in
`IntegralSpaceFinitePresentationLimit`. Sheaf pullbacks give the canonical base changes;
no representability or finiteness is assumed at any finite stage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type morphism of qcqs algebraic spaces that becomes finite over a
limit with affine transitions is finite at every sufficiently late stage.
Source: Stacks Project, Limits of Spaces, Situation 084W and Lemma 084Z;
Morphisms of Spaces, Tag 03ZS; Properties of Spaces, `lemma-characterize-quasi-separated`
(blueprint: lem-sfb-space-eventually-finite-map).

Proof:
1. Restrict to the directed tail above i₀. Choose an affine surjective etale scheme
   chart V₀ of Y₀ by [lem-sfb-qc-space-affine-etale-atlas]. Form W₀ = X₀ ×_Y₀ V₀
   and its base changes Wᵢ, Vᵢ. By [lem-trf-space-fibre-products-etale-covers] these
   are the corresponding chart pullbacks of Xᵢ, Yᵢ, and Vᵢ → Yᵢ stays surjective
   etale. The affine scheme V₀ is qcqs by [lem-weil-pbc-affine-scheme-qcqs], and
   [lem-sfb-qcqs-space-fibre-product] makes W₀ qcqs.
2. By [lem-sfb-space-affine-locality] and [lem-sfb-space-qcqs-permanence], affine
   transitions make every Vᵢ an affine scheme and every Wᵢ qcqs, with affine
   transitions. Since X₀ is quasi-compact and Y₀ quasi-separated, f₀ is quasi-compact.
   Its local finite type hypothesis therefore gives finite type. Base change preserves
   this by [lem-sfb-space-four-property-fppf-descent]. Once Wᵢ is a scheme, identity
   charts in [def-sfb-space-morphism-properties] give local finite type for Wᵢ → Vᵢ.
3. By [lem-sfb-space-affine-limits-schematic-stages], V = lim Vᵢ and W = lim Wᵢ,
   and V is affine. The identity W = X ×_Y V and the assumed scheme-test finiteness
   make W finite over V, hence affine, using [def-weil-finite-integral-morphism].
   Eventual affineness in [lem-sfb-space-affine-limits-schematic-stages] gives an
   affine Wₖ, and then all subsequent Wᵢ are affine.
4. Reindex at k. The algebraic-space limit of the affine schemes Vᵢ is also their
   scheme limit. Fibre-product associativity gives Wᵢ = Wₖ ×_Vₖ Vᵢ and
   W = Wₖ ×_Vₖ V. Apply [lem-weil-pbc-descend-finite] to Wₖ → Vₖ: all initial
   schemes are qcqs by [lem-weil-pbc-affine-scheme-qcqs], the transitions are affine,
   the initial map is locally of finite type, and its limit is finite. Obtain j ≥ k
   with Wⱼ → Vⱼ finite.
5. The surjective etale chart Vⱼ → Yⱼ and
   [lem-sfb-space-integral-finite-etale-locality] imply fⱼ is finite. For every i ≥ j,
   fᵢ is its base change, hence finite by [lem-sfb-finite-space-morphism-topology]. -/
theorem exists_eventually_isFinite_baseChange
    {S : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hBqc : ∀ i : I, CompactSpace (Point (D.obj (op i)).obj.obj))
    (hBqs : ∀ (i : I) (U V : Over S)
      (a : yoneda.obj U ⟶ (D.obj (op i)).obj.obj)
      (b : yoneda.obj V ⟶ (D.obj (op i)).obj.obj),
      IsAffine U.left → IsAffine V.left → CompactSpace (Point (Limits.pullback a b)))
    (haff : ∀ (i j : Iᵒᵖ) (g : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map g).hom.hom)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : AlgebraicSpace S) (f₀ : X₀ ⟶ Y₀) (y₀ : Y₀ ⟶ D.obj (op i₀))
    (hXqc : CompactSpace (Point X₀.obj.obj))
    (hXqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X₀.obj.obj)
      (b : yoneda.obj V ⟶ X₀.obj.obj), IsAffine U.left → IsAffine V.left →
      CompactSpace (Point (Limits.pullback a b)))
    (hYqc : CompactSpace (Point Y₀.obj.obj))
    (hYqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y₀.obj.obj)
      (b : yoneda.obj V ⟶ Y₀.obj.obj), IsAffine U.left → IsAffine V.left →
      CompactSpace (Point (Limits.pullback a b)))
    (hlft : MapIsLocally (@LocallyOfFiniteType) f₀)
    (hfinite : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left)
      (((Over.pullback (c.π.app (op i₀)).hom).map
        (Over.homMk (U := Over.mk (f₀.hom ≫ y₀.hom))
          (V := Over.mk y₀.hom) f₀.hom rfl)).left.hom)) :
    ∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hji : j ≤ i),
      IsRepresentableWith (fun _ _ p ↦ IsFinite p.left)
        (((Over.pullback (D.map (homOfLE (le_trans hj hji)).op).hom).map
          (Over.homMk (U := Over.mk (f₀.hom ≫ y₀.hom))
            (V := Over.mk y₀.hom) f₀.hom rfl)).left.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
