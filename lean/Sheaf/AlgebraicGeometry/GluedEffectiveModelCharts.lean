/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Gluing local effective models along descended overlaps

Source: Stacks Project, Descent, Tag 0AP4, construction of the descended open overlaps.
(blueprint: lem-pd-glued-effective-model-charts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Local effective models embed into one scheme, and their charts pull back to the given opens.
Source: Stacks Project, Descent, Tag 0AP4, proof, through the construction of the glued scheme.
(blueprint: lem-pd-glued-effective-model-charts).

Proof: For each pair i,j, take the inverse image of U_j inside U_i. Compatibility of the
restricted transports with D, followed by inverse transport, shows that this open is
invariant under E_i. Since the square for q_i is cartesian, q_i is an fpqc covering and
its double overlap has the canonical transport. Descent of compatible opens (03N0) gives
an open W_ij of W_i pulling back to this intersection. On this intersection the identity
is compatible with both data; descent of morphisms (02W0) gives an isomorphism W_ij to
W_ji. Descend the inverse too. Faithfulness proves the inverse identities and the triple
cocycle, while uniqueness of descended opens identifies the triple overlaps. Use scheme
gluing for these opens and transitions. The structure maps to Y glue because their
restrictions agree; the resulting chart maps j_i are open immersions and cover W. The
maps q_i followed by j_i agree on the intersections of the U_i, so glue to q on V.
The chart square is cartesian: both its source and the inverse image of the chart are
obtained by gluing the intersections with all the U_j, with the same transition maps,
and their local identifications are the cartesian squares for the descended opens.
If the index type is empty, the covering hypothesis forces V empty; take the empty
scheme over Y. This construction asserts only the chart squares, not global effectivity
or transport invariance of q. -/
theorem exists_glued_effective_model_charts
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i, IsPullback (q i) (U i).ι (j i) q₀) := by sorry

end CategoryTheory.Over.DescentDatum
