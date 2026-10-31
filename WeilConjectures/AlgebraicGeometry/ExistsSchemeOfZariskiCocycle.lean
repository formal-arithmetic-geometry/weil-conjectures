/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Relative gluing of schemes over a Zariski cover

Source: blueprint, sec-curve-estimates, lem-galois-glue; Stacks Project, Tags 01JB,
01JC and 01JR. (blueprint: lem-galois-glue)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Schemes over a Zariski cover glue along a normalized cocycle, uniquely with their charts.

Source: blueprint, sec-curve-estimates, lem-galois-glue; Stacks Project, Tags 01JB,
01JC and 01JR. (blueprint: lem-galois-glue)

The two equations in `hφ` say that the transition preserves both coordinates in
`Yᵢ ×[Y] Yⱼ`. The hypothesis `hcocycle` expresses the triple-overlap equation on
arbitrary test schemes: `a`, `d`, and `c` lie in overlaps `(i,j)`, `(j,k)`, and `(i,k)`;
their three antecedents identify the intermediate Pⱼ-coordinate, initial Pᵢ-coordinate,
and final Yₖ-coordinate. Equality of the final Pₖ-coordinates is the cocycle equation.
The other coordinate is already fixed by `hφ`, so equality of these coordinates is
equivalent to equality of the restricted transition morphisms by the pullback property.
The compatibility equations in the conclusion use the chart embeddings
`(e i).inv ≫ pullback.fst p (b i)` and hence include the chosen local identifications.

Proof:
1. By lem-weil-pbc-open-preimage-fibre-product (01JR), `Pᵢ ×[Y] Yⱼ` is the open inverse
   image of Yⱼ in Pᵢ. The equations `hφ` identify the triple-overlap domains. Normalization
   and the cocycle imply that the reversed transition is the inverse transition.
2. Apply lem-weil-pbc-glue-schemes (01JB, 01JC) to these open overlaps and transitions.
   This gives P with covering open chart embeddings qᵢ. Their maps to Y agree on overlaps,
   so lem-weil-pbc-scheme-morphism-gluing gives a unique p with qᵢ ≫ p = fᵢ ≫ bᵢ.
3. The image of qᵢ equals p⁻¹(Yᵢ). One inclusion follows from this equation. For the other,
   express a point in some chart j; its image in Yᵢ places it in the overlap (j,i), and
   the transition expresses it in chart i. Open immersions identify the corresponding
   open subschemes, not merely their underlying point sets (def-weil-open-immersion).
4. By 01JR this inverse image is `P ×[Y] Yᵢ`, giving eᵢ over Yᵢ. Its base equation follows
   by cancelling the open immersion bᵢ. The overlap equation for qᵢ gives compatibility.
5. For any other compatible solution, glue the local comparison isomorphisms in both
   directions using lem-weil-pbc-scheme-morphism-gluing. Check their composites and their
   maps to Y on the covering charts. The same lemma gives uniqueness of the isomorphism
   preserving the charts. Thus uniqueness concerns the local identifications as well.
-/
theorem exists_scheme_of_zariski_cocycle
    (Y : Scheme.{u}) (I : Type v) (Yᵢ Pᵢ : I → Scheme.{u})
    (b : ∀ i : I, Yᵢ i ⟶ Y) [∀ i : I, IsOpenImmersion (b i)]
    (hcover : ∀ y : Y, ∃ (i : I) (x : Yᵢ i), b i x = y)
    (f : ∀ i : I, Pᵢ i ⟶ Yᵢ i)
    (φ : ∀ i j : I, pullback (f i ≫ b i) (b j) ≅ pullback (f j ≫ b j) (b i))
    (hφ : ∀ i j : I,
      (φ i j).hom ≫ pullback.fst (f j ≫ b j) (b i) ≫ f j =
        pullback.snd (f i ≫ b i) (b j) ∧
      (φ i j).hom ≫ pullback.snd (f j ≫ b j) (b i) =
        pullback.fst (f i ≫ b i) (b j) ≫ f i)
    (hφ_self : ∀ i : I, φ i i = Iso.refl _)
    (hcocycle : ∀ (i j k : I) (T : Scheme.{u})
      (a : T ⟶ pullback (f i ≫ b i) (b j))
      (d : T ⟶ pullback (f j ≫ b j) (b k))
      (c : T ⟶ pullback (f i ≫ b i) (b k)),
      a ≫ (φ i j).hom ≫ pullback.fst (f j ≫ b j) (b i) =
        d ≫ pullback.fst (f j ≫ b j) (b k) →
      a ≫ pullback.fst (f i ≫ b i) (b j) =
        c ≫ pullback.fst (f i ≫ b i) (b k) →
      d ≫ pullback.snd (f j ≫ b j) (b k) =
        c ≫ pullback.snd (f i ≫ b i) (b k) →
      d ≫ (φ j k).hom ≫ pullback.fst (f k ≫ b k) (b j) =
        c ≫ (φ i k).hom ≫ pullback.fst (f k ≫ b k) (b i)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y) (e : ∀ i : I, pullback p (b i) ≅ Pᵢ i),
      (∀ i : I, (e i).hom ≫ f i = pullback.snd p (b i)) ∧
      (∀ i j : I,
        pullback.fst (f i ≫ b i) (b j) ≫ (e i).inv ≫ pullback.fst p (b i) =
          (φ i j).hom ≫ pullback.fst (f j ≫ b j) (b i) ≫
            (e j).inv ≫ pullback.fst p (b j)) ∧
      ∀ (P' : Scheme.{u}) (p' : P' ⟶ Y) (e' : ∀ i : I, pullback p' (b i) ≅ Pᵢ i),
        (∀ i : I, (e' i).hom ≫ f i = pullback.snd p' (b i)) →
        (∀ i j : I,
          pullback.fst (f i ≫ b i) (b j) ≫ (e' i).inv ≫ pullback.fst p' (b i) =
            (φ i j).hom ≫ pullback.fst (f j ≫ b j) (b i) ≫
              (e' j).inv ≫ pullback.fst p' (b j)) →
        ∃! h : P ≅ P', h.hom ≫ p' = p ∧
          ∀ i : I, (e i).inv ≫ pullback.fst p (b i) ≫ h.hom =
            (e' i).inv ≫ pullback.fst p' (b i) := by
  sorry

end AlgebraicGeometry.Scheme
