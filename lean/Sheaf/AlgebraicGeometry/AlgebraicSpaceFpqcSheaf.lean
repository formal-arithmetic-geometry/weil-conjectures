/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent
import Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood

/-!
# Morphisms to an algebraic space satisfy fpqc descent

Source: Stacks Project, Descent of Spaces, Tag 04P2,
`lemma-fpqc-universal-effective-epimorphisms`, specialized to scheme domains;
Properties of Spaces, Tag 0APL, `proposition-sheaf-fpqc` (Gabber's proof)
(blueprint: lem-a1-algebraic-space-fpqc-sheaf).

Maps from an `S`-scheme to `E` are sections of its defining fppf sheaf, by Yoneda.
The overlap is the scheme pullback with its structure map through the first projection;
`Limits.pullback.condition_assoc` makes the second projection an `S`-morphism too.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Compatible maps from an fpqc covering of schemes to an algebraic space descend
uniquely, and equality of two maps is detected on the covering. The index type may be
empty. No separatedness or finiteness hypothesis is imposed on the algebraic space.
Source: Stacks Project, Tags 04P2 and 0APL
(blueprint: lem-a1-algebraic-space-fpqc-sheaf).

Proof (the seven steps of the node):
1. For two locally equal maps `a,b : T → E`, the representable diagonal gives their
   equalizer scheme `P → T`, a monomorphism. The local equalities give maps to `P`;
   monicity makes them compatible. Scheme fpqc descent
   (`lem-weil-pbc-fpqc-representable-descent`) glues `r : T → P`. Its composite to `T`
   is the identity by scheme descent uniqueness with target `T`. Pulling the equality
   on `P` back by this section proves `a=b`.
2. On all schemes consider the presheaf `H(A)` of pairs `(s : A → S, x ∈ E(A,s))`.
   Scheme morphisms glue Zariski locally, and the fppf sheaf condition glues `x` after
   fixing `s`, including the empty cover. Thus `H` is a Zariski sheaf.
   `lem-a1-fpqc-sheaf-affine-criterion` reduces existence to singleton affine fpqc covers
   `f : T' → T`. Scheme descent first descends the structure map to `S`.
3. For compatible `c : T' → E`, `lem-a1-qc-map-affine-etale-neighbourhood` supplies
   affine `U → E` with `V = T' ×_E U → T'` surjective, étale, separated and locally
   quasi-finite. The two pullbacks of `V` to `T' ×_T T'` identify by keeping the
   `U` coordinate. The triple-product cocycle follows by the fibre-product universal
   property (`def-pd-descent-datum`, `def-pc-fibre-product`).
4. `lem-a1-separated-lqf-fpqc-effective-descent` gives `W → T` and an isomorphism
   `W ×_T T' ≅ V` inducing this datum. `lem-galois-fpqc-descend-etale` makes `W → T`
   étale; surjectivity follows by lifting a point first to `T'` and then to `V`.
5. The map `W ×_T T' → V → U` is invariant under the datum since its `U` coordinate
   is fixed. The fpqc cover `W ×_T T' → W`
   (`lem-galois-fpqc-covering-base-change`) and scheme descent give `b : W → U`.
   Scheme descent uniqueness with target `S` shows `b` is an `S`-map. Its composite
   with `U → E` pulls back to `c` on `W ×_T T'`.
6. On `W ×_T W` the two resulting maps to `E` agree after the fpqc base change by
   `T'`, hence agree by step 1. The étale surjection `W → T` is an fppf covering
   (`def-weil-etale-morphism`, `def-pc-fppf-site`), so the defining fppf sheaf of `E`
   glues them to `a : T → E`. Check `af=c` on the fppf cover `V → T'` and use its
   sheaf uniqueness. Step 1 gives uniqueness of `a`.
7. The affine criterion now gives descent for every fpqc family. Apply it to
   `(T.hom ∘ v_i,e_i)`. Scheme descent uniqueness shows the glued structure map is
   `T.hom`, so the glued section is over the prescribed `S`-scheme `T`. Step 1 also
   gives the equality clause. Only the auxiliary chart was separated; no condition
   on separatedness or finiteness of `E` entered the argument. -/
theorem existsUnique_section_and_eq_of_fpqc_cover
    {S : Scheme.{u}} (E : AlgebraicSpace S) (T : Over S) {I : Type w}
    (T' : I → Scheme.{u}) (v : ∀ i : I, T' i ⟶ T.left)
    (hcover : Presieve.ofArrows T' v ∈ Scheme.fpqcPrecoverage T.left) :
    (∀ e : ∀ i : I, E.obj.obj.obj (op (Over.mk (v i ≫ T.hom))),
      (∀ i j : I,
        E.obj.obj.map
            (Over.homMk
              (U := Over.mk (Limits.pullback.fst (v i) (v j) ≫ v i ≫ T.hom))
              (V := Over.mk (v i ≫ T.hom))
              (Limits.pullback.fst (v i) (v j)) rfl).op (e i) =
          E.obj.obj.map
            (Over.homMk
              (U := Over.mk (Limits.pullback.fst (v i) (v j) ≫ v i ≫ T.hom))
              (V := Over.mk (v j ≫ T.hom))
              (Limits.pullback.snd (v i) (v j))
              (Limits.pullback.condition_assoc (f := v i) (g := v j) T.hom).symm).op (e j)) →
      ∃! a : E.obj.obj.obj (op T),
        ∀ i : I, E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op a = e i) ∧
    (∀ a b : E.obj.obj.obj (op T),
      (∀ i : I, E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op a =
        E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op b) → a = b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
