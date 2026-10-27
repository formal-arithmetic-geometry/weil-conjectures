/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-! # Effective fppf descent for finite locally free covers of fixed degree

Source: Stacks Project, Descent, Tags 0245, 02VO, 023Q;
Morphisms, Tag 02KD (blueprint: lem-sfb-finite-locally-free-fppf-descent).

The objects of the groupoid over `T` are `Z : Over T` with
`Z.hom.IsFiniteLocallyFreeOfDegree d`; its arrows are isomorphisms in `Over T`.
The pullback functor is the existing `Over.pullback`, which acts on arrows by `mapIso`.
The three clauses below express stability, effective object descent, and unique arrow
descent. The Cartesian squares and transport equality are the existing geometric
`SchemeCoverDescentDatum.IsEffective` formula, retaining the realizing object so its
fixed degree can be asserted. Thus the descended object realizes the given transitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite locally free covers of degree `d` and their isomorphisms form an fppf stack.

Source: Stacks Project, Descent, Tags 0245 (affine effectivity), 02VO (finite locally
free descent), 023Q (representable sheaves); Morphisms, Tag 02KD (base change)
(blueprint: lem-sfb-finite-locally-free-fppf-descent).

Proof:
1. Finiteness, flatness and local finite presentation are preserved by base change
   (`lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-flat-morphism-base-change`,
   `lem-weil-pbc-qcqs-morphism-permanence`). Fibre rank is unchanged
   (`lem-weil-pbc-finite-flat-rank-iso`), so the degree stays `d`. The functor
   `Over.pullback` sends isomorphisms to isomorphisms; its identity and composition
   comparisons are the canonical fibre-product comparisons (`def-pc-fibre-product`).
2. Each local cover is finite, hence affine (`def-weil-finite-integral-morphism`).
   Convert the family datum to its coproduct singleton datum
   (`lem-trf-fppf-family-coproduct-descent-encoding`). The coproduct morphism is affine:
   use affine covers in each summand, disjointness of the summands
   (`lem-weil-pbc-scheme-coproduct-family`) and target locality
   (`pqf-lem-affine-local-target`). This applies to infinite families too.
3. Apply affine fpqc effectivity (`lem-galois-fpqc-affine-descent-effective`), then
   restrict the realization along the coprojections using the fixed-realization
   comparison in `lem-trf-fppf-family-coproduct-descent-encoding`. This gives precisely
   the displayed Cartesian squares and invariance under the specified transitions.
4. An fppf cover is fpqc (`lem-trf-fppf-covering-is-fpqc`). On this same realization,
   descend finiteness, flatness and local finite presentation separately
   (`lem-weil-pbc-fpqc-descend-finite`, `lem-weil-pbc-fpqc-descend-flat`,
   `lem-weil-pbc-fpqc-descend-locally-finite-presentation`).
5. Joint surjectivity lifts every base point into one covering member. Base-change
   invariance of rank (`lem-weil-pbc-finite-flat-rank-iso`) identifies its fibre degree
   with the local degree `d`; hence the global cover has degree `d`.
6. For compatible local isomorphisms, compose with the projections to the second
   global scheme. The displayed pairwise equalities allow unique gluing by fpqc
   representable descent (`lem-weil-pbc-fpqc-representable-descent`) on the pullback
   cover (`lem-galois-fpqc-covering-base-change`). Uniqueness with target `T` makes
   the resulting map a `T`-map. Fibre-product uniqueness identifies its pullbacks
   with the original isomorphisms.
7. Glue the compatible inverses in the same way. Uniqueness makes both composites
   identities and proves uniqueness of the global isomorphism. An empty cover
   forces an empty base; all schemes over it are empty. Degree zero and empty
   covering members are included throughout. -/
theorem finiteLocallyFree_fppf_descent (S : Scheme.{u}) (T : Over S) (d : ℕ) :
    (∀ (Z : Over T.left), Z.hom.IsFiniteLocallyFreeOfDegree d →
      ∀ (T' : Scheme.{u}) (g : T' ⟶ T.left),
        (pullback.snd Z.hom g).IsFiniteLocallyFreeOfDegree d) ∧
    (∀ (I : Type (u + 1)) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T.left),
      Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T.left →
      (∀ (D : SchemeCoverDescentDatum f),
        (∀ i, (D.localScheme i).hom.IsFiniteLocallyFreeOfDegree d) →
        ∃ (Z : Over T.left) (q : ∀ i, (D.localScheme i).left ⟶ Z.left),
          Z.hom.IsFiniteLocallyFreeOfDegree d ∧
          (∀ i, IsPullback (q i) (D.localScheme i).hom Z.hom (f i)) ∧
          ∀ (B : Scheme.{u}) (p : B ⟶ T.left) (i j : I)
            (a : B ⟶ U i) (b : B ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
            (x : (D.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))),
            ((D.representation j).homEquiv.symm
              ((D.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫ q j =
              ((D.representation i).homEquiv.symm x).left ≫ q i) ∧
      (∀ (Z W : Over T.left), Z.hom.IsFiniteLocallyFreeOfDegree d →
        W.hom.IsFiniteLocallyFreeOfDegree d →
        ∀ (e : ∀ i, (Over.pullback (f i)).obj Z ≅ (Over.pullback (f i)).obj W),
          (∀ i j,
            pullback.fst (pullback.fst Z.hom (f i)) (pullback.fst Z.hom (f j)) ≫
                (e i).hom.left ≫ pullback.fst W.hom (f i) =
              pullback.snd (pullback.fst Z.hom (f i)) (pullback.fst Z.hom (f j)) ≫
                (e j).hom.left ≫ pullback.fst W.hom (f j)) →
          ∃! b : Z ≅ W, ∀ i, (Over.pullback (f i)).mapIso b = e i)) := by
  sorry

end AlgebraicGeometry
