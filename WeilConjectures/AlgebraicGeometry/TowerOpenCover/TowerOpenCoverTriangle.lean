/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleCore
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleTail

/-! # The open-cover triangle of varying-coefficient towers

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-triangle).

Index `n : ℕ` denotes the paper's positive coefficient level `n + 1`.
The sequence-site presentation `SpTowerShriek.D` is the ordinary derived category
of strict towers, identified sectionwise with `spCoefficientTowers` by `Base.realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v₀ v₁ v₂ u₀ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- The distinguished open-cover triangle, natural on the ordinary unbounded derived
category, with its compact-support image and its normalized finite evaluations.
`IsPullback` identifies `W` with `U ∩ V`, and `cover` says that the two opens cover `X`.
The last three equalities fix the evaluation isomorphism on all three vertices; hence
its last commuting square identifies the finite boundary with evaluation of this boundary.

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-triangle).

Proof:
1. Represent M by a complex of strict varying-coefficient towers. Apply
   lem-dla1-site-open-cover-extension-sequence in each degree and at each level.
   The maps are the nested-open counits with signs (+,-), and the sum of counits.
   The semilinear-derived-sections operations are levelwise and their ordinary
   adjunctions commute with scalar restriction, so these maps form tower maps.
   Componentwise kernels and cokernels (det-sp-coefficient-towers-abelian) give
   a short exact sequence of tower complexes, natural in the complex.
2. Apply lem-weil-pbc-complex-ses-triangle. Its natural connecting arrow gives
   delta and the distinguished triangle. Exactness of restriction and extension
   makes their termwise operations preserve quasi-isomorphisms. Every derived
   morphism is a word in chain maps and inverses of quasi-isomorphisms, so all
   three naturality squares descend to the derived category.
3. Exact open extension preserves boundedness below. For bounded-below M the
   compactification functor is Rp_* after j_!. The exact-functor triangulation
   lemma and lem-weil-pbc-derived-direct-image-triangulated show that their
   composite, with its composite shift isomorphism, preserves this triangle.
4. Evaluation is exact, termwise and triangulated. The normalized level open
   adjunctions and pullback compositors identify its first two arrows with the
   finite signed nested counits and finite sum of counits. Its shift comparison
   identifies the last arrow. Thus the specified vertex comparisons give the
   displayed triangle isomorphism. This includes every positive level.
The arguments also cover the zero object, empty scheme, empty opens, redundant
covers and U=V=X; no normalization or constructibility of M is used. -/
theorem tower_open_cover_triangle {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (_intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (_cover : Set.range jU ∪ Set.range jV = Set.univ) :
    ∃ delta : ∀ M : SpTowerShriek.D l E X, M ⟶ ((support l E b o jW).obj M)⟦(1 : ℤ)⟧,
      (∀ M : SpTowerShriek.D l E X,
        Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
          (second l E b o jU jV M) (delta M) ∈ distTriang (SpTowerShriek.D l E X)) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        (support l E b o jW).map h ≫ first l E b o aU aV jU jV jW wU wV N =
          first l E b o aU aV jU jV jW wU wV M ≫
            biprod.map ((support l E b o jU).map h) ((support l E b o jV).map h)) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        biprod.map ((support l E b o jU).map h) ((support l E b o jV).map h) ≫
          second l E b o jU jV N = second l E b o jU jV M ≫ h) ∧
      (∀ (M N : SpTowerShriek.D l E X) (h : M ⟶ N),
        h ≫ delta N = delta M ≫ (shiftFunctor _ (1 : ℤ)).map
          ((support l E b o jW).map h)) ∧
      (∀ {Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
        (M : DerivedCategory.Plus (SpTowerShriek.S l E X)),
        (SpTowerShriek.F l E b o c).mapTriangle.obj
          (Triangle.mk (first l E b o aU aV jU jV jW wU wV M.obj)
            (second l E b o jU jV M.obj) (delta M.obj)) ∈
          distTriang (SpTowerShriek.D l E Y)) ∧
      (∀ (M : SpTowerShriek.D l E X) (n : ℕ),
        ∃ d : (SpTowerShriek.Ev l E X n).obj M ⟶
          ((finiteSupport l E b jW n).obj ((SpTowerShriek.Ev l E X n).obj M))⟦(1 : ℤ)⟧,
        ∃ e : (SpTowerShriek.Ev l E X n).mapTriangle.obj
            (Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
              (second l E b o jU jV M) (delta M)) ≅
          Triangle.mk
            (biprod.lift
              (finiteAlpha l E b aU jU jW wU n ((SpTowerShriek.Ev l E X n).obj M))
              (-finiteAlpha l E b aV jV jW wV n ((SpTowerShriek.Ev l E X n).obj M)))
            (biprod.desc
              ((finiteAdjunction l E b jU n).counit.app ((SpTowerShriek.Ev l E X n).obj M))
              ((finiteAdjunction l E b jV n).counit.app ((SpTowerShriek.Ev l E X n).obj M))) d,
          e.hom.hom₁ = (supportEvaluation l E b o jW n).hom.app M ∧
          e.hom.hom₂ = biprod.lift
            ((SpTowerShriek.Ev l E X n).map biprod.fst ≫
              (supportEvaluation l E b o jU n).hom.app M)
            ((SpTowerShriek.Ev l E X n).map biprod.snd ≫
              (supportEvaluation l E b o jV n).hom.app M) ∧
          e.hom.hom₃ = 𝟙 _) := by
  obtain ⟨delta, hcore⟩ := tower_open_cover_core l E b o
    aU aV jU jV jW _intersection wU wV _cover
  obtain ⟨hcompact, hevaluation⟩ := tower_open_cover_tail l E b o
    aU aV jU jV jW wU wV delta hcore.1
  refine ⟨delta, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2, hcompact, hevaluation⟩

end AlgebraicGeometry.ProEtale.TowerOpenCover
