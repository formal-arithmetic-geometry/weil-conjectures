/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.IntegralMatrixModelData

/-! # Simultaneous finite matrix models for integral local reductions

Source: Stacks 093J, 093M, 06YQ, 06YY, 07A6.
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe r t w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)
variable [hD : ∀ (D : Type (r + 1)) [Category.{r} D] [Abelian D],
  HasDerivedCategory.{w} D]

/-- A given scalar free resolution gives a completed short exact sequence and simultaneous
matrix models with their actual quotient maps.

Source: Stacks 093J, 093M, 06YQ, 06YY, 0E8K, 07A6; original matrix-reduction node,
steps 1--4 (blueprint: lem-sp-integral-matrix-local-resolution).

Proof: constant sheafification is exact. The completed coefficient ring is flat over
constant scalars by 093M, so scalar extension of the supplied resolution is exact.
Restrict to U and compose its augmentation with the inverse of the specified local
model isomorphism. Identify its finite free terms by b tensor (a_i) mapped to (ba_i),
with inverse the sum of b_i tensor e_i. Its cone resolves L on the slice and is K-flat
by 06YQ. Exact slice restriction preserves K-flat resolutions; the pure-tensor
restriction comparison identifies the global derived reduction with the slice
calculation. Compute all reductions with this one augmented resolution. The free
basis maps give exactly the entrywise reduced differential and the zero terms in
other degrees. The normalized coefficient adjunction sends x to x tensor 1 and its
adjunct sends x tensor a to a g(x); hence each quotient map is x tensor a mapped to
x tensor q(a). In both bases this is scalarReduction. Naturality of the K-flat
comparison and its localization square give transition_square, also for m=n.
No new cover or scalar resolution is chosen for any level. Zero ranks and empty
slices use the same tensor and cone identities.
-/
theorem local_resolution
    (S : Scheme.{t}) (site : C ≌ S.ProEt)
    (topology : J = site.functor.inducedTopology (Scheme.ProEt.topology S))
    (L : Modules J (completion l E J)) (U : C) (N : ModuleCat.{r} (Scalars l E))
    (hN : HasFiniteScalarConstantModelOn J (Scalars l E) (completion l E J)
      (scalarMap l E J) L U N)
    {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (p : (Fin b → Scalars l E) →ₗ[Scalars l E] N)
    (hd : Function.Injective (Matrix.toLin' d))
    (hex : Function.Exact (Matrix.toLin' d) p) (hp : Function.Surjective p) :
    ∃ eN : ((model l E J).obj N).over U ≅ L.over U,
      ∃ hz : ((model l E J).map (ModuleCat.ofHom (Matrix.toLin' d))).over U ≫
        ((model l E J).map (ModuleCat.ofHom p)).over U ≫ eN.hom = 0,
      (ShortComplex.mk
        (((model l E J).map (ModuleCat.ofHom (Matrix.toLin' d))).over U)
        (((model l E J).map (ModuleCat.ofHom p)).over U ≫ eN.hom) hz).ShortExact ∧
      Nonempty (SimultaneousModels l E J L U d) := by sorry

end IntegralMatrix
end AlgebraicGeometry.ProEtale
