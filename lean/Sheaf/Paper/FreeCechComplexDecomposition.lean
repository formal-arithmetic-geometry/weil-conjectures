module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Sheaf.Paper.PowerSetComplexContractible

/-!
# Fibrewise comparison for the evaluated free Čech complex

Source: Stacks Project, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-free-cech-complex-fibre-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Exactness of the evaluated free Čech complex is equivalent to range/kernel equality
in each tuple complex over a fixed map to the base. This comparison does not assert that
any of the tuple complexes is exact.
Source: Stacks Project, sites-cohomology.tex, proof of Tag 03AT up to the direct-sum
of tuple complexes, and the first proof of Tag 03F5 with `O(W)` coefficients.
(blueprint: lem-weil-pbc-free-cech-complex-fibre-comparison)

Proof: In degree `n`, evaluation identifies the coproduct of free representable modules
with the free `O(W)`-module on pairs consisting of a tuple of indices and a map from `W`
to their fibre product over `U₀`. By the universal property of that fibre product, such a
pair is uniquely a map `φ : W ⟶ U₀` together with an `(n+1)`-tuple in
`Sφ = Σ i, {g : W ⟶ U i // g ≫ f i = φ}`. The inverse takes a tuple of compatible lifts
to the unique map to the fibre product. Extend these inverse bijections linearly. They
identify the evaluated degree with the direct sum over `φ` of `O(W)[Sφ^(n+1)]`.
Every projection deletes precisely the corresponding lift and preserves `φ`, so the
linear identifications intertwine the alternating differential with the direct sum of
`Algebra.powerSetComplexDifferential`, including its signs. Exactness at `p+1` is
range/kernel equality for the adjacent differentials. For a block diagonal differential,
its kernel is the direct sum of the block kernels and its image is the direct sum of the
block images: a kernel element has finite support, and if each block is an image, choose
preimages only for that finite support and add them. Conversely, embed a block kernel
into the direct sum and project a preimage to that block. This proves the equivalence,
without using contractibility or exactness of any tuple complex. -/
theorem freeCechComplex_exact_iff_fibres (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) (p : ℕ) :
    (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)))).ExactAt (p + 1) ↔
      ∀ φ : W ⟶ U₀,
        let S := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
        LinearMap.range (Algebra.powerSetComplexDifferential (O.obj (op W)) S (p + 1)) =
          LinearMap.ker (Algebra.powerSetComplexDifferential (O.obj (op W)) S p) := by
  sorry

end AlgebraicGeometry
