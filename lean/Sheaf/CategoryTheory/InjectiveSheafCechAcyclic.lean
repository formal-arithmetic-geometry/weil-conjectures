import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Injective abelian étale sheaves are Čech-acyclic

Source: Stacks Project, sites-cohomology.tex, Lemma 03AW
(blueprint: lem-weil-pbc-injective-sheaf-cech-acyclic).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- An injective object `𝓘` of `Ab(X_ét)` (abelian sheaves on the small étale site, valued in
`AddCommGrpCat.{u + 1}` as in lem-weil-pbc-cech-vanishing-criterion) has zero Čech cohomology
`Ȟ^p(𝒰, 𝓘)` in every degree `p > 0`, for every covering `𝒰 = {f i : V i ⟶ U}` of an object `U`
indexed by any `I : Type (u + 1)` (finite or not, possibly empty). The Čech complex is the
recorded `cechComplexFunctor` of the family `i ↦ Over.mk (f i)` in `Over U`, whose finite
products are the fibre products `V i₀ ×_U ⋯ ×_U V iₚ`, applied to `𝓘` restricted to `Over U`.
Source: Stacks Project, Lemma 03AW, via Lemmas 03F6, 03AS, 03AT.
(blueprint: lem-weil-pbc-injective-sheaf-cech-acyclic)

Proof (the node's five steps). (1) With `O` the constant presheaf of rings `ℤ`, presheaves of
`O`-modules are presheaves of abelian groups, and the free complex `K_• = O_{𝒰,•}` of
lem-weil-pbc-free-cech-complex-exact is Stacks' `ℤ_{𝒰,•}`. (2) `𝓘` is injective as an abelian
presheaf by lem-weil-pbc-injective-abelian-sheaf-injective-presheaf, hence injective in
presheaves of `O`-modules. (3) By lem-weil-pbc-free-yoneda-presheaf-module,
`Hom(K_•, G) ≅ Č^•(𝒰, G)` naturally, precomposition with the face maps being restriction along
the projections. (4) `K_•` is exact in positive degrees by lem-weil-pbc-free-cech-complex-exact,
objectwise, so `im d_{p+1} = ker d_p` as subpresheaves. (5) A cocycle `s : K_p ⟶ 𝓘` (`p > 0`)
factors through `K_p ↠ im d_p ⊆ K_{p-1}`; injectivity extends it to `s' : K_{p-1} ⟶ 𝓘` with
`s = s' ∘ d_p`, so `H^p(Hom(K_•, 𝓘)) = 0`, i.e. `Ȟ^p(𝒰, 𝓘) = 0`. -/
theorem injective_sheaf_cech_acyclic
    (X : Scheme.{u})
    (𝓘 : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective 𝓘]
    (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (hc : Sieve.ofArrows V f ∈ X.smallEtaleTopology U) :
    ∀ (p : ℕ), 0 < p →
      IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
        ((Over.forget U).op ⋙ 𝓘.obj)).homology p) := by
  sorry

end CategoryTheory
