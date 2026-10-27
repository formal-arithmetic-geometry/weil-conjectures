module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Right exact linear module functors preserving direct sums

Source: Stacks Project, Tag 0EX3, `lemma-top-cohomology-functor`, proof of (b),
the exercise on right exact linear functors
(blueprint: lem-sfb-linear-right-exact-module-functor-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- A right exact linear module functor preserving all direct sums is canonically tensoring
by its value on the ring. Source: Stacks Project, Tag 0EX3, proof of (b), exercise
(blueprint: lem-sfb-linear-right-exact-module-functor-tensor).

Proof: Set N = F(R). Additivity and scalar compatibility on Hom modules make
(x,m) ↦ F(u_m)(x) bilinear, so the tensor universal property gives theta_M.
For a : M → M', a u_m = u_{a(m)} proves naturality on pure tensors. At R the
map is x tensor r ↦ r x, with inverse x ↦ x tensor 1.
For a free module P_I = R^(I), construct inverse maps between N tensor P_I and
N^(I) by x tensor (sum r_i e_i) ↦ sum iota_i(r_i x) and
sum iota_i(x_i) ↦ sum x_i tensor e_i. These formulas include the empty sum.
The colimit universal property (def-weil-pbc-category-colimit) identifies theta
on P_I with the canonical direct-sum comparison, so it is an isomorphism.
Present any M by P_J → P_I → M → 0, using I = M and J the kernel of the
surjection e_m ↦ m; these sets lie in the same universe. Tensor right exactness
(lem-weil-pbc-tensor-right-exact, Mathlib `lTensor_exact`) and the assumed right
exactness of F give exact rows. Naturality and the isomorphisms on P_J and P_I
give surjectivity of theta_M by lifting an element through F(P_I), then through
theta_{P_I}. For injectivity, lift a kernel element through N tensor P_I; its
image under theta_{P_I} lifts through F(P_J). Lift again through theta_{P_J}
and subtract its image. Injectivity on P_I shows the original lift is in the
image from N tensor P_J, hence its image in N tensor M is zero. The inverse
linear maps are natural by the naturality of theta and its bijectivity. -/
theorem exists_tensorLeft_iso_of_rightExact_preservesCoproducts
    (R : Type u) [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R]
    (hRightExact : ∀ (M₁ M₂ M₃ : ModuleCat.{u} R)
      (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃),
      Function.Exact f g → Function.Surjective g →
      Function.Exact (F.map f) (F.map g) ∧ Function.Surjective (F.map g))
    (hSums : ∀ (I : Type u), PreservesColimitsOfShape (Discrete I) F) :
    ∃ θ : tensorLeft (F.obj (ModuleCat.of R R)) ≅ F,
      ∀ (M : ModuleCat.{u} R) (x : F.obj (ModuleCat.of R R)) (m : M),
        (θ.hom.app M) (TensorProduct.tmul R x m) =
          (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))) x := by
  sorry

end ModuleCat
