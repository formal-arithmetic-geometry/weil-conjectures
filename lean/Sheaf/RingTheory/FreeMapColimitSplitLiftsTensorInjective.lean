module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Tensor injectivity from eventually split finite basis lifts

Source: Stacks Project, Tag 05FQ, proof of `lemma-universally-injective-local`,
finite basis support reduction and final tensor-colimit argument
(blueprint: lem-trf-free-map-colimit-split-lifts-tensor-injective).
-/

@[expose] public section

universe u v w z t

open CategoryTheory CategoryTheory.Limits

namespace LinearMap

/-- A map out of a based free module is tensor injective if each finite basis span lifts
into a directed colimit diagram and that lift splits after every later transition.
The colimit module is `c.pt`, its structure maps are `(c.ι.app i).hom`, and the span of
`E` is `Submodule.span R (b '' (E : Set B))`. No flatness of the stages or compatibility
between the individual retractions is required.

Source: Stacks Project, Tag 05FQ, proof of `lemma-universally-injective-local`
(blueprint: lem-trf-free-map-colimit-split-lifts-tensor-injective).

Proof plan:
1. Write a tensor in the kernel as a finite sum of pure tensors. The union of the
   basis supports of its second factors is a finite `E`, so it is the image of a tensor
   `y` with second factor in the span of `E`. For an empty sum take `E` empty and `y = 0`.
   This uses the tensor-product and free-module definitions.
2. Tensor commutes with colimits (`lem-weil-pbc-tensor-commutes-with-colimits`). Use the
   tensor flip, defined on pure tensors, to put the test module on the left. The flips
   commute with transition maps and cocone legs by their formula on pure tensors.
3. Choose the lift `f` at `i`. The image of `y` under `1 ⊗ f` maps to zero in the tensor
   colimit, so filtered-colimit zero detection
   (`lem-weil-pbc-filtered-colimit-modules-elementwise`) kills it at some `j ≥ i`.
4. Tensor the retraction at this `j`. Its composite with the transitioned lift is the
   identity, hence `y = 0` and the original tensor is zero. Apply this kernel calculation
   to differences to obtain injectivity for every test module.
-/
theorem lTensor_injective_of_finite_basis_eventually_split_lifts
    {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    {B : Type z} (b : Module.Basis B R M)
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{max u v} R) (c : Cocone F) (hc : IsColimit c)
    (u : M →ₗ[R] c.pt)
    (hlifts : ∀ E : Finset B,
      ∃ (i : I) (f : Submodule.span R (b '' (E : Set B)) →ₗ[R] F.obj i),
        (c.ι.app i).hom.comp f = u.comp (Submodule.span R (b '' (E : Set B))).subtype ∧
        ∀ (j : I) (h : i ≤ j),
          ∃ s : F.obj j →ₗ[R] Submodule.span R (b '' (E : Set B)),
            s.comp ((F.map (homOfLE h)).hom.comp f) = LinearMap.id)
    (L : Type t) [AddCommGroup L] [Module R L] :
    Function.Injective (u.lTensor L) := by
  sorry

end LinearMap
