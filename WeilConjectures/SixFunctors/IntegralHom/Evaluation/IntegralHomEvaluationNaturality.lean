/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationTransport

/-! # First-variable naturality of normalized integral evaluation

## References

* [Stacks, Tag 08J9]
* [Stacks, Tag 06YS]
* [Stacks, Tag 06YU]
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralHom

/-- The representative-normalized counits form a natural evaluation in the Hom source.
This concerns a single arbitrary ring sheaf and a supplied presentation; it constructs
neither tensor, symmetry nor any scalar-reduction presentation. -/
theorem evaluation_naturality (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (K K' W : Derived.{u, u} X R) (f : K' ⟶ K) :
    a.tensor.map (Prod.mkHom (𝟙 K')
      ((hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
        (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W := by
  obtain ⟨S, e, hc⟩ := tensorPresentation_counit_transport X R a
  rw [← hc K' W, ← hc K W]
  exact transportedCounit_naturality X R a S e K K' W f

end WeilConjectures.IntegralHom
