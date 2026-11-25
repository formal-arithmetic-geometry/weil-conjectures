/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationTransport

/-! # First-variable naturality of normalized integral evaluation

We show that the representative-normalized counits of a tensor presentation over an arbitrary
ring sheaf form an evaluation natural in the Hom source.

## Implementation details

The counits are identified with the transport of the counits of the native closed symmetric
monoidal structure on the derived category, whose evaluation is natural; naturality of the
tensor identification and of the symmetry carries this over. No boundedness, finite-Tor or
constructibility hypothesis is needed.

## References

* Stacks Project, Tags 06YS, 06YU, 08J9.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralHom

/-- The counits of a tensor presentation form an evaluation natural in the Hom source: for
`f : K' ⟶ K`, the counit at `K'` precomposed with `Hom(f, W)` agrees with the counit at `K`
precomposed with `f ⊗ 𝟙`. -/
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
