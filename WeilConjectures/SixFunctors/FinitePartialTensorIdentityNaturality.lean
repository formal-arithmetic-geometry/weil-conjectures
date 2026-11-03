/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityNaturalityCoordinates

/-! Naturality of the explicit finite partial tensor comparison.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The pullback tensor comparison is natural in both inputs. This is the
coordinate naturality calculation for the fixed-scalar tensor comparison and
the two pullback realizations described in the parent theorem.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, together with the
naturality clauses of the realization comparisons.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality). -/
theorem finitePartialTensor_identityNaturality
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    ∀ (M M' : sixFunctorFiniteCategory D C E n hn X)
      (L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left)
      (f : M ⟶ M') (g : L ⟶ L'),
      U.map (T.map (Prod.mkHom f g)) ≫
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M' L').hom =
        (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
          T.map (Prod.mkHom (U.map f) (V.map g)) := by
  dsimp
  intro M M' L L' f g
  apply (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
    (hn := hn) X).map_injective
  apply (cancel_mono (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
    ((S.finite.pull (𝟙 X)).obj M') L').hom).1
  simpa only [Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    Functor.map_comp, Category.assoc] using
    (finitePartialTensor_identityNaturality_coordinates S X M M' L L' f g)


end WeilConjectures
