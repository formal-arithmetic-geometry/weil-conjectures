/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHomDefinitions
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

/-! Comparison constructions for inverse image along a scheme isomorphism. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private theorem tensorSection_eq {X : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    purTensorSection O F G V s t =
      AlgebraicGeometry.ProEtaleTensorComparison.pure F G V s t := by
  rfl

private theorem secondMap_id {Z : Scheme.{u}}
    {R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}}
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    SheafOfModules.siteSheafTensorSecondMap F (𝟙 G) = 𝟙 _ := by
  have h : SheafOfModules.siteTensorSecondMap F.val (𝟙 G.val) = 𝟙 _ := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  have hf : (𝟙 G : G ⟶ G).val = 𝟙 G.val := rfl
  dsimp only [SheafOfModules.siteSheafTensorSecondMap]
  rw [hf, h]
  exact CategoryTheory.Functor.map_id _ _

end AlgebraicGeometry.Scheme
