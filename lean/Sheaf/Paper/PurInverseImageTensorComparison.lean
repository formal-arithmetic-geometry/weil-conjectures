/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-! Comparison constructions for inverse image along a scheme isomorphism. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private theorem inverseSection_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : Y.ProEt) (s : F.val.obj (op V)) :
    purInverseImageSection g O F V s =
      AlgebraicGeometry.ProEtaleTensorComparison.inverseSection g F V s := by
  rfl

private theorem tensorSection_eq {X : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    purTensorSection O F G V s t =
      AlgebraicGeometry.ProEtaleTensorComparison.pure F G V s t := by
  rfl

set_option backward.isDefEq.respectTransparency false in
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

/-- The normalized tensor comparison, natural in its first variable.
Source: Stacks Project, `sites-modules.tex`, Tags 03CY and 03EL
(blueprint: lem-pur-inverse-image-tensor-comparison).
Proof: identify inverse image under the scheme isomorphism with reindexing along the
inverse site equivalence, transporting the module action through the same ring
identification. Reindexing the sectionwise tensor presheaf gives the tensor presheaf
of the reindexed factors, since both restriction maps send a pure tensor to the
pure tensor of the restricted sections. Reindexing commutes with module
sheafification: transport its universal factorization property through the inverse
site equivalence. Sheafify the presheaf identification and conjugate by the canonical
inverse-image identification. Compatibility of those identifications with their
adjunction units gives the displayed pure-tensor equation. For a map in the first
factor, both composites agree on pure tensors by naturality of the unit; the
sheafification universal property and algebraic tensor generation give equality.
The construction requires no nonzero-ring or nonempty-site hypothesis. -/
theorem purInverseImageTensorComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ σ : ∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
      (proEtaleModuleInverseImage g O).obj
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F) ≅
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
          ((proEtaleModuleInverseImage g O).obj G)).obj
          ((proEtaleModuleInverseImage g O).obj F),
        (∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (V : Y.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)),
          (σ F G).hom.val.app (op ((proEtaleBaseChange g).obj V))
            (purInverseImageSection g O _ V (purTensorSection O F G V s t)) =
          purTensorSection ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
            ((proEtaleModuleInverseImage g O).obj F)
            ((proEtaleModuleInverseImage g O).obj G) ((proEtaleBaseChange g).obj V)
            (purInverseImageSection g O F V s) (purInverseImageSection g O G V t)) ∧
        (∀ (F G F' : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (a : F ⟶ F'),
            (proEtaleModuleInverseImage g O).map
                ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).map a) ≫
              (σ F' G).hom =
            (σ F G).hom ≫
              (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
                ((proEtaleModuleInverseImage g O).obj G)).map
                ((proEtaleModuleInverseImage g O).map a))  := by
  let σ := fun F G =>
    @asIso _ _ _ _
      (AlgebraicGeometry.ProEtaleTensorComparison.comparison g O F G)
      (AlgebraicGeometry.ProEtaleTensorComparison.inverseImage_tensor_comparison
        (𝟙 X) g O F G).1
  refine ⟨σ, ?_, ?_⟩
  · intro F G V s t
    have hPure := (AlgebraicGeometry.ProEtaleTensorComparison.inverseImage_tensor_comparison
      (𝟙 X) g O F G).2.1
    change (AlgebraicGeometry.ProEtaleTensorComparison.comparison g O F G).val.app
      (op ((proEtaleBaseChange g).obj V)) _ = _
    simpa only [← inverseSection_eq, ← tensorSection_eq] using hPure V s t
  · intro F G F' a
    have hNat := (AlgebraicGeometry.ProEtaleTensorComparison.inverseImage_tensor_comparison
      (𝟙 X) g O F G).2.2.1
    change _ ≫ AlgebraicGeometry.ProEtaleTensorComparison.comparison g O F' G =
      AlgebraicGeometry.ProEtaleTensorComparison.comparison g O F G ≫ _
    have h := hNat F' G a (𝟙 G)
    rw [AlgebraicGeometry.ProEtaleTensorComparison.tensorMap,
      AlgebraicGeometry.ProEtaleTensorComparison.tensorMap] at h
    erw [(proEtaleModuleInverseImage g O).map_id G] at h
    simpa only [secondMap_id, Category.comp_id] using h

end AlgebraicGeometry.Scheme
