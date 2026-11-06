/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality

/-! # Independence of the source-only stalk comparison from its representative

Source: Stacks Project, Tags 06Y6, 08IB and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-base-change-source-representative-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem exists_stalkCohomologyComparison (Y : Scheme.{u}) (p : Y) (i : ℤ) :
    ∃ δ : SingleComplexBaseChange.comparisonStalkCohomology Y p i ≅
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i ⋙
            RingedSpace.moduleStalkFunctor Y.toRingedSpace p,
      ∀ P, δ.hom.app (DerivedCategory.Q.obj P) =
        (SingleComplexBaseChange.comparisonStalkHomologyIso Y p P i).hom ≫
          (affineRepresentativeStalkIso Y p P i).inv := by
  let F := SingleComplexBaseChange.comparisonStalkCohomology Y p i
  let G := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i ⋙
      RingedSpace.moduleStalkFunctor Y.toRingedSpace p
  let ε : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    NatIso.ofComponents (fun P ↦
      SingleComplexBaseChange.comparisonStalkHomologyIso Y p P i ≪≫
        (affineRepresentativeStalkIso Y p P i).symm) (by
      intro P N a
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.comp_map]
      apply (cancel_mono (affineRepresentativeStalkIso Y p N i).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [G, Functor.comp_map]
      rw [affineRepresentativeStalkIso_naturality Y p a i]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact SingleComplexBaseChange.comparisonStalkHomologyIso_naturality Y p a i)
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  refine ⟨Localization.liftNatIso DerivedCategory.Q W
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G ε, ?_⟩
  intro P
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rfl

end AlgebraicGeometry
