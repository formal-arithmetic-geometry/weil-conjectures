/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-! Natural comparison transformation for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-core) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem extendScalars_transport_naturality
    {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {a b : R₀ →+* S₀} (h : a = b) {M N : ModuleCat.{u} R₀} (s : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} a).map s ≫
        eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj N) h) =
      eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj M) h) ≫
        (ModuleCat.extendScalars.{u, u, u} b).map s := by
  subst b
  simp


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

private theorem tensorStalkIso_naturality (z : X')
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (a : P ⟶ Q) :
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    let E := ModuleCat.extendScalars.{u, u, u}
      ((tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
    (E.mapHomologicalComplex (.up ℤ)).map
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapHomologicalComplex (.up ℤ)).map a) ≫
        (tensorStalkIso f f' g g' sq z Q).hom =
      (tensorStalkIso f f' g g' sq z P).hom ≫
        ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).map
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map a) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z Q) i,
    Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) i]
  erw [← Category.assoc, extendScalars_transport_naturality
      (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1,
    Category.assoc]
  exact congrArg (fun k ↦ _ ≫ k)
    ((Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.naturality
      (a.f i))

end AlgebraicGeometry.SingleComplexBaseChange
