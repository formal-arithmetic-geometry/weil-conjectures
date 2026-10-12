/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import Sheaf.Algebra.Homology.InverseImageStalkScalarTransport

/-!
# The stalk complex of termwise tensor pullback

Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC.
(blueprint: lem-pc-tensor-pullback-stalk-complex)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A complex with the termwise tensor pullback formula has the expected stalk complex.
Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC, stalk comparison.
(blueprint: lem-pc-tensor-pullback-stalk-complex)

Proof: at `x`, the natural inverse-image stalk isomorphisms identify the source
ring and module stalks with those at `f x`. Their formulas on adjunction-unit germs,
and semilinearity of that unit, show that the module comparison respects the ring
comparison. Compose the inverse ring-stalk isomorphism with the stalk of `α` to get
`ρ`. Change of rings commutes with stalks: apply `stalkChangeOfRingsIso` termwise,
then the preceding inverse-image module comparison. These linear isomorphisms give
extension of scalars of the original stalk terms. Naturality on module morphisms
identifies the differentials with extension of the stalk differentials. Finally
compose with the stalks of `e`; the assumed differential square gives a chain
isomorphism to the stalk of `P`. This argument imposes no boundedness or flatness
assumption; if `X` is empty there is no `x`, and zero stalk rings cause no exception. -/
theorem exists_tensorPullback_stalk_complex_iso
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf)
    (K : CochainComplex (RingedSpace.Modules Y) ℤ)
    (P : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : ∀ i : ℤ, P.X i ≅
      SheafOfModules.changeOfRings.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i)))
    (he : ∀ i j : ℤ, P.d i j ≫ (e j).hom =
      (e i).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i))
        (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf (K.X i) (K.d i j)))
    (x : X) :
    ∃ ρ : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x,
      Nonempty
        ((((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor Y (f x)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
        (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj P)) :=
  by
    let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    let ψ : TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
        (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x →+* X.presheaf.stalk x :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
    let ρ := ψ.comp k.hom
    obtain ⟨c, β, hβ, hc⟩ := exists_ringed_inverseImage_stalk_scalar_transport X Y f α x
    obtain ⟨τ, _, hτ⟩ := SheafOfModules.stalkChangeOfRingsIso X.carrier
      (TopCat.Sheaf.inverseImageRing f Y.sheaf) X.sheaf α x
    let δ (M : RingedSpace.Modules Y) :
        (ModuleCat.extendScalars ρ).obj
            ((RingedSpace.moduleStalkFunctor Y (f x)).obj M) ≅
          (RingedSpace.moduleStalkFunctor X x).obj
            (SheafOfModules.changeOfRings.{u, u, u} α
              (TopCat.Sheaf.inverseImageModule f Y.sheaf M)) :=
      β M ≪≫ τ (TopCat.Sheaf.inverseImageModule f Y.sheaf M)
    have hδ (M N : RingedSpace.Modules Y) (a : M ⟶ N) :
        (ModuleCat.extendScalars ρ).map
            ((RingedSpace.moduleStalkFunctor Y (f x)).map a) ≫ (δ N).hom =
          (δ M).hom ≫ (RingedSpace.moduleStalkFunctor X x).map
            (SheafOfModules.changeOfRingsHom.{u, u, u} α
              (TopCat.Sheaf.inverseImageModule f Y.sheaf M)
              (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change (τ _).hom ((β N).hom
        ((ModuleCat.extendScalars ρ).map
          ((RingedSpace.moduleStalkFunctor Y (f x)).map a)
          (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
            (1 : X.presheaf.stalk x) m))) = _
      rw [ModuleCat.ExtendScalars.map_tmul, hβ, hc]
      change (τ _).hom _ = (RingedSpace.moduleStalkFunctor X x).map _
        ((τ _).hom ((β M).hom (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
            (1 : X.presheaf.stalk x) m)))
      rw [hβ]
      exact (hτ _ _ (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a) 1 (c M m)).symm
    refine ⟨ρ, ⟨HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ δ (K.X i) ≪≫ ((RingedSpace.moduleStalkFunctor X x).mapIso (e i)).symm)
      ?_⟩⟩
    intro i j _
    change ((δ (K.X i)).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (e i).inv) ≫
        (RingedSpace.moduleStalkFunctor X x).map (P.d i j) =
      (ModuleCat.extendScalars ρ).map
        ((RingedSpace.moduleStalkFunctor Y (f x)).map (K.d i j)) ≫
        ((δ (K.X j)).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (e j).inv)
    apply (cancel_mono ((RingedSpace.moduleStalkFunctor X x).map (e j).hom)).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [he i j]
    simp only [← Category.assoc]
    simp only [Iso.inv_hom_id, Category.id_comp]
    rw [(RingedSpace.moduleStalkFunctor X x).map_id, Category.comp_id]
    exact (hδ (K.X i) (K.X j) (K.d i j)).symm

end
end CochainComplex
