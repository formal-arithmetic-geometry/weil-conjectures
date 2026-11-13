/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LerayEdgeCocycleData
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.LeraySectionsResolutionComparison

/-! # Comparison of the cocycle Leray edge with the Grothendieck edge

## References

* Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option maxHeartbeats 600000 in
-- Comparing resolution maps unfolds composed module and forgetful functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Comparison of the edge on module cohomology with the abstract Grothendieck edge.
There is no vanishing assumption: this is only the resolution comparison and
identification of the edge, not the degeneration assertion. -/
theorem leray_edge_grothendieck_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ε : LerayEdge X Y f) (hε : LerayEdgeCocycle f ε) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
    letI : PreservesFiniteLimits G := inferInstanceAs
      (PreservesFiniteLimits
        (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    ∀ hFG : D.IsAcyclicComposablePair G,
      ∃ e : ∀ q : ℕ,
        (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
          ((D ⋙ G).rightDerived q ⋙ forget₂ _ AddCommGrpCat),
      ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        (ε q).app F = (e q).hom.app F ≫
          (forget₂ _ AddCommGrpCat).map ((D.grothendieckLeftEdgeMap G hFG q).app F) := by
  classical
  dsimp only
  intro hFG
  let grothX := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  let grothY := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let derivedX := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let derivedY := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let derivedM := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits D := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
    infer_instance
  let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let : PreservesFiniteLimits G := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  obtain ⟨e, he⟩ := leray_sections_resolution_comparison f
  refine ⟨e, ?_⟩
  intro q F
  let I := injectiveResolution F
  let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T := ((D ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  obtain ⟨c, hc, hcπ⟩ := (grothendieck_left_edge_cocycle D G hFG F I).1 q
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv).mp
      inferInstance x
  obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective
    ((RingedSpace.globalSectionsComplex I).homologyπ q)).mp inferInstance a
  subst a
  subst x
  obtain ⟨z, hz, hez⟩ := he q F I s
  obtain ⟨z', hz', hεz⟩ := hε q F I K rfl s
  have hz'eq : z' = z := by
    apply (ModuleCat.mono_iff_injective (G.map (K.iCycles q))).mp inferInstance
    simpa only [eqToHom_refl, HomologicalComplex.id_f, Category.comp_id] using
      hz'.symm.trans hz
  subst z'
  have hεz' : (ε q).app F
      ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
      G.map (I.isoRightDerivedObj D q).inv (G.map (K.homologyπ q) z) := by
    dsimp only [D, G]
    simpa only [eqToHom_refl, HomologicalComplex.homologyMap_id, Category.id_comp,
      Functor.map_comp, ConcreteCategory.comp_apply] using! hεz
  have hedge : ((D.grothendieckLeftEdgeMap G hFG q).app F)
      ((I.isoRightDerivedObj (D ⋙ G) q).inv (T.homologyπ q (c z))) =
      G.map (I.isoRightDerivedObj D q).inv (G.map (K.homologyπ q) z) := by
    have heq := congrArg (fun a ↦ a ≫ G.map (I.isoRightDerivedObj D q).inv) hcπ
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id] at heq
    simpa only [G.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using!
      CategoryTheory.congr_fun heq z
  change (ε q).app F _ = ((D.grothendieckLeftEdgeMap G hFG q).app F)
    ((e q).hom.app F _)
  rw [hez c hc]
  exact hεz'.trans hedge.symm

end AlgebraicGeometry
