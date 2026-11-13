/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Natural comparison with ordinary cohomology

## References

* [Stacks, Tag 03FD]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Module right-derived sections agree naturally with the ordinary Ext model H
(Stacks, Tag 03FD). -/
theorem exists_moduleCohomology_source_comparison (X : Scheme.{u}) (q : ℕ) :
    ∃ e : ∀ F : X.Modules,
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q,
      ∀ (F G : X.Modules) (φ : F ⟶ G)
          (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
        e G (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
          H.map φ q (e F x) := by
  classical
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  obtain ⟨a, ha⟩ := zariskiModuleAbelianCohomologyAgree X
  let e0 : yoneda.obj (⊤ : TopologicalSpace.Opens X.carrier) ⋙ AddCommGrpCat.free ≅
      (Functor.const (TopologicalSpace.Opens X.carrier)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : TopologicalSpace.Opens X.carrier)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro z
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X.carrier)
    AddCommGrpCat).mapIso e0
  let t (F : X.Modules) :
      @CategoryTheory.Sheaf.H' _ _ _ _
        (hasExt_of_enoughInjectives _) ((SheafOfModules.toSheaf
          (moduleRings X.toRingedSpace)).obj F) q ⊤ ≃+ H F q :=
    (Abelian.Ext.precompAddEquiv eS ((SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)).obj F) q).symm
  refine ⟨fun F ↦ (((a q).app F).addCommGroupIsoToAddEquiv).trans (t F), ?_⟩
  intro F G φ x
  have hα := congrArg (fun f ↦ f.hom x) ((a q).hom.naturality φ)
  change t G (((a q).hom.app G)
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x)) = _
  change ((a q).hom.app G)
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
      (((Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X.carrier) q).map
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)).app (op ⊤))
        (((a q).hom.app F) x) at hα
  erw [hα]
  change (Abelian.Ext.mk₀ eS.inv).comp
      (((((a q).hom.app F) x)).comp
        (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ))
        (add_zero q)) (zero_add q) =
    ((Abelian.Ext.mk₀ eS.inv).comp (((a q).hom.app F) x) (zero_add q)).comp
      (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ))
      (add_zero q)
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

end AlgebraicGeometry.Scheme.Modules
