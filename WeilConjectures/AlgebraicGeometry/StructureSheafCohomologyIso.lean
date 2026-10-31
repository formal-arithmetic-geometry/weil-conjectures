/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism

/-! # Structure-sheaf cohomology under an isomorphism over a field

Source: Stacks Project, Cohomology of Sheaves, §20.11, Tag 01DZ;
the geometric-fibre comparison in Pikaart--de Jong (1995), §2.3.3
(blueprint: lem-sfb-structure-sheaf-cohomology-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem finrank_moduleCohomology_eq_finrankH
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (F : Y.Modules) (q : ℕ) :
    Module.finrank k ((RingedSpace.moduleCohomology Y.toRingedSpace q ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj F) =
      (letI : Y.Over (Spec (.of k)) := ⟨g⟩; F.finrankH k q) := by
  let : Y.Over (Spec (.of k)) := ⟨g⟩
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison Y q
  let C := (RingedSpace.moduleCohomology Y.toRingedSpace q ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj F
  let e : C ≃ₗ[k] F.H q :=
    { a F with
      map_smul' := fun c x ↦ by
        let b := Scheme.globalSectionsRingHom k (X := Y) c
        have hn := ha F F (F.smulHom b) x
        have hm := moduleCohomology_scalar_endomorphism F (F.smulHom b) b
          (fun U t ↦ Scheme.Modules.smulHom_app_apply F b U t) q x
        rw [hm] at hn
        exact hn }
  exact e.finrank_eq

/-- An isomorphism over a field preserves the dimensions of structure-sheaf cohomology,
with scalar actions restricted along the structure maps.
Source: Stacks Project, §20.11, Tag 01DZ
(blueprint: lem-sfb-structure-sheaf-cohomology-iso).

Proof: Compare module right-derived sections with the source library's ordinary H
using exists_moduleCohomology_source_comparison. Naturality for multiplication by
a global function, and moduleCohomology_scalar_endomorphism, show that this additive
comparison is linear after restricting scalars along the structure map. Thus its
linear equivalence preserves finrank. Give X and Y their specified structures as
k-schemes. The equation he makes e.hom a map over k. The structure sheaf on Y is
quasi-coherent, and its pullback is the structure sheaf on X. Apply
finrankH_pullback_of_isIso and finrankH_congr to obtain equality of the ordinary
cohomology dimensions, then transport through the two linear comparisons.
No finite-dimensionality or nonemptiness assumption is used; degree zero, zero
cohomology, and empty schemes are included. -/
theorem finrank_structureSheafCohomology_iso
    {k : Type u} [Field k] {X Y : Scheme.{u}} (e : X ≅ Y)
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (he : e.hom ≫ g = f) (q : ℕ) :
    Module.finrank k
      ((ModuleCat.restrictScalars
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
            (SheafOfModules.unit (moduleRings X.toRingedSpace)))) =
      Module.finrank k ((ModuleCat.restrictScalars
          (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom)).obj
            ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj
              (SheafOfModules.unit (moduleRings Y.toRingedSpace)))) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : Y.Over (Spec (.of k)) := ⟨g⟩
  have : e.hom.IsOver (Spec (.of k)) := (Scheme.Hom.isOver_iff _).mpr he
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := Y.ringCatSheaf)
  exact (finrank_moduleCohomology_eq_finrankH f _ q).trans
    (((Scheme.Modules.finrankH_congr k (Scheme.Modules.pullbackObjUnitIso e.hom) q).symm.trans
      (Scheme.Modules.finrankH_pullback_of_isIso e.hom _ q)).trans
        (finrank_moduleCohomology_eq_finrankH g _ q).symm)

end AlgebraicGeometry
