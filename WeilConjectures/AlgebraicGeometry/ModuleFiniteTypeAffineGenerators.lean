/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModuleGeneratingSectionsCompactSelection
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite affine sections generating on a compact open

## References

* [Stacks, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_affine_generatingSections
    (X : Scheme.{u}) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent] :
    Nonempty (H.over V.1).GeneratingSections := by
  let H' : X.Modules := H
  let M := H'.restrict V.2.fromSpec
  have : M.IsQuasicoherent := inferInstance
  have : IsIso M.fromTildeΓ := inferInstance
  let P := (presentationTilde
    ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) .univ (by simp) _
    (Submodule.span_eq _)).ofIsIso M.fromTildeΓ
  let Q := presentationOverOfRestrict V.2.fromSpec.opensRange
    (presentationRestrictOpensRange V.2.fromSpec P)
  exact V.2.opensRange_fromSpec ▸ ⟨Q.generators⟩

/-- Finitely many sections on an affine open generate a quasi-coherent module on a
compact open where it is of finite type (Stacks, Tag 01PF). -/
theorem exists_finiteType_affine_generators
    (X : Scheme.{u}) (V : X.affineOpens) (K : X.Opens)
    (hK : IsCompact (K : Set X)) (hKV : K ≤ V.1)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over K).IsFiniteType] :
    ∃ (n : ℕ) (φ : SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V.1) (ULift.{u} (Fin n)) ⟶ H.over V.1),
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hKV)).map φ) := by
  classical
  obtain ⟨σ⟩ := exists_affine_generatingSections X V H
  obtain ⟨S, hS⟩ := exists_finset_generatingSections_on_compact X V.1 K hK hKV H σ
  let e : ULift.{u} (Fin (Fintype.card S)) ≃ S :=
    Equiv.ulift.trans (Fintype.equivFin S).symm
  let R := moduleRings X.toRingedSpace
  let T := SheafOfModules.overMap R (homOfLE hKV)
  let f := SheafOfModules.freeMap (R := R.over V.1) ((↑) : S → σ.I) ≫ σ.π
  let g := ((SheafOfModules.freeFunctor (R := R.over V.1)).mapIso e.toIso).hom
  have : Epi (T.map f) := hS
  refine ⟨Fintype.card S, g ≫ f, ?_⟩
  rw [T.map_comp]
  exact epi_comp' (IsIso.epi_of_iso (T.map g)) hS

end AlgebraicGeometry.Scheme.Modules
