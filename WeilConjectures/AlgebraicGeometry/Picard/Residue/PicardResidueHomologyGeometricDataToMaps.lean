/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenGeometricFibreData
import WeilConjectures.AlgebraicGeometry.AbelianVariety.PicardResidueHomologyComposeData

/-! # Composition of packaged residue and geometric comparisons -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Extract the final maps from packaged affine and geometric comparisons. -/
theorem picard_residue_homology_geometric_data_to_maps
    {I : Type u} {Ksrc A C : Type v} {Tgt B D P : I → Type v}
    (M : ∀ i, P i → Ksrc → Tgt i) (N : ∀ i, C → D i)
    [AddCommGroup Ksrc] [AddCommGroup A] [AddCommGroup C]
    [∀ i, AddCommGroup (Tgt i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (D i)]
    (d : PicardResidueHomologyGeometricData (I := I) (Ksrc := Ksrc)
      (A := A) (C := C) (Tgt := Tgt) (B := B) (D := D) (P := P) M N) :
    ∃ (eK : Ksrc ≃+ C) (eC : ∀ i, Tgt i ≃+ D i) (φ : ∀ i, P i),
      ∀ i z, eC i (M i (φ i) z) = N i (eK z) := by
  refine ⟨d.eK.trans d.e, (fun i ↦ (d.eC i).trans (d.ei i)), d.φ, ?_⟩
  exact picard_residue_homology_compose_data d.eK d.eC
    (fun i z ↦ M i (d.φ i) z) d.e d.ei d.F
    (fun i z ↦ N i z) d.hdata d.hgeom

end AlgebraicGeometry.Scheme
