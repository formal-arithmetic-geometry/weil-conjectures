/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The geometric affine chart square

## References

* Stacks Project, Tag 08EU.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The geometric square of an affine chart, independently of derived categories
(Stacks, Tag 08EU). -/
theorem exists_projectionMate_affineChart_data
    (X Y : Scheme.{u}) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ (A : Type u) (hA : CommRing A),
      letI := hA
      ∃ (Z : Scheme.{u}) (hZ : CompactSpace Z) (hZqs : QuasiSeparatedSpace Z),
        letI := hZ
        letI := hZqs
        ∃ (g : Z ⟶ Spec (.of A)) (hg : QuasiCompact g) (hgqs : QuasiSeparated g),
          letI := hg
          letI := hgqs
          ∃ (eV : Spec (.of A) ≅ V.toScheme)
            (eZ : Z ≅ (f ⁻¹ᵁ V).toScheme),
            g ≫ eV.hom = eZ.hom ≫ (f ∣_ V)  := by
  let A := Y.presheaf.obj (Opposite.op V)
  let Z := (f ⁻¹ᵁ V).toScheme
  have hZ : CompactSpace Z :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hV.isCompact)
  have : IsAffine V.toScheme := hV
  have : QuasiSeparatedSpace V.toScheme := inferInstance
  have hZqs : QuasiSeparatedSpace Z :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  let g : Z ⟶ Spec A := (f ∣_ V) ≫ hV.isoSpec.hom
  have hg : QuasiCompact g := inferInstance
  have hgqs : QuasiSeparated g := inferInstance
  refine ⟨A, inferInstance, Z, hZ, hZqs, g, hg, hgqs,
    hV.isoSpec.symm, Iso.refl _, ?_⟩
  simp [g]

end AlgebraicGeometry
