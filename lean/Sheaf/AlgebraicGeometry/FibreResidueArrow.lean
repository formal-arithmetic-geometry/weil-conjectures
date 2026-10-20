/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The residue-field arrow of a point in its scheme fibre

Source: Stacks Project, More on Morphisms, Tag 0G4F, passage to the generic fibre.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem residueFieldMap_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [SurjectiveOnStalks f] (x : X) : Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := X.residue_surjective x b
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x a
  exact ⟨S.residue (f x) c, rfl⟩

/-- The residue field of a point is unchanged on viewing it in its scheme fibre, compatibly
with the residue-field map to the base.

Source: Stacks Project, More on Morphisms, Tag 0G4F, generic residue-field identification.
(blueprint: lem-zl-fibre-residue-arrow).

Proof: The fibre inclusion is a preimmersion, hence surjective on stalks. Its map on residue
fields is surjective and, as a field homomorphism, injective. It is therefore an isomorphism.
Identify the image of asFiber x with x. Naturality of the canonical residue-field point and
the pullback square identify the composite to the base residue field with Spec of the
original residueFieldMap. -/
theorem nonempty_fibreResidueArrow_iso {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Nonempty (Arrow.mk
      ((f.fiber (f x)).fromSpecResidueField (f.asFiber x) ≫
        f.fiberToSpecResidueField (f x)) ≅
      Arrow.mk (Spec.map (f.residueFieldMap x))) := by
  let z := f.asFiber x
  let i := f.fiberι (f x)
  have : IsIso (i.residueFieldMap z) :=
    (ConcreteCategory.isIso_iff_bijective (i.residueFieldMap z)).mpr
      (residueFieldMap_bijective i z)
  let e := (X.residueFieldCongr (f.fiberι_asFiber x)).symm ≪≫
    asIso (i.residueFieldMap z)
  refine ⟨Arrow.isoMk (Scheme.Spec.mapIso e.op) (Iso.refl _) ?_⟩
  change Spec.map e.hom ≫ Spec.map (f.residueFieldMap x) =
    (f.fiber (f x)).fromSpecResidueField z ≫ f.fiberToSpecResidueField (f x) ≫ 𝟙 _
  rw [Category.comp_id]
  apply (cancel_mono (S.fromSpecResidueField (f x))).mp
  rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have he : Spec.map e.hom ≫ X.fromSpecResidueField x =
      (f.fiber (f x)).fromSpecResidueField z ≫ i := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_inv,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField i z
  rw [← Category.assoc, he, Category.assoc, Category.assoc]
  dsimp only [i]
  rw [Scheme.Hom.fiber_fac]

end AlgebraicGeometry
