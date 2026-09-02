/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue fields along a morphism surjective on stalks

## Main results

- `AlgebraicGeometry.Scheme.Hom.residueFieldMap_surjective` and
  `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap`: the residue field map of a morphism
  surjective on stalks is surjective, hence an isomorphism, a surjective map of fields being
  bijective. This generalises the instance for open immersions in
  `Mathlib.AlgebraicGeometry.ResidueField`.
- `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_mem_range` and
  `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_surjective`: a field-valued point
  `Spec K ⟶ Y` factors through a morphism `f : X ⟶ Y` surjective on stalks as soon as its
  image lies in the image of `f`; in particular always if `f` is surjective.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]

/-- The residue field map of a morphism which is surjective on stalks is surjective. -/
lemma Hom.residueFieldMap_surjective (x : X) : Function.Surjective (f.residueFieldMap x) :=
  IsLocalRing.ResidueField.map_surjective _ (f.stalkMap_surjective x)

/-- The residue field map of a morphism which is surjective on stalks is an isomorphism, a
surjective map of fields being bijective. -/
instance Hom.isIso_residueFieldMap (x : X) : IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap x).hom.injective, f.residueFieldMap_surjective x⟩

/-- **Field-valued points lift along a morphism surjective on stalks**: if the image of
`s : Spec K ⟶ Y` lies in the image of `f`, then `s` factors through `f`.

```
         Spec K
     ∃s' ↙      ↘ s
        X ───f──→ Y
```
-/
lemma Hom.exists_comp_eq_of_mem_range {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y)
    (hs : s (IsLocalRing.closedPoint _) ∈ Set.range f) :
    ∃ s' : Spec (.of K) ⟶ X, s' ≫ f = s := by
  obtain ⟨⟨y, φ⟩, rfl⟩ := (SpecToEquivOfField K Y).symm.surjective s
  obtain ⟨x, hx⟩ := hs
  simp only [SpecToEquivOfField_symm_apply, Hom.comp_apply, fromSpecResidueField_apply] at hx
  subst hx
  refine ⟨Spec.map (inv (f.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_⟩
  simp only [SpecToEquivOfField_symm_apply]
  rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id_assoc]

/-- Field-valued points lift along a surjective morphism which is surjective on stalks, for
instance along a surjective closed immersion. -/
lemma Hom.exists_comp_eq_of_surjective [Surjective f] {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Y) : ∃ s' : Spec (.of K) ⟶ X, s' ≫ f = s :=
  f.exists_comp_eq_of_mem_range s (f.surjective _)

end AlgebraicGeometry.Scheme

end
