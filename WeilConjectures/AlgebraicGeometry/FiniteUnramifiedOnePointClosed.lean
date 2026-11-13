/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.FiniteClosedImmersionNearFibre
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# A finite unramified morphism with one purely inseparable fibre point is locally a closed immersion

## References

* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isField_stalk_of_unramified_over_field
    {K : Type u} [Field K] {T : Scheme.{u}} (g : T ⟶ Spec (.of K))
    [FormallyUnramified g] [LocallyOfFiniteType g] (t : T) :
    IsField (T.presheaf.stalk t) := by
  have hK : IsField ((Spec (.of K)).presheaf.stalk (g t)) := by
    have he : g t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [he]
    exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField K)
  rw [IsLocalRing.isField_iff_maximalIdeal_eq] at hK ⊢
  rw [← FormallyUnramified.map_maximalIdeal_stalkMap g t, hK, Ideal.map_bot]

private theorem isIso_asFiberHom_of_unique_unramified
    {X S : Scheme.{u}} (π : X ⟶ S) (x : X)
    (hunique : ∀ y : X, π y = π x → y = x)
    [FormallyUnramified π] [LocallyOfFiniteType π] : IsIso (π.asFiberHom x) := by
  have : FormallyUnramified (π.fiberToSpecResidueField (π x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (π.fiberToSpecResidueField (π x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have heq (p : π.fiber (π x)) : p = π.asFiber x := by
    apply (π.fiberι (π x)).isEmbedding.injective
    rw [π.fiberι_asFiber]
    apply hunique
    have hp : π.fiberι (π x) p ∈ π ⁻¹' {π x} := by
      rw [← π.range_fiberι]
      exact ⟨p, rfl⟩
    exact hp
  have hsurj : Function.Surjective (π.asFiberHom x) := fun p ↦
    ⟨IsLocalRing.closedPoint _, (π.asFiberHom_apply x _).trans (heq p).symm⟩
  have : ∀ z, IsIso ((π.asFiberHom x).stalkMap z) := fun z ↦ by
    let := (isField_stalk_of_unramified_over_field
      (π.fiberToSpecResidueField (π x)) (π.asFiberHom x z)).toField
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨((π.asFiberHom x).stalkMap z).hom.injective,
      (π.asFiberHom x).stalkMap_surjective z⟩
  have : IsOpenImmersion (π.asFiberHom x) :=
    .of_isIso_stalkMap _ ⟨(π.asFiberHom x).isEmbedding, by
      rw [hsurj.range_eq]
      exact isOpen_univ⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨this, ⟨hsurj⟩⟩

/-- Let `π : X ⟶ S` be finite and unramified. If `x` is the unique point of the fibre over
`s` and the residue-field extension at `x` over `s` is purely inseparable, then `π` is a
closed immersion after restriction to some open neighbourhood of `s`.
(Stacks, Tag 04DG.) -/
theorem finite_unramified_one_point_closed
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S) (x : X)
    (hx : π x = s)
    (hunique : ∀ y : X, π y = s → y = x)
    (hfinite : IsFinite π)
    (hunramified : LocallyOfFiniteType π ∧ IsOpenImmersion (pullback.diagonal π))
    (hpure : letI : Algebra (S.residueField (π x)) (X.residueField x) :=
      (π.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (S.residueField (π x)) (X.residueField x)) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (π ∣_ U) := by
  subst s
  have : IsFinite π := hfinite
  have : LocallyOfFiniteType π := hunramified.1
  have : IsOpenImmersion (pullback.diagonal π) := hunramified.2
  let : Algebra (S.residueField (π x)) (X.residueField x) :=
    (π.residueFieldMap x).hom.toAlgebra
  have : IsPurelyInseparable (S.residueField (π x)) (X.residueField x) := hpure
  have hsurj : Function.Surjective (π.residueFieldMap x) :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _
  have : IsClosedImmersion (Spec.map (π.residueFieldMap x)) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have : IsIso (π.asFiberHom x) := isIso_asFiberHom_of_unique_unramified π x hunique
  have hcomp : IsClosedImmersion
      (π.asFiberHom x ≫ π.fiberToSpecResidueField (π x)) := by
    rw [π.asFiberHom_fiberToSpecResidueField]
    infer_instance
  have hfiber : IsClosedImmersion (π.fiberToSpecResidueField (π x)) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _ _).mp hcomp
  exact exists_isClosedImmersion_restrict_of_fiber π (π x) hfiber

end AlgebraicGeometry
