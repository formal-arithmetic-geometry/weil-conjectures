module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Sheaf.RingTheory.GlobalDimension
import Sheaf.RingTheory.ProjectiveResolutionExtCharacterization
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! Finite global dimension gives finite projective dimension for the residue field.

Source: Stacks Project, Algebra, Proposition 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension)
-/

@[expose] public section

universe u v

namespace Ring

/-- The residue field of a ring of finite global dimension has finite projective dimension.
Source: Stacks Project, Algebra, Proposition Tag 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension). -/
theorem residueField_hasFiniteProjectiveDimension (R : Type u) [CommRing R]
    [IsLocalRing R] (h : Ring.HasFiniteGlobalDimension.{u, max u v} R) :
    ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  obtain ⟨n, hn⟩ := h
  let K := ModuleCat.of R (IsLocalRing.ResidueField R)
  let L := ModuleCat.of R (ULift.{v} (IsLocalRing.ResidueField R))
  have hL := (ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing L n).2.mp (hn L)
  let : CategoryTheory.HasProjectiveDimensionLE L n := ⟨fun i hi Y ↦ hL Y i hi⟩
  let : CategoryTheory.HasProjectiveDimensionLE K n :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv.{max u v, u}
      (M := L) (N := K)
      (ULift.moduleEquiv : L ≃ₗ[R] K) n
  refine ⟨n, (ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing K n).2.mpr ?_⟩
  intro Y i hi
  let := CategoryTheory.HasExt.standard (ModuleCat.{u} R)
  exact CategoryTheory.HasProjectiveDimensionLT.subsingleton.{u + 1} K (n + 1) i hi Y

end Ring
