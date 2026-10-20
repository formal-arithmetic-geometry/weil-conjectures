/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.FiniteRadicialNeighbourhoodModel

/-!
# A prescribed purely inseparable generic extension on a finite radicial cover

Source: Stacks Project, Tag 0GK7, the generic radicial-extension step.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Realize a finite purely inseparable extension of a component generic residue field
on a finite radicial cover of an affine neighbourhood of a reduced scheme.

Source: Stacks Project, Tag 0GK7, radicial-extension step, using finite-presentation descent.
(blueprint: lem-weil-pbc-purely-inseparable-generic-cover)

Proof: The stalk of the reduced base at a component generic point is a field, so its
residue map is an isomorphism. The finite field extension gives a finite-presentation
finite surjection of spectra. Pure inseparability implies universal injectivity:
two maps into any field agreeing on the base field agree on the extension. Transport
this cover along the stalk-residue isomorphism, extend it to an affine neighbourhood
by finite radicial model descent, and transport the resulting cartesian square back
to the residue field. Its base projection agrees with the canonical residue-field map.
-/
theorem exists_purely_inseparable_generic_cover
    (S : Scheme.{u}) [IsReduced S] (η : S)
    (hη : ∃ C ∈ irreducibleComponents S, IsGenericPoint η C)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K] :
    ∃ (U : S.Opens) (_ : η ∈ U) (_ : IsAffineOpen U)
      (V : Scheme.{u}) (p : V ⟶ U.toScheme)
      (a : Spec (S.residueField η) ⟶ U.toScheme),
      LocallyOfFinitePresentation p ∧ IsFinite p ∧ Surjective p ∧
      UniversallyInjective p ∧ a ≫ U.ι = S.fromSpecResidueField η ∧
      ∃ h : Spec (.of K) ⟶ V,
        IsPullback h (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))) p a := by
  classical
  obtain ⟨C, hC, hηC⟩ := hη
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents S η
    (hηC.def.symm ▸ hC)
  let := hfield.toField
  let er := (RingEquiv.ofBijective (S.residue η).hom
    ⟨(S.residue η).hom.injective, S.residue_surjective η⟩).toCommRingCatIso
  have : IsIso (S.residue η) := inferInstanceAs (IsIso er.hom)
  let r := Spec.map (S.residue η)
  have : IsIso r := by dsimp [r]; infer_instance
  let q := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))
  have hfinite : IsFinite q :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation q :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance))
  have hsurj : Surjective q := ⟨Function.surjective_to_subsingleton _⟩
  have hrad : UniversallyInjective q := by
    apply ((tfae_universallyInjective q).out 1 0).mp
    intro Ω _ g₁ g₂ hg
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply IsPurelyInseparable.injective_comp_algebraMap (S.residueField η) K Ω
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective (by
      simpa only [q, ← Spec.map_comp] using hg))
  have := hfinite
  have := hfp
  have := hsurj
  have := hrad
  let g := q ≫ r
  have : IsFinite g := by dsimp [g]; infer_instance
  have : LocallyOfFinitePresentation g := by dsimp [g]; infer_instance
  have : Surjective g := by dsimp [g]; infer_instance
  have : UniversallyInjective g :=
    (MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective q r).mpr hrad
  obtain ⟨U, hηU, hU, V, p, a, hpfp, hpfin, hps, hpr, ha, h, H⟩ :=
    exists_finite_radicial_neighbourhood_model S η g
  refine ⟨U, hηU, hU, V, p, r ≫ a, hpfp, hpfin, hps, hpr, ?_, h, ?_⟩
  · rw [Category.assoc, ha]
    rfl
  · exact H.of_iso (Iso.refl _) (Iso.refl _) (asIso r).symm (Iso.refl _)
      (by simp) (by simp [g, q]) (by simp) (by simp)

end AlgebraicGeometry
