/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Bounded constructible field-coefficient complexes form a thick triangulated subcategory

The property is the recorded finite-constant-model notion, not the different upstream
stratified-local-finite-presentation property. The two coefficient choices carry their
canonical ring-object structures. The algebraic-closure coefficient has sections valued
in a finite subextension, as required by the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem kernel_closed_retract
    {A : Type*} [Category A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderKernels] {M N : A} (e : Retract M N) (hN : P N) : P M := by
  let f : N ⟶ N := 𝟙 N - e.r ≫ e.i
  have w : e.i ≫ f = 0 := by simp [f, Preadditive.comp_sub, ← Category.assoc]
  apply P.prop_of_isLimit_kernelFork (k := Limits.KernelFork.ofι e.i w) _ hN hN
  refine Limits.KernelFork.IsLimit.ofι e.i w (fun g _ ↦ g ≫ e.r) ?_ ?_
  · intro W g hg
    have h : g - g ≫ e.r ≫ e.i = 0 := by
      simpa [f, Preadditive.comp_sub] using hg
    simpa only [Category.assoc] using (sub_eq_zero.mp h).symm
  · intro W g hg m hm
    rw [← hm]
    simp

private theorem bounded_homology_thick
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
      ).IsClosedUnderIsomorphisms ∧
    (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
      ).IsTriangulated ∧
    (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
      ).IsStableUnderRetracts := by
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (cohomology_in_weak_serre_subcategory P).1
  refine ⟨inferInstance, inferInstance, ⟨?_⟩⟩
  intro M N e hN
  obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded N).2 hN.1
  refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).1
    ⟨a, b, (DerivedCategory.homologyConcentratedIn a b).prop_of_retract e hab⟩, ?_⟩
  intro n
  exact kernel_closed_retract P (e.map (DerivedCategory.homologyFunctor A n)) (hN.2 n)

/-- On a Noetherian scheme, bounded constructible complexes over each finite extension
`E` of `ℚ_ℓ` and over the finite-subextension-valued condensed `ℚ̄_ℓ` form replete thick
triangulated full subcategories of the ambient derived categories of `Λ_X`-modules.
`IsTriangulated` includes zero, all integer shifts and extension closure; together with
isomorphism closure, rotation gives the two-out-of-three property for all distinguished
triangles. `IsStableUnderRetracts` is closure under direct summands, i.e. thickness. -/
theorem constantModelBoundedConstructible_field_triangulated
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsClosedUnderIsomorphisms ∧
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsTriangulated ∧
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsStableUnderRetracts) ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsTriangulated ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsStableUnderRetracts := by
  classical
  have : IsNoetherian X := {}
  have field_case (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
      [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ)]
      (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
        FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
        Λ = Profinite.padicAlgClCondensedRing ℓ) :
      let L := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ
      (constantModelBoundedConstructible L X).IsClosedUnderIsomorphisms ∧
      (constantModelBoundedConstructible L X).IsTriangulated ∧
      (constantModelBoundedConstructible L X).IsStableUnderRetracts := by
    let L := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ
    let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj L X)) := IsConstantModelConstructible L X
    obtain ⟨hk, hc, he, ha, _⟩ := (coefficientHeart_closure ℓ Λ hΛ).2 X
    have : P.IsClosedUnderKernels := hk
    have : P.IsClosedUnderCokernels := hc
    have : P.IsClosedUnderExtensions := he
    have : Abelian P.FullSubcategory := ha.some
    have : P.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined L X).1
    obtain ⟨Z, hZ⟩ := Limits.HasZeroObject.zero (C := P.FullSubcategory)
    have : P.ContainsZero := ⟨⟨Z.obj, P.ι.map_isZero hZ, Z.property⟩⟩
    exact bounded_homology_thick P
  constructor
  · intro E
    exact field_case (Profinite.continuousMapRingSheaf.{u} E)
      (Or.inl ⟨E.1, E.2, rfl⟩)
  · exact field_case (Profinite.padicAlgClCondensedRing.{u} ℓ) (Or.inr rfl)

end AlgebraicGeometry.ProEtale
