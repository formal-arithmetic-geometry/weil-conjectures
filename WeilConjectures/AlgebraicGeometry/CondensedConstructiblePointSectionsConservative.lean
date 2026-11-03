/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-! # Coefficient sections detect zero constructible point complexes

Source: the nonzero-fibre paragraph of the first Fourier formula proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem point_module_zero_of_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω))))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of Ω))) M)
    (h : IsZero ((CondensedRing.condensedRingCoefficientSections Λ (Spec (.of Ω))).obj M)) :
    IsZero M := by
  classical
  have hfp := CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
    Λ (Field.toIsField Ω) IsField.isSepClosed_toField hM (𝟙 _)
  have hfp' := hfp.of_iso ((CondensedRing.upperStarId Λ _).app M)
  have hs := ModuleCat.subsingleton_of_isZero h
  have hhom (f : Mod.regular (condensedRingObj Λ (Spec (.of Ω))) ⟶ M) : f = 0 :=
    hs.elim f 0
  obtain ⟨n, m, f, ⟨e⟩⟩ := hfp'
  let q := cokernel.π f ≫ e.inv
  have hq : q = 0 := by
    apply biproduct.hom_ext'
    intro j
    exact hhom (biproduct.ι
      (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ (Spec (.of Ω)))) j ≫ q)
  have : Epi q := inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi q).1
  simp [hq]

/-- Exact coefficient sections detect zero bounded constructible complexes at an
algebraically closed point, for any commutative condensed coefficient ring.

Source: latest blueprint, first-formula proof, nonzero geometric fibre paragraph
(blueprint: lem-fd-constructible-point-sections-conservative).

Proof. Constructible modules pulled back to a geometric point are finitely presented;
apply this to the identity point. Such a module is a quotient of a finite sum of
regular modules. Its coefficient sections are maps from the regular module, so zero
sections make this quotient map zero and hence make the module zero. Sections are
exact at the algebraically closed point because the regular module is projective.
Their total right derived functor is therefore the termwise derived functor and
commutes with homology. Apply the module argument to each constructible homology
object, then use the derived homology criterion for zero objects. This makes no
claim about arbitrary condensed modules. -/
theorem condensed_constructible_point_zero_of_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} (MonObj.Γ Λ))]
    (K : DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))))
    (hK : boundedConstructible (condensedRingObj Λ (Spec (.of Ω))) K)
    (h : IsZero ((CondensedRing.condensedRingCoefficientSections Λ
      (Spec (.of Ω))).rightDerivedFunctor.obj K)) : IsZero K := by
  let F := CondensedRing.condensedRingCoefficientSections Λ (Spec (.of Ω))
  have := (CondensedRing.finite_point_sections_exact Λ Ω).1
  have := (CondensedRing.finite_point_sections_exact Λ Ω).2
  have hz : IsZero (F.mapDerivedCategory.obj K) :=
    h.of_iso (F.rightDerivedFunctorIsoMapDerivedCategory.app K).symm
  apply DerivedCategory.isZero_of_forall_isZero_homology
  intro n
  apply point_module_zero_of_sections Λ Ω _ (hK.2 n)
  exact ((DerivedCategory.homologyFunctor _ n).map_isZero hz).of_iso
    ((F.mapDerivedCategoryHomologyFunctorIso n).app K)

end AlgebraicGeometry.ProEtale
