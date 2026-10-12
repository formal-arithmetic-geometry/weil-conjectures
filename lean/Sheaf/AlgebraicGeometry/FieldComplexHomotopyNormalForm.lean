module
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
private theorem negative_single_nonnegative_homology_zero
    {R : CommRingCat.{u}} (A : (Spec R).Modules) (q : ℕ) :
    IsZero (((CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A).homology
      (q : ℤ)) := by
  exact CochainComplex.isZero_of_isLE _ (-1) q (by omega)

private theorem no_equiv_negative_single
    {R : CommRingCat.{u}} (A B : (Spec R).Modules) (hA : ¬ IsZero A) (i : ℕ) :
    ¬ Nonempty (HomotopyEquiv
      ((CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A)
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj B)) := by
  rintro ⟨e⟩
  have hz := CochainComplex.isZero_of_isGE
    ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj B) i (-1) (by omega)
  have hz' := hz.of_iso (e.toHomologyIso (-1))
  exact hA (hz'.of_iso
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) A).symm)

private theorem counterexample_to_single_field_homology {R : CommRingCat.{u}} (hR : IsField R) :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      (∀ q : ℕ, q ≠ 0 → IsZero (P.homology (q : ℤ))) ∧
      (P.homology (0 : ℤ)).IsFiniteLocallyFreeOfRank 0 ∧
      ¬ Nonempty (HomotopyEquiv P
        ((CochainComplex.singleFunctor (Spec R).Modules (0 : ℤ)).obj
          (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin 0))))) := by
  let := hR.toField
  let A := SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin 1))
  let P := (CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A
  have hA := finrank_moduleSpecΓFunctor_obj_free hR (Iso.refl A)
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj A) := hA.2
  have hAnonzero : ¬ IsZero A := by
    intro hz
    have heq := (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hR A).mp hz
    simp only [Fintype.card_ulift, Fintype.card_fin] at hA
    omega
  have hz : IsZero (P.homology (0 : ℤ)) :=
    negative_single_nonnegative_homology_zero A 0
  have hzΓ := (moduleSpecΓFunctor (R := R)).map_isZero hz
  have : Subsingleton ((moduleSpecΓFunctor (R := R)).obj (P.homology (0 : ℤ))) :=
    ModuleCat.subsingleton_of_isZero hzΓ
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (P.homology (0 : ℤ))) :=
    inferInstance
  refine ⟨P, fun q _ ↦ negative_single_nonnegative_homology_zero A q, ?_, ?_⟩
  · apply (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hR _ 0).mpr
    exact Module.finrank_zero_of_subsingleton
  · exact no_equiv_negative_single A _ hAnonzero 0

/- STATEMENT-DISPUTED: hzero constrains only natural degrees, not negative homology.
The private counterexample above takes the rank-one free sheaf in degree -1, with i = r = 0.
All hypotheses hold, but a homotopy equivalence would kill its nonzero degree -1 homology. -/
/-- Field-complex splitting into the sole finite locally free cohomology.
Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: new-field-complex-homotopy-normal-form). -/
theorem homotopyEquiv_of_single_field_homology
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ)
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r))))) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
