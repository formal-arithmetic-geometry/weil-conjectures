/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# K-flat base change over commutative rings

## References

* Stacks Project, More on Algebra, Tag 06Y1
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CochainComplex

/-- Restriction of scalars reflects acyclicity of cochain complexes. -/
private theorem acyclic_of_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (L : CochainComplex (ModuleCat.{u} B) ℤ)
    (hL : (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (ModuleCat.restrictScalars ρ)).mp
  exact hL i

private theorem acyclic_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :
    (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
  intro i
  exact (hL i).map (ModuleCat.restrictScalars ρ)

/-- Extension of scalars preserves K-flatness without requiring the ring map to be flat. -/
theorem acyclic_mapBifunctor_extendScalars_of_kFlat
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, F.Acyclic →
      (mapBifunctor F K (curriedTensor _)).Acyclic)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :
    (mapBifunctor L
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)
      (curriedTensor _)).Acyclic := by
  apply acyclic_of_restrictScalars ρ
  obtain ⟨e⟩ := nonempty_tensorRestrictExtendScalarsIso ρ L K
  have h := hK _ (acyclic_restrictScalars ρ L hL)
  intro i
  exact (h i).of_iso e.symm

end CochainComplex
