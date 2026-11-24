/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detecting acyclicity of change of rings by total tensor

## References

* Stacks Project, Tag 06YY (and the degree-zero total tensor comparison)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private theorem acyclic_of_restriction
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    (L : CochainComplex (SheafOfModules.{u} R') ℤ)
    (hL : (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (toSheaf R')).mp
  exact (hL i).map (toSheaf R)

/-- Universal tensor acyclicity implies acyclicity after extension of scalars. -/
theorem changeOfRings_acyclic_of_tensor_acyclic
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive]
    (K : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ)
    (hT : ∀ F : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ,
      letI := monoidalCategory O
      (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  let := monoidalCategory O
  let U := restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let S := U.obj (unit (𝓡 O'))
  obtain ⟨e, he⟩ := exists_changeOfRings_tensor_comparison φ
  let q (i : ℤ) : U.obj (E.obj (K.X i)) ≅ S ⊗ K.X i :=
    U.mapIso (eqToIso (h (K.X i))) ≪≫ e (K.X i)
  let L := ((E.mapHomologicalComplex (.up ℤ)).obj K)
  let Q := (((curriedTensor _).obj S).mapHomologicalComplex (.up ℤ)).obj K
  have hq : ((U.mapHomologicalComplex (.up ℤ)).obj L) ≅ Q :=
    HomologicalComplex.Hom.isoOfComponents q (by
      intro i j hij
      change (q i).hom ≫ S ◁ K.d i j = U.map (E.map (K.d i j)) ≫ (q j).hom
      dsimp [q]
      rw [hm, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [← he]
      simp [U])
  let t := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) S K
  have ht := hT ((HomologicalComplex.single _ (.up ℤ) 0).obj S)
  have hL : ((U.mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
    intro i
    exact ((ht i).of_iso t).of_iso hq.symm
  exact acyclic_of_restriction
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) L hL

end SheafOfModules
