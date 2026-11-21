/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsAcyclicKFlat
import WeilConjectures.Algebra.Homology.KFlatClosure
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Change of rings preserves quasi-isomorphisms between K-flat complexes

## References

* Stacks Project, Cohomology on Sites, Tags 06YT, 06YS and 06YY
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Termwise extension of scalars preserves quasi-isomorphisms between K-flat complexes. -/
theorem changeOfRings_kFlat_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∀ {P Q : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ} (α : P ⟶ Q),
      P.IsKFlatTensor → Q.IsKFlatTensor → QuasiIso α →
        QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  intro P Q α hP hQ hα
  have hcone : (CochainComplex.mappingCone α).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have hkcone : (CochainComplex.mappingCone α).IsKFlatTensor :=
    CochainComplex.isKFlat_mappingCone α hP hQ
  have hEcone := changeOfRings_acyclic_of_isKFlat φ E h hm
    (CochainComplex.mappingCone α) hkcone hcone
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hEcone i)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso α E)).symm

end SheafOfModules
