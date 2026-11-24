/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic

/-!
# Extension of scalars of acyclic K-flat complexes

## References

* Stacks Project, Cohomology on Sites, Tags 06YT, 06YS and 06YY
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Extension of scalars sends an acyclic K-flat complex to an acyclic complex. -/
theorem changeOfRings_acyclic_of_isKFlat
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
    (hK : K.IsKFlatTensor) (hA : K.Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic  := by
  apply changeOfRings_acyclic_of_tensor_acyclic φ E h hm K
  intro F
  exact tensor_acyclic_of_isKFlat K hK hA F

end SheafOfModules
