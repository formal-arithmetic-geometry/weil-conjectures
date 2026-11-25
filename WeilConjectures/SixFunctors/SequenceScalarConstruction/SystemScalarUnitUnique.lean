/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators

/-! # Generic normalized scalar comparison

## References

* [Stacks, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks, Tag 03EK](https://stacks.math.columbia.edu/tag/03EK)
* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe sa sb sw
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SequenceScalarConstruction
variable {C : Type sa} [Category.{sb} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C]

/-- Generic scalar comparison extracted from IntegralComparisonSequenceSystems. -/
theorem scalarUnitUnique
    {R : Sheaf J CommRingCat.{sw}} {φ : R ⟶ R} (hφ : φ = 𝟙 R)
    (A : SheafOfModules.SystemScalarModel φ) :
    ∃! a : A.model.E ≅ 𝟭 _, ∀ P U (s : R.obj.obj U) (x : P.val.obj U),
      (a.hom.app P).val.app U (SheafOfModules.systemModelTmul A.model P U s x) =
        s • x := by
  let a := SheafOfModules.systemScalarModelUnit hφ A
  have ha := SheafOfModules.systemScalarModelUnit_tmul hφ A
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply SheafOfModules.systemScalarModel_hom_ext A P P
  intro U x
  exact (hb P U 1 x).trans (ha P U 1 x).symm

end SequenceScalarConstruction
