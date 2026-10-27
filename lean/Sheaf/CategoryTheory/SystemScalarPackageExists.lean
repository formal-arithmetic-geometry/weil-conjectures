module

public import Sheaf.CategoryTheory.SystemScalarModel
import Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Sheaf.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-system-scalar-package-exists).
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

/-- Generic scalar comparison extracted from IntegralComparisonSequenceSystems.
Source: Stacks 03D7, 03EK and 06YY
(blueprint: lem-sf-system-scalar-package-exists).
Proof: Choose the normalized derived counit comparison using the cochain universal property. The
ordinary tensor/restriction adjunction gives its unique unit-normalized adjunction, and the
derived Hom comparison gives the derived adjunction with the required transpose. The unit sends
x to one tensor x by the ordinary unit formula; this constructs the scalar package without
changing its cochain model. -/
theorem scalarPackageExists
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ A : SheafOfModules.SystemScalarModel φ, A.model = D := by
  obtain ⟨ε, hε, hεP⟩ :=
    exists_homotopy_leftDerived_comparison D.E D.T D.ε D.universal
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, ha⟩ := ho D.E D.obj_eq D.map_eq
  obtain ⟨d, hd⟩ := SheafOfModules.sheafRingDerivedHomComparison φ
    D.E D.obj_eq D.map_eq a D.T ε hε
  refine ⟨{ model := D
            ordinaryAdj := a
            unit_normalized := ?_
            adjunction := d
            transpose := adjunction_cochain_transpose D.E _ a D.T D.ε ε hεP d hd }, rfl⟩
  intro P U x
  have hu := ha P (D.E.obj P) (eqToHom (D.obj_eq P).symm) U x
  dsimp only [SheafOfModules.systemModelTmul]
  rw [one_smul]
  have ht : ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
      (P.val.obj U)) x =
        (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x := rfl
  rw [ht]
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
  exact hu

end SequenceScalarConstruction
