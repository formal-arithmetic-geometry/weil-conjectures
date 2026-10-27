/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.BundledTensorComparison
import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! # Uniqueness from ordinary tensor comparison

Source: Stacks 06YN and 07A4 (blueprint: lem-sf-tensor-comparison-model-uniqueness).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections
namespace WeilConjectures.TensorModelUniqueness
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (F : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (B : WeilConjectures.SemilinearSections.Closed.{c, v, r} K S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B)
  (mu nu : A.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor)
  (M : TensorComparisonModel.{c, v, r} J K R S F A B TA TB mu)
  (N : TensorComparisonModel.{c, v, r} J K R S F A B TA TB nu)
private theorem chain_eq (ho : M.ordinary = N.ordinary)
    (P Q : CochainComplex
      (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    M.chain P Q = N.chain P Q := by
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change tensorSummand.{c, v, r} K S _ _ p q k hpq ≫ _ =
    tensorSummand.{c, v, r} K S _ _ p q k hpq ≫ _
  rw [M.summand, N.summand, ho]

private theorem derived_eq (ho : M.ordinary = N.ordinary) : mu = nu := by
  suffices he : mu.inv = nu.inv by
    have hi : mu.symm = nu.symm := Iso.ext he
    exact congrArg Iso.symm hi
  obtain ⟨_, _, _, h⟩ := SheafOfModules.cochain_tensor_model_rigidity J R
  apply (h (DerivedCategory
    (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)) inferInstance _ _).1
  apply NatTrans.ext
  funext X
  rcases X with ⟨P, Q⟩
  change mu.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    nu.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  have hm := M.derived P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hn := N.derived P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hc := chain_eq.{c, v, r} J K R S F A B TA TB mu nu M N ho P.obj Q.obj
  rw [hc] at hm
  have he := hm.trans hn.symm
  let a := tensorModelIso.{c, v, r} K S B TB _ _
    (M.kflat P.obj P.property.1 P.property.2)
    (M.kflat Q.obj Q.property.1 Q.property.2)
  let b := B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app P.obj)
    ((Functor.mapDerivedCategoryFactors F).app Q.obj)).symm
  let d := F.mapDerivedCategory.mapIso
    (tensorModelIso.{c, v, r} J R A TA P.obj Q.obj P.property.1 Q.property.1).symm
  let e := (Functor.mapDerivedCategoryFactors F).app
    ((totalTensor.{c, v, r} J R).obj (P.obj, Q.obj))
  have he' : a.hom ≫ b.hom ≫ mu.inv.app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) ≫ d.hom ≫ e.hom =
      a.hom ≫ b.hom ≫ nu.inv.app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) ≫ d.hom ≫ e.hom := he
  have hi := congrArg (fun z ↦ b.inv ≫ a.inv ≫ z ≫ e.inv ≫ d.inv) he'
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hi

/-- The ordinary map determines its total and derived comparison.
Source: Stacks 06YN and 07A4 (blueprint: lem-sf-tensor-comparison-model-uniqueness).
Proof: the summand formula and the universal property of the total direct sum
identify the chain maps. Substitute in the two representative equations and
cancel all four invertible comparison factors. Cochain tensor rigidity extends
the resulting equality of derived natural transformations to every pair of
objects. Finally proof irrelevance identifies the remaining model fields. -/
theorem tensorComparisonModel_unique (ho : M.ordinary = N.ordinary) :
    mu = nu ∧ HEq M N := by
  have hm := derived_eq.{c, v, r} J K R S F A B TA TB mu nu M N ho
  refine ⟨hm, ?_⟩
  subst nu
  have hc : M.chain = N.chain := by
    funext P Q
    exact chain_eq.{c, v, r} J K R S F A B TA TB mu mu M N ho P Q
  cases M
  cases N
  dsimp only at ho hc
  cases ho
  cases hc
  rfl
/-- Bundle extensionality is checked with an abstract exact functor. -/
private theorem bundled_unique
    (M' N' : BundledTensorComparison.{c, v, r} J K R S F A B TA TB)
    (ho : M'.model.ordinary = N'.model.ordinary) : M' = N' := by
  obtain ⟨hm, hmodel⟩ := tensorComparisonModel_unique.{c, v, r}
    J K R S F A B TA TB M'.mu N'.mu M'.model N'.model ho
  cases M'
  cases N'
  dsimp only at hm hmodel
  cases hm
  cases hmodel
  rfl

end WeilConjectures.TensorModelUniqueness
