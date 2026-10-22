/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonFunctor
public import Sheaf.Paper.FieldPerfectScalarComparison
public import Sheaf.Paper.RationalComparisonStageSystem

/-! # The rational stage system with its original tower maps

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent
attribute [local semireducible] FieldOf integerRing
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)


/-- The two actual integer-to-field composites agree as bundled ring maps.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-scalar-square). -/
theorem fractionMap_square {E L : Index l Ω} (a : E ≤ L) :
    integerMap l Ω a ≫ fractionMap l Ω L = fractionMap l Ω E ≫ fieldMap l Ω a := by
  ext r
  rfl


/-- Scalar tower comparisons are natural on any specified perfect-valued functor.
Source: Stacks 06Y6 (blueprint: lem-sf-rational-comparison-scalar-square). -/
def scalarCompOn {J : Type c} [Category.{h} J] {R S T : CommRingCat.{u}}
    (F : J ⥤ DerivedCategory.PerfectScalar.D.{u, u} R)
    (hF : ∀ X, DerivedCategory.IsPerfectRingComplex (F.obj X))
    (f : R ⟶ S) (g : S ⟶ T) :
    F ⋙ DerivedCategory.PerfectScalar.B f ⋙ DerivedCategory.PerfectScalar.B g ≅
      F ⋙ DerivedCategory.PerfectScalar.B (f ≫ g) :=
  NatIso.ofComponents
    (fun X ↦ scalarComp f g (F.obj X) (hF X)) (by
      intro X Y a
      have hc : DerivedCategory.PerfectScalar.coherenceData.{u, u}.Normalized := by
        unfold DerivedCategory.PerfectScalar.coherenceData
        exact DerivedCategory.PerfectScalar.perfect_scalar_tensor_coherence_data.exists.choose_spec
      dsimp only [Functor.comp_map]
      unfold scalarComp
      exact hc.2.1 f g (F.obj X) (F.obj Y) (hF X) (hF Y) (F.map a))

/-- The integral comparison viewed as its actual natural isomorphism.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-scalar-square). -/
def integralPhi {E L : Index l Ω} (a : E ≤ L) :
    A.S.T a ⋙ A.F L ≅ A.F E ⋙ integralB l Ω a :=
  NatIso.ofComponents (A.phi a) (fun {X Y} f ↦ hA.hypothesis1 a X Y f)

open CategoryTheory.Functor in
/-- The scalar-square comparison is natural before extending Hom modules.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-scalar-square). -/
def integralRationalPhi {E L : Index l Ω} (a : E ≤ L) :
    A.S.T a ⋙ fractionFunctor A L ≅
      fractionFunctor A E ⋙ DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (integralPhi A hA a) (fractionB l Ω L) ≪≫
    Functor.associator _ _ _ ≪≫
    scalarCompOn (A.F E) (A.perfect E) (integerMap l Ω a) (fractionMap l Ω L) ≪≫
    eqToIso (congrArg (fun f ↦ A.F E ⋙ DerivedCategory.PerfectScalar.B.{u, u} f)
      (fractionMap_square a)) ≪≫
    (scalarCompOn (A.F E) (A.perfect E) (fractionMap l Ω E) (fieldMap l Ω a)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft (fractionFunctor A E)
      (DerivedCategory.PerfectScalar.fieldScalarComparison (fieldMap l Ω a).hom)

/-- The balanced comparison of the two scalar-extension paths on each perfect object.
Source: blueprint order 1826, step 5
(blueprint: lem-sf-rational-comparison-scalar-square). -/
def rationalPhiComponent {E L : Index l Ω} (a : E ≤ L) (X : C E) :
    (fractionB l Ω L).obj ((A.F L).obj ((A.S.T a).obj X)) ≅
      (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).obj
        ((fractionFunctor A E).obj X) :=
  (fractionB l Ω L).mapIso (A.phi a X) ≪≫
    scalarComp (integerMap l Ω a) (fractionMap l Ω L) _ (A.perfect E X) ≪≫
    (eqToIso (congrArg (fun f ↦ (DerivedCategory.PerfectScalar.B.{u, u} f).obj
      ((A.F E).obj X)) (fractionMap_square a))) ≪≫
    (scalarComp (fractionMap l Ω E) (fieldMap l Ω a) _ (A.perfect E X)).symm ≪≫
    (DerivedCategory.PerfectScalar.fieldScalarComparison (fieldMap l Ω a).hom).app _

/-- The exact field extension is semilinear on each actual perfect Hom group.
Source: Stacks 06Y6 (blueprint: lem-sf-rational-comparison-scalar-square). -/
theorem fieldScalar_map_smul {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (P Q : DerivedCategory (ModuleCat.{u} K))
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (hQ : DerivedCategory.IsPerfectRingComplex Q) (r : K) (g : P ⟶ Q) :
    (DerivedCategory.fieldDerivedScalarExtension f).map (r • g) =
      f r • (DerivedCategory.fieldDerivedScalarExtension f).map g := by
  let κ := DerivedCategory.PerfectScalar.fieldScalarComparison f
  apply (cancel_epi (κ.hom.app P)).1
  rw [← κ.hom.naturality, DerivedCategory.PerfectScalar.coherenceData.linear
    (CommRingCat.ofHom f) P Q hP hQ, Linear.smul_comp,
    κ.hom.naturality, Linear.comp_smul]
  rfl

set_option linter.flexible false in
/-- The scalar-square composite has exactly the balanced component formula.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-scalar-square). -/
theorem integralRationalPhi_app {E L : Index l Ω} (a : E ≤ L) (X : C E) :
    (integralRationalPhi A hA a).app X = rationalPhiComponent A a X := by
  apply Iso.ext
  simp [integralRationalPhi, rationalPhiComponent, scalarCompOn, integralPhi,
    Category.assoc]
  dsimp only [fractionFunctor, Functor.comp_obj]
  rw [Category.id_comp]
  rfl

attribute [local instance] rationalStructures

/-- The comparison naturality extends from integral arrows by tensor additivity.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-scalar-square). -/
def rationalPhi {E L : Index l Ω} (a : E ≤ L) :
    rationalTransition A hA a ⋙ rationalFunctor A hA L ≅
      rationalFunctor A hA E ⋙
        DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom :=
  NatIso.ofComponents (fun X ↦ rationalPhiComponent A a X.obj) (by
    intro X Y f
    letI := rationalFunctor_additive A hA E
    letI := rationalFunctor_additive A hA L
    letI := rationalTransition_additive A hA a
    change rationalHom A hA L _ _ (rationalTransitionHom A hA a _ _ f) ≫ _ =
      _ ≫ (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).map
        (rationalHom A hA E _ _ f)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add, Functor.map_add, Preadditive.add_comp,
        Preadditive.comp_add, hf, hg]
    | tmul r f =>
      rw [rationalTransitionHom_tmul, rationalHom_tmul, rationalHom_tmul,
        AlgEquiv.apply_symm_apply, fieldScalar_map_smul _ _ _
          (rationalFunctor_perfect A hA E X) (rationalFunctor_perfect A hA E Y)]
      simp only [Linear.smul_comp, Linear.comp_smul]
      congr 1
      have hn := (integralRationalPhi A hA a).hom.naturality f
      rw [← integralRationalPhi_app A hA a X.obj,
        ← integralRationalPhi_app A hA a Y.obj]
      exact hn)

/-- Perfectness is preserved by the specified exact field extension.
Source: Stacks 06Y6 (blueprint: lem-sf-rational-comparison-scalar-square). -/
theorem rationalFunctor_extendedPerfect {E L : Index l Ω} (a : E ≤ L) (X : Rat C E) :
    DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).obj
        ((rationalFunctor A hA E).obj X)) := by
  have hp := DerivedCategory.PerfectScalar.coherenceData.{u, u}.preserves
    (fieldMap l Ω a) _ (rationalFunctor_perfect A hA E X)
  rcases hp with ⟨P, m, n, hm, hn, ht, ⟨e⟩⟩
  exact ⟨P, m, n, hm, hn, ht,
    ⟨((DerivedCategory.PerfectScalar.fieldScalarComparison
      (fieldMap l Ω a).hom).app _).symm ≪≫ e⟩⟩

end WeilConjectures.TensorComparisonDescent
