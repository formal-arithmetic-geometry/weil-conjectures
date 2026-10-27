module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Free right dg modules on closed homogeneous sheaf generators

Source: Stacks Project, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators).

A graded sheaf of sets is encoded by its integer-indexed fibre sheaves. Its total
sheaf is their coproduct in sheaves, with the induced map to the constant integer
sheaf. This includes locally varying degrees: the coproduct is in sheaves, not
sectionwise sets. Conversely the fibres of any such degree map give this encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite

namespace CategoryTheory.SheafDg

set_option quotPrecheck false in
set_option hygiene false in
/-- The underlying sheaf of sets of a coefficient module (forget the module structure),
written inline from Mathlib's `SheafOfModules.toSheaf`.
Source: Stacks, Modules on Sites, 03CY
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
local notation "𝔘[" R "]" =>
  SheafOfModules.toSheaf (rings R) ⋙ sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{w})

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {S : Sheaf J CommRingCat.{w}}

/-- Right dg modules are left module objects in the reversed tensor category.
Source: Stacks, sdga.tex, 0FRI, right-module convention
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
abbrev RightModule (A : Algebra S) := Mod (Complex S)ᴹᵒᵖ (mop A.X)

/-- Forget a right action, keeping the underlying cochain complex.
Source: Stacks, sdga.tex, 0FRI
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightUnderlying (A : Algebra S) : RightModule A ⥤ Complex S :=
  Mod.forget (mop A.X) ⋙ unmopFunctor _

/-- The right action as a map of total tensor complexes.
Source: Stacks, sdga.tex, 0FRI
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightAction (A : Algebra S) (P : RightModule A) :
    (rightUnderlying A).obj P ⊗ A.X ⟶ (rightUnderlying A).obj P :=
  (ModObj.smul (M := mop A.X) (X := P.X)).unmop

/-- The degree-k free coefficient sheaf, with zero differential.
Source: Stacks, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def closedGenerators (S : Sheaf J CommRingCat.{w})
    (E : GradedObject ℤ (Sheaf J (Type w))) : Complex S where
  X n := (SheafFreeModule.free S).obj (E n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Functoriality of the closed-generator complex in its fibre sheaves.
Source: Stacks, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def closedGeneratorsFunctor (S : Sheaf J CommRingCat.{w}) :
    GradedObject ℤ (Sheaf J (Type w)) ⥤ Complex S where
  obj := closedGenerators S
  map e :=
    { f := fun n ↦ (SheafFreeModule.free S).map (e n)
      comm' := fun _ _ _ ↦ by simp [closedGenerators] }
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (SheafFreeModule.free S).map_id (M n)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (SheafFreeModule.free S).map_comp (f n) (g n)

/-- The actual free right dg module G(E) tensor A. The total tensor gives
F^n = sheafification of the direct sum of A^(n-k) labelled by E_k.
Since d_G=0, its differential is d(sa)=(-1)^k s da.
Source: Stacks, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def freeRightFunctor (A : Algebra S) :
    GradedObject ℤ (Sheaf J (Type w)) ⥤ RightModule A :=
  closedGeneratorsFunctor S ⋙ mopFunctor _ ⋙ Mod.free (mop A.X)

/-- The free right module on the supplied homogeneous generators.
Source: Stacks, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
abbrev freeRight (A : Algebra S) (E : GradedObject ℤ (Sheaf J (Type w))) :=
  (freeRightFunctor A).obj E

/-- Insert a closed generator as s tensor 1 in the free right module.
Source: Stacks, sdga.tex, Remark 0FSF
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def freeGenerator (A : Algebra S) (E : GradedObject ℤ (Sheaf J (Type w))) (k : ℤ) :
    E k ⟶ (𝔘[S]).obj
      (((rightUnderlying A).obj (freeRight A E)).X k) :=
  SheafFreeModule.generatorRaw S (E k) ≫ (𝔘[S]).map
    (((@MonoidalCategoryStruct.rightUnitor (Complex S) _
        (complexMonoidal S).toMonoidalCategoryStruct (closedGenerators S E)).inv ≫
      (closedGenerators S E ◁ MonObj.one (X := A.X))).f k)

/-- Evaluate the homogeneous right action on local sections.
Source: Stacks, sdga.tex, 0FRI
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightActionSection (A : Algebra S) (P : RightModule A) (p q : ℤ) (U : Cᵒᵖ)
    (x : (((rightUnderlying A).obj P).X p).val.obj U) (a : (A.X.X q).val.obj U) :
    (((rightUnderlying A).obj P).X (p + q)).val.obj U :=
  ((HomologicalComplex.ιTensorObj ((rightUnderlying A).obj P) A.X
    p q (p + q) rfl ≫ (rightAction A P).f (p + q)).val.app U)
      (tensorSection (((rightUnderlying A).obj P).X p) (A.X.X q) U x a)

/-- The unit of a dg algebra, evaluated in degree zero.
Source: Stacks, sdga.tex, definition-dga
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def oneSection (A : Algebra S) (U : Cᵒᵖ) : (A.X.X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ringedSiteModules.{w} (rings S)))).inv ≫
      (MonObj.one (X := A.X)).f 0).val.app U (1 : S.obj.obj U)

/-- The first balancing arrow, (p,a,n) mapped to (pa,n).
Source: Stacks, sdga.tex, tensor products
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightTensorBalance₁ (A : Algebra S) (P : RightModule A) (N : LeftModule A) :
    ((rightUnderlying A).obj P ⊗ A.X) ⊗ N.X ⟶ (rightUnderlying A).obj P ⊗ N.X :=
  rightAction A P ▷ N.X

/-- The second balancing arrow, (p,a,n) mapped to (p,an).
Source: Stacks, sdga.tex, tensor products
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightTensorBalance₂ (A : Algebra S) (P : RightModule A) (N : LeftModule A) :
    ((rightUnderlying A).obj P ⊗ A.X) ⊗ N.X ⟶ (rightUnderlying A).obj P ⊗ N.X :=
  (@MonoidalCategoryStruct.associator (Complex S) _
    (complexMonoidal S).toMonoidalCategoryStruct ((rightUnderlying A).obj P) A.X N.X).hom ≫
    ((rightUnderlying A).obj P ◁ ModObj.smul (M := A.X) (X := N.X))

/-- The balanced dg tensor is the actual coequalizer in coefficient complexes.
Thus it uses sheafified balanced tensor, direct-sum total grading and Koszul d.
Source: Stacks, sdga.tex, tensor products
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightTensor (A : Algebra S) (P : RightModule A) (N : LeftModule A) : Complex S :=
  coequalizer (rightTensorBalance₁ A P N) (rightTensorBalance₂ A P N)

/-- The unbalanced-to-balanced tensor projection.
Source: Stacks, sdga.tex, tensor products
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def rightTensorπ (A : Algebra S) (P : RightModule A) (N : LeftModule A) :
    (rightUnderlying A).obj P ⊗ N.X ⟶ rightTensor A P N :=
  coequalizer.π (rightTensorBalance₁ A P N) (rightTensorBalance₂ A P N)

/-- The underlying graded free-tensor formula on any graded coefficient sheaf M:
its nth term is the sum over k of O[E_k] tensor M^(n-k). This is the reduced
balanced tensor F_A(E) tensor_A M when M has a graded left A-action.
Source: Stacks, sdga.tex, 0FSF and the first display in 0FSG
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
def freeGradedTensor (S : Sheaf J CommRingCat.{w})
    (E : GradedObject ℤ (Sheaf J (Type w))) :
    GradedObject ℤ (ringedSiteModules.{w} (rings S)) ⥤
      GradedObject ℤ (ringedSiteModules.{w} (rings S)) where
  obj M n := ∐ (fun k : ℤ ↦ (SheafFreeModule.free S).obj (E k) ⊗ M (n - k))
  map {M N} f n := Sigma.desc (fun k : ℤ ↦
    ((SheafFreeModule.free S).obj (E k) ◁ f (n - k)) ≫
      Sigma.ι (fun j : ℤ ↦ (SheafFreeModule.free S).obj (E j) ⊗ N (n - j)) k)
  map_id _ := by
    funext n
    apply Sigma.hom_ext
    intro k
    simp
  map_comp _ _ := by
    funext n
    apply Sigma.hom_ext
    intro k
    simp

/-- The reduced free graded tensor sends zero maps to zero maps.
Source: Stacks, sdga.tex, 0FSF, functorial action on direct sums
(blueprint: def-sfb-sheaf-dg-free-closed-generators). -/
instance freeGradedTensor_preservesZero (S : Sheaf J CommRingCat.{w})
    (E : GradedObject ℤ (Sheaf J (Type w))) :
    (freeGradedTensor S E).PreservesZeroMorphisms where
  map_zero M N := by
    funext n
    apply Sigma.hom_ext
    intro k
    simp [freeGradedTensor]

end CategoryTheory.SheafDg
