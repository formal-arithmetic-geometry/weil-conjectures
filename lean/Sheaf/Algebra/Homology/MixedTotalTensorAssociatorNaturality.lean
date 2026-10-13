/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module
public import Sheaf.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.BifunctorAssociator
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
/-!
# Naturality of the mixed total-complex associator

Source: Stacks Project, Tag 0BYJ; Mathlib's total bifunctor associator.
(blueprint: lem-pc-mixed-total-tensor-associator-naturality).
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
namespace DerivedCategory
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
/-- The module associator after extension of scalars in its third variable.
Source: Stacks Project, Tag 0BYJ.
(blueprint: lem-pc-mixed-total-tensor-associator-naturality) -/
noncomputable def mixedModuleAssociator :
    bifunctorComp₁₂ (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) ≅
    bifunctorComp₂₃ (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun N ↦
    NatIso.ofComponents (fun F ↦ α_ P N
      ((ModuleCat.extendScalars (algebraMap R A)).obj F)) (by
        intro F F' f
        exact associator_naturality_right P N _)) (by
          intro N N' n
          apply NatTrans.ext
          funext F
          exact associator_naturality_middle P n _)) (by
            intro P P' p
            apply NatTrans.ext
            funext N
            apply NatTrans.ext
            funext F
            exact associator_naturality_left p N _)
/-- The canonical total-complex associator obtained from the module associator.
Source: Stacks Project, Tag 0BYJ; `HomologicalComplex.mapBifunctorAssociator`.
(blueprint: lem-pc-mixed-total-tensor-associator-naturality) -/
noncomputable def mixedChainAssociator
    (P N : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    mapBifunctor (mapBifunctor P N (curriedTensor _) (.up ℤ)) F
      (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) ≅
    mapBifunctor P (mapBifunctor N F (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ))
      (curriedTensor _) (.up ℤ) := by
  have : HasGoodTrifunctor₁₂Obj (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) P N F (.up ℤ) (.up ℤ) := by
    intro i j
    change Limits.PreservesColimit _
      (tensorRight ((ModuleCat.extendScalars (algebraMap R A)).obj (F.X j)))
    exact Limits.preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight _)
  have : HasGoodTrifunctor₂₃Obj (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) P N F (.up ℤ) (.up ℤ) (.up ℤ) := by
    intro i j
    infer_instance
  exact mapBifunctorAssociator (mixedModuleAssociator R A) P N F (.up ℤ) (.up ℤ) (.up ℤ)
/-- The canonical total associator restricts to ordinary rebracketing on triple summands.
Source: Stacks Project, Tag 0BYJ; Mathlib's summand formula.
(blueprint: lem-pc-mixed-total-tensor-associator-naturality) -/
theorem mixedChainAssociator_summand :
    ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) (F : CochainComplex (ModuleCat.{u} R) ℤ)
      (i j k : ℤ),
        ((ModuleCat.mixedTensor (algebraMap R A)).map
          (ιMapBifunctor P N (curriedTensor _) (.up ℤ) i j (i + j) rfl)).app (F.X k) ≫
          ιMapBifunctor (((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.obj P).obj N) F
            (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) (i + j) k ((i + j) + k) rfl ≫
          (mixedChainAssociator R A P N F).hom.f ((i + j) + k) =
        (α_ (P.X i) (N.X j)
          ((ModuleCat.extendScalars (algebraMap R A)).obj (F.X k))).hom ≫
          ((curriedTensor (ModuleCat.{u} A)).obj (P.X i)).map
            (ιMapBifunctor N F (ModuleCat.mixedTensor (algebraMap R A))
              (.up ℤ) j k (j + k) rfl) ≫
          ιMapBifunctor P (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj N).obj F)
            (curriedTensor _) (.up ℤ)
            i (j + k) ((i + j) + k) (Int.add_assoc i j k).symm := by
  intro P N F i j k
  have : HasGoodTrifunctor₁₂Obj (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) P N F (.up ℤ) (.up ℤ) := by
    intro s t
    change Limits.PreservesColimit _
      (tensorRight ((ModuleCat.extendScalars (algebraMap R A)).obj (F.X t)))
    exact Limits.preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight _)
  have : HasGoodTrifunctor₂₃Obj (curriedTensor (ModuleCat.{u} A))
      (ModuleCat.mixedTensor (algebraMap R A)) P N F (.up ℤ) (.up ℤ) (.up ℤ) := by
    intro s t
    infer_instance
  rw [← Category.assoc]
  exact ι_mapBifunctorAssociatorX_hom (mixedModuleAssociator R A)
    P N F (.up ℤ) (.up ℤ) (.up ℤ) i j k ((i + j) + k) rfl

/-- The canonical mixed total-complex associator is natural in all three complexes.
Source: Stacks Project, Tag 0BYJ, associativity of total tensor products.
(blueprint: lem-pc-mixed-total-tensor-associator-naturality)

Proof: in each degree, precompose both sides with the inclusions of triple tensor
summands. These inclusions jointly determine a map, since tensoring over A preserves
coproducts. The total associator on each summand is the ordinary module associator.
The total map induced by f is the tensor of its three degreewise components.
Naturality of the module associator in those three components equates the two maps
on each summand. The componentwise equalities yield equality of chain maps.
The differentials need no new check: mixedChainAssociator is already a chain isomorphism
by Mathlib's total-complex associator. This works for unbounded complexes since the
sums are coproducts, with no finiteness assumption. It also covers zero complexes and
zero morphisms, whose summand maps vanish. -/
theorem mixedChainAssociator_naturality :
    let T := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex
    let S := ModuleCat.mixedTotalTensor (algebraMap R A)
    let Lc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₁₂ T S))
    let Uc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₂₃ T S))
    ∀ X Y (f : X ⟶ Y),
      Lc.map f ≫ (mixedChainAssociator R A Y.1.1 Y.1.2 Y.2).hom =
        (mixedChainAssociator R A X.1.1 X.1.2 X.2).hom ≫ Uc.map f := by sorry
end DerivedCategory
