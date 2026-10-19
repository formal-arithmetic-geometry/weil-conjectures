/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Completed pullback on the published completed-coefficient categories

Source: Stacks proetale.tex, Tag 099N (2),(5), blueprint order 1261.
(blueprint: lem-weil-pbc-ringed-topoi-module-adjunction)
The coefficient structure is fixed on all quotient projections. Ordinary pullback
is its total derived sheafified tensor inverse image. Completion is characterized
by its reflection universal property on the actual intrinsic complete subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The original ring-valued presentation of the actual coefficient limit.
Source: blueprint order 1261 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualCompletedRing (T : Scheme.{u}) :=
  (adicLisseForget T).obj (pbcAdicCompletion T d)

/-- Forgetting commutativity in an actual quotient projection.
Source: blueprint order 1261 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualProjection (T : Scheme.{u}) (n : ℕ) :=
  (adicLisseForget T).map (pbcAdicProjection T d n)

/-- The recorded coefficient structure map, after forgetting commutativity.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualStructureMap : pbcActualCompletedRing d Y ⟶
    (proEtaleSheafDirectImage g RingCat.{u + 1}).obj (pbcActualCompletedRing d X) :=
  ⟨Functor.whiskerRight (completedCoefficientDirectImageMap g d).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The published sectionwise module direct image.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualModulePush := completedModuleDirectImage g d

/-- The published module inverse image followed by completed scalar tensor.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualModulePull := completedModulePullback g d

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The ordinary tensor-unit section uses the actual model-site inverse-image unit.
Source: Stacks 03D2 and 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualModuleUnitSection (M : pbcModules Y (pbcAdicCompletion Y d))
    (U : Y.ProEt) (x : M.val.obj (op U)) :
    ((pbcActualModulePush g d).obj ((pbcActualModulePull g d).obj M)).val.obj (op U) :=
  reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
    (op ((proEtaleBaseChange g).obj U)) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (proEtaleModelRingUnit g
      (pbcAdicCompletion Y d))).unit.app
        ((proEtaleModuleToModel ((adicLisseForget Y).obj (pbcAdicCompletion Y d))).obj M)).val.app
          (op (AsSmall.up.obj U)) x)

/-- The published pullback and direct image have the uniquely normalized tensor adjunction.
Source: Stacks 03D2 and 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: on the small model apply the ordinary module inverse-image adjunction,
then the tensor-restriction adjunction of the completed coefficient map.
Transport along the sectionwise model equivalences. Its unit is the model unit
followed by 1 tensor x, exactly as displayed. These local tensor generators fix
the Hom transpose and hence the adjunction uniquely. -/
theorem pbcActualModuleAdjunction_exists :
    ∃! adj : pbcActualModulePull g d ⊣ pbcActualModulePush g d,
      ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (U : Y.ProEt) (x : M.val.obj (op U)),
        (adj.unit.app M).val.app (op U) x = pbcActualModuleUnitSection g d M U x := by
  sorry

/-- The actual module adjunction, with the inverse-image tensor unit retained.
Source: Stacks 03D2 and 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualModuleAdjunction := (pbcActualModuleAdjunction_exists g d).exists.choose

/-- Pullback and pushforward are additive.
Source: 03D7 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: sectionwise direct image preserves sums of maps. Sheafified inverse image
and its scalar tensor are additive, by their ordinary module construction. -/
theorem pbcActualModuleOperations_additive :
    (pbcActualModulePull g d).Additive ∧ (pbcActualModulePush g d).Additive := by
  sorry

/-- Additivity of the specified module pullback.
Source: 03D7 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualModulePull_additive : (pbcActualModulePull g d).Additive :=
  (pbcActualModuleOperations_additive g d).1

/-- Additivity of the specified module direct image.
Source: 03D7 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualModulePush_additive : (pbcActualModulePush g d).Additive :=
  (pbcActualModuleOperations_additive g d).2

/-- K-flat resolving complexes define the actual total left derived pullback.
Source: 099N, 0D6D (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: use the one-object case of diagram-kflat-replacements, with flat terms.
Module inverse image and tensor preserve quasi-isomorphisms between these resolving
objects. Apply left-derived-from-kflat-class; it gives the universal derived
counit, invertible on that resolving class. No site universes are identified. -/
@[instance] theorem pbcActualPull_hasLeftDerived :
    ((pbcActualModulePull g d).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  sorry

/-- The published ordinary total derived pullback with its fixed resolving pair.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualDerivedPull := completedOrdinaryPullback g d

/-- The published universal ordinary-pullback counit.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualPullCounit := completedOrdinaryPullbackCounit g d

/-- Its computation on cochain representatives retains the universal counit.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualPullComplexCounit (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcActualDerivedPull g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((pbcActualModulePull g d).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcActualDerivedPull g d).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (pbcActualPullCounit g d).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((pbcActualModulePull g d).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((pbcActualModulePull g d).mapHomologicalComplex (.up ℤ)).obj P)

/-- Ordinary derived direct image, computed using K-injectives in all modules.
Source: 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
abbrev pbcActualDerivedPush : PbcCompletedDerived X d ⥤ PbcCompletedDerived Y d :=
  completedDerivedDirectImage g d

/-- The universal homotopy-category unit of ordinary derived direct image.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualPushUnit :
    (pbcActualModulePush g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ pbcActualDerivedPush g d :=
  (pbcActualModulePush g d).rightDerivedFunctorUnit

/-- Universality of the named ordinary left derived pair.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: unfold its totalLeftDerived and counit; the universal Kan-extension
construction gives IsLeftDerivedFunctor. -/
@[instance] theorem pbcActualPullUniversal :
    (pbcActualDerivedPull g d).IsLeftDerivedFunctor (pbcActualPullCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  sorry

/-- Universality of the named ordinary right derived pair.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: unfold its totalRightDerived and unit; the universal Kan-extension
construction gives IsRightDerivedFunctor. -/
@[instance] theorem pbcActualDirectUniversal :
    (pbcActualDerivedPush g d).IsRightDerivedFunctor
      (pbcActualPushUnit g d)
        (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  sorry

/-- The resolving left derived pair remains universal after the indicated direct image.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the K-flat resolving construction is pointwise and hence absolute.
Postcomposition by ordinary derived direct image preserves its universal derived
comparison; equivalently compute at a resolving complex, where the counit is
invertible. This gives the stated universal left derived pair. -/
@[instance] theorem pbcActualDerivedLeftComposite :
    (pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d))
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  sorry

/-- The resolving right derived pair remains universal after the indicated pullback.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the K-injective resolving construction is pointwise and hence absolute.
Postcomposition by ordinary derived pullback preserves its universal derived
comparison; equivalently compute at a K-injective complex, where the unit is
invertible. This gives the stated universal right derived pair. -/
@[instance] theorem pbcActualDerivedRightComposite :
    (pbcActualDerivedPush g d ⋙ pbcActualDerivedPull g d).IsRightDerivedFunctor
      (whiskerRight (pbcActualPushUnit g d) (pbcActualDerivedPull g d) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  sorry

/-- The derived adjunction obtained from the actual module adjunction and its
universal derived counit/unit. Source: Stacks Tag 099N
(blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualDerivedAdjunction :
    pbcActualDerivedPull g d ⊣ pbcActualDerivedPush g d :=
  (pbcActualModuleAdjunction g d).mapHomotopyCategory (.up ℤ) |>.derived
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
      (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ))
      (pbcActualPullCounit g d) (pbcActualPushUnit g d)

/-- The ordinary comparison on resolving complexes uniquely fixes the derived shift.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the additive ordinary functor commutes with termwise shifts. Its universal
derived comparison descends that structure and fixes it on resolving complexes.
Every derived object has such a representative, which proves uniqueness and
transports the zero and addition identities. -/
theorem pbcActualPullShift_exists :
    ∃! q : (pbcActualDerivedPull g d).CommShift ℤ,
      (fun [qInst : (pbcActualDerivedPull g d).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualPullCounit g d) ℤ) (qInst := q) := by
  sorry

/-- The canonical shift structure, normalized by the universal derived comparison.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualPullShift : (pbcActualDerivedPull g d).CommShift ℤ :=
  (pbcActualPullShift_exists g d).exists.choose

/-- The ordinary comparison on resolving complexes uniquely fixes the derived shift.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the additive ordinary functor commutes with termwise shifts. Its universal
derived comparison descends that structure and fixes it on resolving complexes.
Every derived object has such a representative, which proves uniqueness and
transports the zero and addition identities. -/
theorem pbcActualPushShift_exists :
    ∃! q : (pbcActualDerivedPush g d).CommShift ℤ,
      (fun [qInst : (pbcActualDerivedPush g d).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualPushUnit g d) ℤ) (qInst := q) := by
  sorry

/-- The canonical shift structure, normalized by the universal derived comparison.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualPushShift : (pbcActualDerivedPush g d).CommShift ℤ :=
  (pbcActualPushShift_exists g d).exists.choose


variable (T : Scheme.{u})

/-- The intrinsic complete subcategory is reflective, with the Koszul completion unit.
Source: 099N (2),(5), 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the derived inverse limit of the strict negative-Koszul tower is completion.
Its degree-zero augmentation is a reflection unit, by ringed-koszul-completion-reflector.
Transport the comparison through pbcCompletedComparison. This preserves the unit,
so the predicate is exactly PbcIsIntrinsicallyComplete, even over the empty scheme.
The reflection property determines the output and unit up to unique isomorphism. -/
@[instance] theorem pbcActualCompleteInclusion_isRightAdjoint :
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).IsRightAdjoint := by
  sorry

/-- The canonical reflection onto the actual intrinsically complete subcategory.
Its defining universal property determines its objects up to the equality used
here, namely unique unit-compatible isomorphism.
Source: 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualCompletion : PbcCompletedDerived T d ⥤ PbcCompletedDerived T d :=
  (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).leftAdjoint ⋙
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d))

/-- The universal completion unit of the actual intrinsic complete subcategory.
Source: 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualCompletionUnit : 𝟭 (PbcCompletedDerived T d) ⟶ pbcActualCompletion d T :=
  (Adjunction.ofIsRightAdjoint (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d))).unit

/-- Ordinary derived pullback followed by the unit-normalized completion reflector.
This is equivalently the derived limit of the pulled-back strict reduction tower,
with its quotient augmentation, as asserted by the source's canonical comparison.
Source: 099N (2),(5) (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualCompletedPull : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d :=
  pbcActualDerivedPull g d ⋙ pbcActualCompletion d X

/-- The comparison is the actual completion unit after ordinary derived pullback.
Source: 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualCompletedPullUnit : pbcActualDerivedPull g d ⟶ pbcActualCompletedPull g d :=
  whiskerLeft (pbcActualDerivedPull g d) (pbcActualCompletionUnit d X)

/-- The completion reflection lands in the actual intrinsic complete predicate.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: its left adjoint has values in that full subcategory by construction.
Composing with the inclusion retains the same membership witness. -/
theorem pbcActualCompletedPull_isComplete (K : PbcCompletedDerived Y d) :
    PbcIsIntrinsicallyComplete X d ((pbcActualCompletedPull g d).obj K) := by
  sorry

/-- Completion has the unique shift comparison commuting with its actual unit.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the Koszul tower shifts termwise and the Roos realization preserves shifts.
Its augmentation commutes with this comparison. The reflection unit determines
maps into complete objects, so that comparison and its coherence are unique. -/
theorem pbcActualCompletionShift_exists :
    ∃! q : (pbcActualCompletion d T).CommShift ℤ,
      (fun [qInst : (pbcActualCompletion d T).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualCompletionUnit d T) ℤ) (qInst := q) := by
  sorry

/-- The unit-normalized shift of the completion reflector.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualCompletionShift : (pbcActualCompletion d T).CommShift ℤ :=
  (pbcActualCompletionShift_exists d T).exists.choose

/-- Completed pullback inherits ordinary pullback and completion shifts.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
instance pbcActualCompletedPullShift : (pbcActualCompletedPull g d).CommShift ℤ :=
  inferInstanceAs ((pbcActualDerivedPull g d ⋙ pbcActualCompletion d X).CommShift ℤ)

/-- Direct image commutes with completion with the specified completion unit.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: direct image commutes with derived inverse limits. Apply its perfect
projection arrows to the finite free Koszul coefficient complexes and their
strict transitions. Their derived inverse limit is the completion comparison.
It preserves the augmentation and is invertible. Completeness of derived direct
image of a complete object gives uniqueness from the reflection property. -/
theorem pbcActualDirectCompletionIso_exists :
    ∃! e : pbcActualDerivedPush g d ⋙ pbcActualCompletion d Y ≅
        pbcActualCompletion d X ⋙ pbcActualDerivedPush g d,
      ∀ K : PbcCompletedDerived X d,
        (pbcActualCompletionUnit d Y).app ((pbcActualDerivedPush g d).obj K) ≫
            e.hom.app K =
          (pbcActualDerivedPush g d).map ((pbcActualCompletionUnit d X).app K) := by
  sorry

/-- The completion comparison uniquely fixed by the quotient augmentation.
Source: Stacks 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
def pbcActualDirectCompletionIso := (pbcActualDirectCompletionIso_exists g d).exists.choose

end AlgebraicGeometry.Scheme
