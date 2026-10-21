/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Limits.Final
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.CompatibleCoefficientTower
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.StrictRoosHomotopyFunctor
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Scalar augmentation and its derived descent

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks Project, Tags 03EK, 014E, 08TC, 06YS, 06YT, 06XN and 05S9.
(blueprint: lem-pur-quotient-scalar-comparison-descent)

The tensor factors in the change-of-rings API are written scalar first. Natural index
`n` denotes positive level `n + 1`. Presentation isomorphisms fix the actual sheafified
tensors and their maps; they are not additional hypotheses in the existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

namespace SheafOfModules.ScalarComparisonProof

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]

private noncomputable abbrev res {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

variable {R S T : Sheaf J CommRingCat.{u}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (x : R.obj.obj U) :
    q.hom.app U (f.hom.app U x) = g.hom.app U x :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) x

private noncomputable def sectionMap (U : Cᵒᵖ) :
    (changeOfRingsPresheaf f M).obj U ⟶
      (ModuleCat.restrictScalars (q.hom.app U).hom).obj
        ((changeOfRingsPresheaf g M).obj U) := by
  letI : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (f.hom.app U).hom
  letI : Module (R.obj.obj U) (T.obj.obj U) := Module.compHom _ (g.hom.app U).hom
  let h : S.obj.obj U →ₗ[R.obj.obj U] T.obj.obj U :=
    { toFun := q.hom.app U
      map_add' := map_add _
      map_smul' := fun x s ↦ by
        change q.hom.app U (f.hom.app U x * s) = g.hom.app U x * q.hom.app U s
        rw [map_mul, coefficient_comp f g q hq] }
  exact ModuleCat.ofHom
    (X := (changeOfRingsPresheaf f M).obj U)
    (Y := (ModuleCat.restrictScalars (q.hom.app U).hom).obj
      ((changeOfRingsPresheaf g M).obj U))
    { toFun := TensorProduct.map h (LinearMap.id : M.val.obj U →ₗ[R.obj.obj U] M.val.obj U)
      map_add' := map_add _
      map_smul' := fun s z ↦ by
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul t x =>
          change S.obj.obj U at t
          change q.hom.app U (s * t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x =
            (q.hom.app U s * q.hom.app U t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x
          rw [map_mul]
        | add z w hz hw => simp only [smul_add, map_add, hz, hw] }

private theorem sectionMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionMap f g q hq M U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x) =
      (show (changeOfRingsPresheaf g M).obj U from
        q.hom.app U s ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x) := rfl

private theorem restriction_tmul {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : B.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsPresheaf c N).map i (s ⊗ₜ[A.obj.obj U,(c.hom.app U).hom] x) =
      B.obj.map i s ⊗ₜ[A.obj.obj V,(c.hom.app V).hom] N.val.map i x :=
  Classical.choose_spec (exists_changeOfRingsMap c N i) s x

private noncomputable def presheafMap :
    changeOfRingsPresheaf f M ⟶
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).obj (changeOfRingsPresheaf g M) where
  app := sectionMap f g q hq M
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change sectionMap f g q hq M V ((changeOfRingsPresheaf f M).map i
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) =
      (changeOfRingsPresheaf g M).map i
        (sectionMap f g q hq M U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x))
    rw [restriction_tmul, sectionMap_tmul, sectionMap_tmul, restriction_tmul]
    simp only [map_one]

private noncomputable def sheafMap : changeOfRings f M ⟶ (res q).obj (changeOfRings g M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).symm
    (presheafMap f g q hq M ≫
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
              (changeOfRingsPresheaf g M)))

private noncomputable def tensorSection (c : R ⟶ S)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRings c N).val.obj U :=
  (toSheafify J (changeOfRingsPresheaf c N).presheaf).app U
    (s ⊗ₜ[R.obj.obj U,(c.hom.app U).hom] x)

include f g q hq M in
private theorem sheafMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (sheafMap f g q hq M).val.app U (tensorSection f M U s x) =
      tensorSection g M U (q.hom.app U s) x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (F := (res q).obj (changeOfRings g M))
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).apply_symm_apply
      (presheafMap f g q hq M ≫
        (PresheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat RingCat)).map q).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
                (changeOfRingsPresheaf g M)))
  exact congrArg (fun k ↦ k.app U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) h

private theorem map_tensorSection
    {N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsHom f M a).val.app U (tensorSection f M U s x) =
      tensorSection f N U s (a.val.app U x) := by
  let k : changeOfRingsPresheaf f M ⟶ changeOfRingsPresheaf f N :=
    { app := fun V ↦ (ModuleCat.extendScalars (f.hom.app V).hom).map (a.val.app V)
      naturality := changeOfRingsHom_naturality f M a }
  let z : (changeOfRingsPresheaf f M).presheaf.obj U :=
    s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map k)
  have h := congrArg (fun η ↦ (η.app U).hom z) hn
  change (toSheafify J (changeOfRingsPresheaf f N).presheaf).app U
      ((ModuleCat.extendScalars (f.hom.app U).hom).map (a.val.app U)
        (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) = _ at h
  erw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm



private theorem restricted_tensor_ext
    {R S T : Sheaf J CommRingCat.{u}} (φ : R ⟶ T) (c : S ⟶ T)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (a b : (res c).obj (changeOfRings φ M) ⟶ N)
    (h : ∀ U s x, a.val.app U (tensorSection φ M U s x) =
      b.val.app U (tensorSection φ M U s x)) : a = b := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

end SheafOfModules.ScalarComparisonProof

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T

/-- Presentations of the two ordinary tensor functors, with their maps fixed on tensors.
Source: Stacks 03EK and the strict tower construction of Stacks 08TC
(blueprint: lem-pur-quotient-scalar-comparison-descent).
These fields package the specified functors, including their canonical transition maps. -/
structure ScalarTowerTensorModel (φ : R ⟶ S) (c : ∀ n, S ⟶ B n)
    (b : ∀ n, B (n + 1) ⟶ B n) where
  E : ringedSiteModules.{u} (𝓡 R) ⥤
    ringedSiteModules.{u} (𝓡 S)
  V : ringedSiteModules.{u} (𝓡 R) ⥤
    (ℕᵒᵖ ⥤ ringedSiteModules.{u} (𝓡 S))
  E_add : E.Additive
  V_add : V.Additive
  eE : ∀ M, E.obj M ≅ changeOfRings φ M
  eV : ∀ M n, (V.obj M).obj (op n) ≅
    (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (c n))).obj
        (changeOfRings (φ ≫ c n) M)
  E_map : ∀ {M N} (f : M ⟶ N),
    (eE M).inv ≫ E.map f ≫ (eE N).hom = changeOfRingsHom φ M f
  V_map : ∀ {M N} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U) (z : (B n).obj.obj U),
    (((eV M n).inv ≫ (V.map f).app (op n) ≫ (eV N n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) N).presheaf).app U
          (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] f.val.app U x)
  transition : ∀ M (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U)
    (z : (B (n + 1)).obj.obj U),
    (((eV M (n + 1)).inv ≫ (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫
        (eV M n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c (n + 1)) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c (n + 1)).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
          ((((b n).hom.app U) z) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)

attribute [instance] ScalarTowerTensorModel.E_add ScalarTowerTensorModel.V_add

namespace ScalarTowerTensorModel

variable {φ : R ⟶ S} {c : ∀ n, S ⟶ B n} {b : ∀ n, B (n + 1) ⟶ B n}
  (M : ScalarTowerTensorModel φ c b)

/-- Ordinary extension of scalars, applied termwise to complexes.
Source: Stacks 03EK (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev F := M.E.mapHomologicalComplex (ComplexShape.up ℤ)

variable [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]

/-- The actual shifted product cone of the strict coefficient tensor tower.
Source: Stacks 014E and 08TC (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev G := M.V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ roosF

/-- The zero shifted-product component and all scalar-augmentation product projections.
Generators are images of presheaf tensors under the sheafification unit, so this
condition specifies sheaf maps even when global sections are not pure tensors.
Source: Stacks 03EK, 014E and 08TC
(blueprint: lem-pur-quotient-scalar-comparison-descent). -/
def AugmentationCoordinates (β : M.F ⟶ M.G) : Prop :=
  (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) (i : ℤ),
    (β.app P).f (i + 1) ≫
      (roosχ ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) i).hom ≫
        biprod.fst = 0) ∧
  ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ)
    (i : ℤ) (n : ℕ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (s : S.obj.obj U),
    ((((M.eE (P.X i)).inv ≫
        (β.app P ≫ roosEval
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) n).f i ≫
        (M.eV (P.X i) n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf φ (P.X i)).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
      (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) (P.X i)).presheaf).app U
        (((c n).hom.app U s) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]

/-- Everywhere-defined universal left derived functors, computed on every flat-term
K-flat complex, and the unique natural descent normalized on all such complexes.
The full comparison equation gives independence of every resolution; uniqueness is
required already from its restriction to the resolving class.
Source: Stacks 06YS, 06XN and 05S9
(blueprint: lem-pur-quotient-scalar-comparison-descent). -/
def DerivedDescent (β : M.F ⟶ M.G) : Prop :=
  ∃ (LF LG : DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S)))
    (εF : DerivedCategory.Q ⋙ LF ⟶ M.F ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ M.G ⋙ DerivedCategory.Q),
    LF.IsLeftDerivedFunctor εF
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) ∧
    LG.IsLeftDerivedFunctor εG
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) ∧
    (∀ X, Nonempty ((Functor.RightExtension.mk LF εF).IsPointwiseRightKanExtensionAt X)) ∧
    (∀ X, Nonempty ((Functor.RightExtension.mk LG εG).IsPointwiseRightKanExtensionAt X)) ∧
    (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (P.X i)) →
        IsIso (εF.app P) ∧ IsIso (εG.app P)) ∧
    ∃ χ : LF ⟶ LG,
      (∀ P, χ.app (DerivedCategory.Q.obj P) ≫ εG.app P =
        εF.app P ≫ DerivedCategory.Q.map (β.app P)) ∧
      ∀ χ' : LF ⟶ LG,
        (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
          P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (P.X i)) →
            χ'.app (DerivedCategory.Q.obj P) ≫ εG.app P =
              εF.app P ≫ DerivedCategory.Q.map (β.app P)) → χ' = χ

end ScalarTowerTensorModel

omit [EssentiallySmall.{u} C] in
private lemma tensor_generator_ext (φ : R ⟶ S)
    (A : ringedSiteModules.{u} (𝓡 R)) (N : ringedSiteModules.{u} (𝓡 S))
    (f g : changeOfRings φ A ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : A.val.obj U) (s : S.obj.obj U),
      f.val.app U ((toSheafify J (changeOfRingsPresheaf φ A).presheaf).app U
        (s ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      g.val.app U ((toSheafify J (changeOfRingsPresheaf φ A).presheaf).app U
        (s ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := 𝓡 S) (𝟙 _)
  apply (adj.homEquiv (changeOfRingsPresheaf φ A) N).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U x 1

private def scalarIdPresheafIso (A : ringedSiteModules.{u} (𝓡 R)) :
    A.val ≅ changeOfRingsPresheaf (𝟙 R) A := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (A.val.obj U)).symm) ?_
  intro U V f
  ext x
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (A.val.obj V)
      (A.val.map f x) =
    changeOfRingsMap (𝟙 R) A f
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (A.val.obj U) x)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) A f) (1 : R.obj.obj U) x).symm

private def scalarIdIso (A : ringedSiteModules.{u} (𝓡 R)) :
    changeOfRings (𝟙 R) A ≅ A := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := 𝓡 R) (𝟙 _)
  let e := (scalarIdPresheafIso A).symm
  let a := (adj.homEquiv _ A).symm e.hom
  have ha : adj.homEquiv _ A a = e.hom := Equiv.apply_symm_apply _ _
  refine ⟨a, ⟨e.inv ≫ adj.unit.app _⟩, ?_, ?_⟩
  · apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, ha]
    change e.hom ≫ (e.inv ≫ adj.unit.app _) = _
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact (adj.homEquiv_id _).symm
  · apply SheafOfModules.hom_ext
    change (e.inv ≫ adj.unit.app _) ≫ a.val = 𝟙 _
    rw [Category.assoc]
    change e.inv ≫ adj.homEquiv _ A a = _
    rw [ha, e.inv_hom_id]

omit [EssentiallySmall.{u} C] in
private lemma scalarIdIso_tmul (A : ringedSiteModules.{u} (𝓡 R))
    (U : Cᵒᵖ) (x : A.val.obj U) (r : R.obj.obj U) :
    (scalarIdIso A).hom.val.app U
      ((toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
        (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) = r • x := by
  have h : (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
      (changeOfRingsPresheaf (𝟙 R) A) ≫ (scalarIdIso A).hom.val =
      (scalarIdPresheafIso A).inv := by
    exact (PresheafOfModules.sheafificationAdjunction (R := 𝓡 R) (𝟙 _)).homEquiv
      (changeOfRingsPresheaf (𝟙 R) A) A |>.apply_symm_apply _
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
    (changeOfRingsPresheaf (𝟙 R) A) ≫ (scalarIdIso A).hom.val).app U
      (r ⊗ₜ[R.obj.obj U,((𝟙 R : R ⟶ R).hom.app U).hom] x) = r • x
  rw [h]
  change (ModuleCat.extendScalarsId (R.obj.obj U)).hom.app (A.val.obj U)
    (r ⊗ₜ[R.obj.obj U,((𝟙 R : R ⟶ R).hom.app U).hom] x) = r • x
  rfl

omit [EssentiallySmall.{u} C] in
private lemma scalarIdIso_naturality {A N : ringedSiteModules.{u} (𝓡 R)}
    (f : A ⟶ N) :
    changeOfRingsHom (𝟙 R) A f ≫ (scalarIdIso N).hom =
      (scalarIdIso A).hom ≫ f := by
  apply tensor_generator_ext
  intro U x r
  have hn := toSheafify_naturality J
    ((PresheafOfModules.toPresheaf _).map
      ({ app := fun U ↦ (ModuleCat.extendScalars
          ((𝟙 R : R ⟶ R).hom.app U).hom).map (f.val.app U)
         naturality := changeOfRingsHom_naturality (𝟙 R) A f } :
        changeOfRingsPresheaf (𝟙 R) A ⟶ changeOfRingsPresheaf (𝟙 R) N))
  change (scalarIdIso N).hom.val.app U
    ((changeOfRingsHom (𝟙 R) A f).val.app U _) = _
  rw [show (changeOfRingsHom (𝟙 R) A f).val.app U
      ((toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
        (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) =
    (toSheafify J (changeOfRingsPresheaf (𝟙 R) N).presheaf).app U
      (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] f.val.app U x) from by
        exact ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app U) hn).symm _]
  rw [scalarIdIso_tmul]
  change _ = f.val.app U ((scalarIdIso A).hom.val.app U _)
  rw [scalarIdIso_tmul]
  exact ((f.val.app U).hom.map_smul r x).symm

omit [EssentiallySmall.{u} C] in
private lemma scalarIdIso_inv_unit (A : ringedSiteModules.{u} (𝓡 R))
    (U : Cᵒᵖ) (x : A.val.obj U) :
    (scalarIdIso A).inv.val.app U x =
      (toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
        ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x) := by
  have h := scalarIdIso_tmul A U x 1
  rw [one_smul] at h
  have hi := congrArg (fun y ↦ (scalarIdIso A).inv.val.app U y) h
  have hinv := congrArg (fun f ↦ f.val.app U) (scalarIdIso A).hom_inv_id
  have hh := ConcreteCategory.congr_hom hinv
    ((toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
      ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U,((𝟙 R : R ⟶ R).hom.app U).hom] x))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hh
  exact hi.symm.trans hh


open ScalarComparisonProof

private def scalarArrow {φ : R ⟶ S} {c : ∀ n, S ⟶ B n}
    {b : ∀ n, B (n + 1) ⟶ B n} (M : ScalarTowerTensorModel φ c b)
    (A : ringedSiteModules.{u} (𝓡 R)) (n : ℕ) : M.E.obj A ⟶ (M.V.obj A).obj (op n) :=
  (M.eE A).hom ≫ sheafMap φ (φ ≫ c n) (c n) rfl A ≫ (M.eV A n).inv

omit [EssentiallySmall.{u} C] in
private theorem scalarArrow_naturality {φ : R ⟶ S} {c : ∀ n, S ⟶ B n}
    {b : ∀ n, B (n + 1) ⟶ B n} (M : ScalarTowerTensorModel φ c b)
    {A N : ringedSiteModules.{u} (𝓡 R)} (f : A ⟶ N) (n : ℕ) :
    M.E.map f ≫ scalarArrow M N n = scalarArrow M A n ≫ (M.V.map f).app (op n) := by
  apply (cancel_epi (M.eE A).inv).1
  apply (cancel_mono (M.eV N n).hom).1
  have he : M.E.map f ≫ (M.eE N).hom =
      (M.eE A).hom ≫ changeOfRingsHom φ A f := by
    rw [← M.E_map f]
    simp
  simp only [scalarArrow, ← Category.assoc (M.E.map f), he, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply tensor_generator_ext
  intro U x s
  change (sheafMap φ (φ ≫ c n) (c n) rfl N).val.app U
    ((changeOfRingsHom φ A f).val.app U _) =
    (((M.eV A n).inv ≫ (M.V.map f).app (op n) ≫ (M.eV N n).hom).val.app U)
      ((sheafMap φ (φ ≫ c n) (c n) rfl A).val.app U _)
  erw [map_tensorSection φ A f U s x,
    sheafMap_tmul φ (φ ≫ c n) (c n) rfl N U s (f.val.app U x),
    sheafMap_tmul φ (φ ≫ c n) (c n) rfl A U s x]
  exact (M.V_map f n U x ((c n).hom.app U s)).symm

omit [EssentiallySmall.{u} C] in
private theorem scalarArrow_transition {φ : R ⟶ S} {c : ∀ n, S ⟶ B n}
    {b : ∀ n, B (n + 1) ⟶ B n} (M : ScalarTowerTensorModel φ c b)
    (hc : ∀ n, c (n + 1) ≫ b n = c n)
    (A : ringedSiteModules.{u} (𝓡 R)) (n : ℕ) :
    scalarArrow M A (n + 1) ≫ (M.V.obj A).map (homOfLE (Nat.le_succ n)).op =
      scalarArrow M A n := by
  apply (cancel_epi (M.eE A).inv).1
  apply (cancel_mono (M.eV A n).hom).1
  simp only [scalarArrow, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]
  apply tensor_generator_ext
  intro U x s
  change (((M.eV A (n + 1)).inv ≫ (M.V.obj A).map
      (homOfLE (Nat.le_succ n)).op ≫ (M.eV A n).hom).val.app U)
      ((sheafMap φ (φ ≫ c (n + 1)) (c (n + 1)) rfl A).val.app U _) = _
  erw [sheafMap_tmul, M.transition]
  change tensorSection (φ ≫ c n) A U _ x =
    (sheafMap φ (φ ≫ c n) (c n) rfl A).val.app U _
  erw [sheafMap_tmul]
  have hh := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) (hc n)) s
  rw [show (b n).hom.app U ((c (n + 1)).hom.app U s) = (c n).hom.app U s from hh]


omit [EssentiallySmall.{u} C] in
private theorem augment_eval
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    {X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} (𝓡 S)) ℤ}
    {P : CochainComplex (ringedSiteModules.{u} (𝓡 S)) ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (n : ℕ) : roosAugment γ hγ ≫ roosEval X n = γ n := by
  ext k : 1
  obtain ⟨i, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (roosAugment γ hγ ≫ roosEval X n).f (i + 1) = (γ n).f (i + 1)
  simp only [HomologicalComplex.comp_f, roosEval_f, reassoc_of% roosAugment_χ,
    biprod.lift_snd_assoc]
  rw [← HomologicalComplex.comp_f, Pi.lift_π]

omit [EssentiallySmall.{u} C] in
private theorem augment_naturality
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} (𝓡 S)) ℤ}
    {P Q : CochainComplex (ringedSiteModules.{u} (𝓡 S)) ℤ}
    (f : X ⟶ Y) (a : P ⟶ Q)
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (δ : ∀ n : ℕ, Q ⟶ Y.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (hδ : ∀ n, δ (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = δ n)
    (h : ∀ n, a ≫ δ n = γ n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) :
    a ≫ roosAugment δ hδ = roosAugment γ hγ ≫ roosF.map f := by
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (a ≫ roosAugment δ hδ).f (p + 1) =
    (roosAugment γ hγ ≫ roosF.map f).f (p + 1)
  apply (cancel_mono (roosχ Y p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc, roosAugment_χ, roosF_map_χ]
  rw [← Category.assoc, roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, roosPmap, Pi.map_π, Pi.lift_π_assoc]
    exact h n

omit [EssentiallySmall.{u} C] in
private theorem scalarAugmentation_existsUnique
    {φ : R ⟶ S} {c : ∀ n, S ⟶ B n} {b : ∀ n, B (n + 1) ⟶ B n}
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    (M : ScalarTowerTensorModel φ c b) (hc : ∀ n, c (n + 1) ≫ b n = c n) :
    ∃! β : M.F ⟶ M.G, M.AugmentationCoordinates β := by
  let γ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) (n : ℕ) :
      M.F.obj P ⟶ ((M.V.mapHomologicalComplex (.up ℤ)).obj P).asFunctor.obj (op n) :=
    { f := fun i ↦ scalarArrow M (P.X i) n
      comm' := fun i j hij ↦ (scalarArrow_naturality M (P.d i j) n).symm }
  have hγ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) (n : ℕ) :
      γ P (n + 1) ≫ ((M.V.mapHomologicalComplex (.up ℤ)).obj P).asFunctor.map
        (homOfLE (Nat.le_succ n)).op = γ P n := by
    ext i : 1
    exact scalarArrow_transition M hc (P.X i) n
  let β : M.F ⟶ M.G :=
    { app := fun P ↦ roosAugment (γ P) (hγ P)
      naturality := by
        intro P Q f
        apply augment_naturality
        intro n
        ext i : 1
        exact scalarArrow_naturality M (f.f i) n }
  have hb : M.AugmentationCoordinates β := by
    constructor
    · intro P i
      exact (roosAugment_χ (γ P) (hγ P) i |> congrArg (fun f ↦ f ≫ biprod.fst)).trans
        (by simp)
    · intro P i n U x s
      change (((M.eE (P.X i)).inv ≫
        (roosAugment (γ P) (hγ P) ≫ roosEval _ n).f i ≫
        (M.eV (P.X i) n).hom).val.app U) _ = _
      rw [augment_eval]
      change (((M.eE (P.X i)).inv ≫ scalarArrow M (P.X i) n ≫
        (M.eV (P.X i) n).hom).val.app U) _ = _
      simp only [scalarArrow, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
      exact sheafMap_tmul φ (φ ≫ c n) (c n) rfl (P.X i) U s x
  refine ⟨β, hb, ?_⟩
  intro β' hb'
  apply NatTrans.ext
  funext P
  ext k : 1
  obtain ⟨i, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  let X := (M.V.mapHomologicalComplex (.up ℤ)).obj P
  apply (cancel_mono (roosχ X i).hom).1
  apply biprod.hom_ext
  · exact (hb'.1 P i).trans (hb.1 P i).symm
  · apply (isLimitOfPreserves (HomologicalComplex.eval _ _ (i + 1))
      (limit.isLimit (Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n))))).hom_ext
    intro n
    change _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n.as).f (i + 1) =
      _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n.as).f (i + 1)
    simp only [Category.assoc, ← roosEval_f]
    apply (cancel_epi (M.eE (P.X (i + 1))).inv).1
    apply (cancel_mono (M.eV (P.X (i + 1)) n.as).hom).1
    apply tensor_generator_ext
    intro U x s
    exact (hb'.2 P (i + 1) n.as U x s).trans (hb.2 P (i + 1) n.as U x s).symm


omit [EssentiallySmall.{u} C] in
private theorem tensorLevel_naturality {φ : R ⟶ S} {c : ∀ n, S ⟶ B n}
    {b : ∀ n, B (n + 1) ⟶ B n} (M : ScalarTowerTensorModel φ c b)
    {A N : ringedSiteModules.{u} (𝓡 R)} (f : A ⟶ N) (n : ℕ) :
    (M.V.map f).app (op n) ≫ (M.eV N n).hom =
      (M.eV A n).hom ≫
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map (c n))).map
          (changeOfRingsHom (φ ≫ c n) A f) := by
  apply (cancel_epi (M.eV A n).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply restricted_tensor_ext (φ ≫ c n) (c n) A
  intro U s x
  exact (M.V_map f n U x s).trans
    (map_tensorSection (φ ≫ c n) A f U s x).symm

private theorem tensorTower_preserves {φ : R ⟶ S} {c : ∀ n, S ⟶ B n}
    {b : ∀ n, B (n + 1) ⟶ B n} (M : ScalarTowerTensorModel φ c b)
    (hres : ∀ n (K L : CochainComplex (ringedSiteModules.{u} (𝓡(B n))) ℤ) (f : K ⟶ L),
      QuasiIso (((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (c n))).mapHomologicalComplex
          (.up ℤ)).map f) ↔ QuasiIso f)
    {P Q : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ} (f : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) : QuasiIso ((M.V.mapHomologicalComplex (.up ℤ)).map f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  let := HasDerivedCategory.standard (ringedSiteModules.{u} (𝓡 R))
  let := HasDerivedCategory.standard (ringedSiteModules.{u} (𝓡 (B n.unop)))
  obtain ⟨D⟩ := nonempty_derivedChangeOfRingsCochainModel (φ ≫ c n.unop)
  let res := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map (c n.unop))
  let e (A : ringedSiteModules.{u} (𝓡 R)) : (M.V.obj A).obj n ≅ res.obj (D.E.obj A) :=
    M.eV A n.unop ≪≫ res.mapIso (eqToIso (D.obj_eq A)).symm
  have he {A N : ringedSiteModules.{u} (𝓡 R)} (g : A ⟶ N) :
      (M.V.map g).app n ≫ (e N).hom = (e A).hom ≫ res.map (D.E.map g) := by
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, tensorLevel_naturality M g n.unop]
    simp [res, D.map_eq, eqToIso, Functor.map_comp, Category.assoc]
  let eP (K : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) :
      ((M.V.mapHomologicalComplex (.up ℤ)).obj K).asFunctor.obj n ≅
        (res.mapHomologicalComplex (.up ℤ)).obj ((D.E.mapHomologicalComplex (.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ e (K.X i))
      (fun i j hij ↦ (he (K.d i j)).symm)
  have hq := (hres n.unop _ _ ((D.E.mapHomologicalComplex (.up ℤ)).map f)).2
    (D.preserves f hP hQ hf)
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (eP P) (eP Q) ?_)).2 hq
  ext i : 1
  exact (he (f.f i)).symm


private theorem roos_map_quasiIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] :
    QuasiIso (roosF.map f) := by
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n)))
        (G := Discrete.functor (fun n : ℕ ↦ Y.asFunctor.obj (op n)))
        (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n.as))).app n) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp hf (op n.as)
  have hp : QuasiIso (roosPmap f) := HomologicalComplex.quasiIso_limMap _
  let τ := CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
    (roosPmap f) (roosPmap f) (roosU_natural f)
  have hc : IsIso (DerivedCategory.Q.map (roosConeFunctor.map f)) :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished (roosU X))
      (DerivedCategory.mappingCone_triangle_distinguished (roosU Y))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
  have : QuasiIso (roosConeFunctor.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  change QuasiIso ((roosConeFunctor.map f)⟦(-1 : ℤ)⟧')
  infer_instance


omit [EssentiallySmall.{u} C] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] in
private theorem exactProducts
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    (h : exactFunctor _ _ (Pi.functor ℕ : (ℕ → ringedSiteModules.{u} (𝓡 S)) ⥤ _)) :
    HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u} (𝓡 S)) := by
  let A := ringedSiteModules.{u} (𝓡 S)
  let e := piEquivalenceFunctorDiscrete ℕ A
  let : PreservesFiniteColimits (Pi.functor ℕ : (ℕ → A) ⥤ A) := (exactFunctor_iff _).mp h |>.2
  let : PreservesFiniteColimits (e.functor ⋙ lim) :=
    preservesFiniteColimits_of_natIso (piEquivalenceFunctorDiscreteCompLim (C := A) ℕ).symm
  have : PreservesFiniteColimits (e.inverse ⋙ (e.functor ⋙ lim)) := inferInstance
  exact ⟨preservesFiniteColimits_of_natIso
    ((Functor.associator e.inverse e.functor lim).symm ≪≫
      Functor.isoWhiskerRight e.counitIso lim ≪≫ Functor.leftUnitor lim)⟩

private theorem derivedPairOfHomotopyFunctor
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]
    (F : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{u} (𝓡 S)) ℤ)
    (H : HomotopyCategory (ringedSiteModules.{u} (𝓡 R)) (.up ℤ) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S)))
    (j : HomotopyCategory.quotient _ (.up ℤ) ⋙ H ≅ F ⋙ DerivedCategory.Q)
    (hinv : ∀ {P Q : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ}
      (f : P ⟶ Q), P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
        QuasiIso f → QuasiIso (F.map f)) :
    ∃ (L : DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S)))
      (ε : DerivedCategory.Q ⋙ L ⟶ F ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
      Nonempty ((Functor.RightExtension.mk L ε).IsPointwiseRightKanExtension) ∧
      ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
        P.IsKFlatIndependentCoefficients → IsIso (ε.app P) := by
  classical
  let A := ringedSiteModules.{u} (𝓡 R)
  let D := DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, K.IsKFlatIndependentCoefficients ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X), X' ∈ P ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hH : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → W s → IsIso (H.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have := hinv f hK hL hf
    have he : H.map (q.map f) = j.hom.app K ≫
        DerivedCategory.Q.map (F.map f) ≫ j.inv.app L := by
      have hn := j.hom.naturality f
      dsimp only [Functor.comp_map] at hn
      rw [← Category.assoc, ← hn]
      simp
      rfl
    rw [he]
    infer_instance
  obtain ⟨_, hright, _, _, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hwitness := Functor.resolvingClass_essentialConstancy W H P hres hH
  have hpw : H.HasPointwiseLeftDerivedFunctor W := by
    intro X
    obtain ⟨Y, v, hc, hr, _⟩ := hwitness X
    have hb := leftDerived_defined_pointwiseKan_bridge W Q H X Y hc v hr
    exact (H.hasPointwiseLeftDerivedFunctorAt_iff Q W X).2 hb.1
  let : H.HasPointwiseLeftDerivedFunctor W := hpw
  let L := H.totalLeftDerived Q W
  let ε := H.totalLeftDerivedCounit Q W
  have hε := Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor L ε W
  have hcomp : ∀ X : HomotopyCategory A (.up ℤ), X ∈ P → IsIso (ε.app X) := by
    intro X hX
    obtain ⟨Y, v, hc, hr, hv⟩ := hwitness X
    obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
      leftDerived_defined_pointwiseKan_bridge W Q H X Y hc v hr
    let hcanonical := hε (Q.obj X)
    let e := hcanonical.conePointUniqueUpToIso hπ
    have hid : W (𝟙 X) := W.id_mem X
    have : IsIso (v.app (⟨Over.mk (𝟙 X), hid⟩ : W.Over ⊤ X)) := hv hid hX
    have : IsIso (π.app (StructuredArrow.mk (𝟙 (Q.obj X)))) := by
      rw [hidentity hid]
      infer_instance
    have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
      (StructuredArrow.mk (𝟙 (Q.obj X)))
    have he' : e.hom ≫ π.app (StructuredArrow.mk (𝟙 (Q.obj X))) = ε.app X := by
      simpa [Functor.RightExtension.coneAt] using he
    rw [← he']
    infer_instance
  let α := (Functor.associator q Q L).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q Q H L ε hε
  let i := DerivedCategory.quotientCompQhIso A
  let δ := Functor.whiskerRight i.inv L ≫ α ≫ j.hom
  have hδ := pointwise_change_iso L i j α hα
  refine ⟨L, δ, ⟨hδ.isRightKanExtension⟩, ⟨hδ⟩, ?_⟩
  intro K hK
  have := hcomp (q.obj K) ⟨K, hK, rfl⟩
  dsimp [δ, α]
  infer_instance


private theorem derivedDescent_of_pairs
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]
    {φ : R ⟶ S} {c : ∀ n, S ⟶ B n} {b : ∀ n, B (n + 1) ⟶ B n}
    (M : ScalarTowerTensorModel φ c b) (β : M.F ⟶ M.G)
    (LF LG : DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S)))
    (εF : DerivedCategory.Q ⋙ LF ⟶ M.F ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ M.G ⋙ DerivedCategory.Q)
    (hF : LF.IsLeftDerivedFunctor εF (HomologicalComplex.quasiIso _ (.up ℤ)))
    (hG : LG.IsLeftDerivedFunctor εG (HomologicalComplex.quasiIso _ (.up ℤ)))
    (hpF : (Functor.RightExtension.mk LF εF).IsPointwiseRightKanExtension)
    (hpG : (Functor.RightExtension.mk LG εG).IsPointwiseRightKanExtension)
    (hcF : ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
      P.IsKFlatIndependentCoefficients → IsIso (εF.app P))
    (hcG : ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
      P.IsKFlatIndependentCoefficients → IsIso (εG.app P)) : M.DerivedDescent β := by
  let : LF.IsLeftDerivedFunctor εF (HomologicalComplex.quasiIso _ (.up ℤ)) := hF
  let : LG.IsLeftDerivedFunctor εG (HomologicalComplex.quasiIso _ (.up ℤ)) := hG
  let τ := Functor.whiskerRight β DerivedCategory.Q
  let χ := Functor.leftDerivedNatTrans LF LG εF εG
    (HomologicalComplex.quasiIso _ (.up ℤ)) τ
  have hχ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) :
      χ.app (DerivedCategory.Q.obj P) ≫ εG.app P =
        εF.app P ≫ DerivedCategory.Q.map (β.app P) :=
    Functor.leftDerivedNatTrans_app LF LG εF εG _ τ P
  refine ⟨LF, LG, εF, εG, hF, hG, (fun X ↦ ⟨hpF X⟩), (fun X ↦ ⟨hpG X⟩),
    (fun P hP _ ↦ ⟨hcF P hP, hcG P hP⟩), χ, hχ, ?_⟩
  intro χ' hχ'
  apply Functor.leftDerived_ext LG εG (HomologicalComplex.quasiIso _ (.up ℤ)) LF
  ext X
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
  have : QuasiIso q := hq
  have : IsIso (εG.app P) := hcG P hP
  have hflat' : ∀ i, IsFlatOnSite (P.X i) := fun i ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hflat i)
  have he : χ'.app (DerivedCategory.Q.obj P) = χ.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono (εG.app P)).1
    exact (hχ' P hP hflat').trans (hχ P).symm
  have hX : χ'.app (DerivedCategory.Q.obj X) = χ.app (DerivedCategory.Q.obj X) := by
    apply (cancel_epi (LF.map (DerivedCategory.Q.map q))).1
    rw [χ'.naturality, χ.naturality, he]
  exact congrArg (fun f ↦ f ≫ εG.app X) hX


/-- The canonical scalar augmentation exists uniquely and descends to universal derived
functors, independently of flat-term K-flat representatives.

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks 03EK, 014E, 08TC, 06YS, 06YT, 06XN and 05S9.
(blueprint: lem-pur-quotient-scalar-comparison-descent)

Proof plan:
1. The balanced maps send p tensor s to p tensor c_n(s), and sheafify (03EK).
   Strict compatibility gives a map alpha to the product killed by 1 minus shift.
2. In the fixed roosχ coordinates use (0, alpha), as in roosAugment. The cone
   differential proves it is a chain map. Pure tensors and product projections give
   naturality and uniqueness, without any surjectivity of c_n.
3. Tensor preserves chain homotopies. The strict Roos homotopy functor sends the
   compatible tensor homotopies to (-h_V, h_V), so both functors pass to K(R).
4. Use the flat-term K-flat resolutions of 06YS. Quasi-isomorphisms in K(R) have
   saturated right fractions by lem-pur-quasi-isos-saturated-triangulated.
5. Apply lem-pur-change-of-rings-kflat-quasi-iso to R to S and each R to B_n.
   Restriction changes no underlying abelian sheaf and preserves quasi-isomorphisms.
6. Exact countable products commute with cohomology, so the product map is a
   quasi-isomorphism. It commutes with 1 minus shift by the strict tower equations.
7. Reorder Roos coordinates and apply lem-pe-roos-coordinates-quasi-iso with
   endomorphism minus (1 minus shift). Thus G preserves these quasi-isomorphisms.
8. Apply resolvingClass_essentialConstancy, leftDerived_defined_pointwiseKan_bridge,
   then the total-left-derived-localization theorem. The identity legs are invertible
   on flat-term K-flat complexes. The cochain version is the same universal extension:
   target localization identifies homotopic maps, so it factors through K(R).
9. The right Kan universal property descends εF followed by beta to χ on all D(R),
   with χ followed by εG equal to εF followed by Q(beta).
10. For any resolution q:P to X, Q(q) is invertible. Naturality forces the value at X
    from the normalized value at P. Hence the normalization determines χ uniquely,
    independently of the resolution and of comparison-preserving derived models.
11. For S=R the multiplication isomorphism sends p tensor r to rp; its inverse
    sends p to p tensor 1. The quotient specialization is stated below.
-/
theorem quotient_scalar_comparison_descent
    (φ : R ⟶ S) (c : ∀ n, S ⟶ B n) (b : ∀ n, B (n + 1) ⟶ B n)
    (hc : ∀ n, c (n + 1) ≫ b n = c n)
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]
    (hexact : exactFunctor _ _
      (Pi.functor ℕ : (ℕ → ringedSiteModules.{u} (𝓡 S)) ⥤ _)) :
    ∃ M : ScalarTowerTensorModel φ c b,
      (∃! β : M.F ⟶ M.G, M.AugmentationCoordinates β) ∧
      ∀ β : M.F ⟶ M.G, M.AugmentationCoordinates β → M.DerivedDescent β := by
  classical
  obtain ⟨D⟩ := nonempty_derivedChangeOfRingsCochainModel φ
  obtain ⟨V, e, hV, ht, hmap, hhom, hshift, hres, hlin⟩ :=
    exists_compatibleCoefficientTower.{uC, vC, u, 0} (fun n ↦ φ ≫ c n) c b
      (fun n ↦ by rw [Category.assoc, hc n]) hc
  let M : ScalarTowerTensorModel φ c b :=
    { E := D.E
      V := V
      E_add := D.additive
      V_add := hV
      eE := fun A ↦ eqToIso (D.obj_eq A)
      eV := e
      E_map := by
        intro A N f
        simp [eqToIso, D.map_eq, Category.assoc]
      V_map := fun {A N} f ↦ hmap A N f
      transition := fun A n ↦ (ht A n).1 }
  refine ⟨M, scalarAugmentation_existsUnique M hc, ?_⟩
  intro β hβ
  have _ := hβ
  let A := ringedSiteModules.{u} (𝓡 R)
  let T := ringedSiteModules.{u} (𝓡 S)
  let : HasExactLimitsOfShape (Discrete ℕ) T := exactProducts hexact
  obtain ⟨_, _, RF, hRF, hfac, _⟩ := roosF_homotopy_functor.{_, _, 0} (A := T)
  let : RF.Additive := hRF
  let H := V.mapHomotopyCategory (.up ℤ) ⋙ RF ⋙ DerivedCategory.Qh (C := T)
  let qR := HomotopyCategory.quotient A (.up ℤ)
  let qT := HomotopyCategory.quotient (ℕᵒᵖ ⥤ T) (.up ℤ)
  let qS := HomotopyCategory.quotient T (.up ℤ)
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let j : qR ⋙ H ≅ M.G ⋙ DerivedCategory.Q :=
    (Functor.associator qR (V.mapHomotopyCategory (.up ℤ))
      (RF ⋙ DerivedCategory.Qh)).symm ≪≫
    Functor.isoWhiskerRight (V.mapHomotopyCategoryFactors (.up ℤ))
      (RF ⋙ DerivedCategory.Qh) ≪≫
    Functor.associator Vc qT (RF ⋙ DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft Vc
      ((Functor.associator qT RF DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (eqToIso hfac) DerivedCategory.Qh ≪≫
        Functor.associator roosF qS DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft roosF (DerivedCategory.quotientCompQhIso T)) ≪≫
    (Functor.associator Vc roosF DerivedCategory.Q).symm
  have hG : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
        QuasiIso f → QuasiIso (M.G.map f) := by
    intro P Q f hP hQ hf
    have := tensorTower_preserves M hres f hP hQ hf
    exact roos_map_quasiIso ((V.mapHomologicalComplex (.up ℤ)).map f)
  obtain ⟨LG, εG, huG, ⟨hpG⟩, hcG⟩ := derivedPairOfHomotopyFunctor M.G H j hG
  have huF := D.universal
  let : D.T.IsLeftDerivedFunctor D.ε (HomologicalComplex.quasiIso _ (.up ℤ)) := huF
  let : (M.F ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso _ (.up ℤ)) := D.pointwise
  have hpF := Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
    D.T D.ε (HomologicalComplex.quasiIso _ (.up ℤ))
  exact derivedDescent_of_pairs M β D.T LG D.ε εG huF huG hpF hpG D.computes hcG


/-- Multiplication identifies the scalar augmentation with the strict quotient unit.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks 03EK and 08TC (blueprint: lem-pur-quotient-scalar-comparison-descent).

Proof: specialize the scalar formula to the identity of R and the canonical
projections R to R/a^(n+1). Multiplication on sheafified tensors sends p tensor r
to rp, with inverse p to p tensor 1. It commutes with restrictions and differentials.
After precomposing beta with this inverse, every product projection sends p to
p tensor 1 and the shifted-product component is zero. Product extensionality and
the fixed Roos coordinates identify the map with roosAugment of that compatible
family. This includes a=0, when the tower is constant R, and invertible a, when
all positive quotient levels vanish. This is Step 11 of the node's proof. -/
theorem quotient_scalar_comparison_unit
    [HasSheafify J CommRingCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (a : (R.obj ⋙ CategoryTheory.forget CommRingCat.{u}).sections)
    (b : ∀ n : ℕ, principalPowerRingQuotient R a ((n + 1) + 1) ⟶
      principalPowerRingQuotient R a (n + 1))
    (hc : ∀ n : ℕ, principalPowerRingProjection R a ((n + 1) + 1) ≫ b n =
      principalPowerRingProjection R a (n + 1))
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 R))]
    (M : ScalarTowerTensorModel (𝟙 R)
      (fun n : ℕ ↦ principalPowerRingProjection R a (n + 1)) b)
    (β : M.F ⟶ M.G) (hβ : M.AugmentationCoordinates β)
    (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) :
    ∃ m : M.F.obj P ≅ P,
      (∀ (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (r : R.obj.obj U),
        (((M.eE (P.X i)).inv ≫ m.hom.f i).val.app U)
          ((toSheafify J (changeOfRingsPresheaf (𝟙 R) (P.X i)).presheaf).app U
            (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) = r • x) ∧
      ∃ (γ : ∀ n : ℕ, P ⟶
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).asFunctor.obj (op n))
        (hγ : ∀ n : ℕ, γ (n + 1) ≫
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).asFunctor.map
            (homOfLE (Nat.le_succ n)).op = γ n),
        (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U),
          (((γ n).f i ≫ (M.eV (P.X i) n).hom).val.app U) x =
            (toSheafify J
              (changeOfRingsPresheaf (𝟙 R ≫ principalPowerRingProjection R a (n + 1))
                (P.X i)).presheaf).app U
              ((1 : (principalPowerRingQuotient R a (n + 1)).obj.obj U)
                ⊗ₜ[R.obj.obj U, ((𝟙 R ≫ principalPowerRingProjection R a (n + 1)).hom.app U).hom]
                  x)) ∧
        m.inv ≫ β.app P = roosAugment γ hγ := by
  have _ := hc
  have _ := (inferInstance : EssentiallySmall.{u} C)
  let m : M.F.obj P ≅ P := HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ M.eE (P.X i) ≪≫ scalarIdIso (P.X i)) (by
      intro i j hij
      change (M.eE (P.X i)).hom ≫ (scalarIdIso (P.X i)).hom ≫ P.d i j =
        M.E.map (P.d i j) ≫ (M.eE (P.X j)).hom ≫ (scalarIdIso (P.X j)).hom
      have hm := M.E_map (P.d i j)
      have hm' : M.E.map (P.d i j) ≫ (M.eE (P.X j)).hom =
          (M.eE (P.X i)).hom ≫ changeOfRingsHom (𝟙 R) (P.X i) (P.d i j) := by
        rw [← hm]
        simp
      rw [← Category.assoc (M.E.map _) _ _, hm']
      rw [Category.assoc, scalarIdIso_naturality])
  have hm (i : ℤ) : (M.eE (P.X i)).inv ≫ m.hom.f i =
      (scalarIdIso (P.X i)).hom := by simp [m]
  refine ⟨m, ?_, ?_⟩
  · intro i U x r
    rw [hm]
    exact scalarIdIso_tmul _ _ _ _
  · let X := (M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
    let γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n) :=
      fun n ↦ m.inv ≫ β.app P ≫ roosEval X n
    have hgen (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) :
        (((γ n).f i ≫ (M.eV (P.X i) n).hom).val.app U) x =
          (toSheafify J
            (changeOfRingsPresheaf (𝟙 R ≫ principalPowerRingProjection R a (n + 1))
              (P.X i)).presheaf).app U
            ((1 : (principalPowerRingQuotient R a (n + 1)).obj.obj U)
              ⊗ₜ[R.obj.obj U,
                ((𝟙 R ≫ principalPowerRingProjection R a (n + 1)).hom.app U).hom] x) := by
      have hb := hβ.2 P i n U x 1
      have he : m.inv.f i = (scalarIdIso (P.X i)).inv ≫ (M.eE (P.X i)).inv := by
        simp [m]
      dsimp only [γ]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [he]
      have hi := scalarIdIso_inv_unit (P.X i) U x
      change (((M.eE (P.X i)).inv ≫
        (β.app P ≫ roosEval X n).f i ≫ (M.eV (P.X i) n).hom).val.app U)
          (((scalarIdIso (P.X i)).inv).val.app U x) = _
      rw [hi]
      (convert hb using 1; simp only [map_one])
    have hγ : ∀ n : ℕ, γ (n + 1) ≫
        X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n := by
      intro n
      ext i : 1
      simp only [HomologicalComplex.comp_f]
      apply (cancel_mono (M.eV (P.X i) n).hom).1
      ext U x
      have h1 := hgen (n + 1) i U x
      have h0 := hgen n i U x
      have ht := M.transition (P.X i) n U x 1
      have hinv := congrArg (fun z ↦ ((M.eV (P.X i) (n + 1)).inv).val.app U z) h1
      simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
        ← SheafOfModules.comp_val, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] at hinv
      have hh := congrArg (fun z ↦
        (((M.V.obj (P.X i)).map (homOfLE (Nat.le_succ n)).op ≫
          (M.eV (P.X i) n).hom).val.app U) z) hinv
      rw [map_one] at ht
      dsimp only [X, HomologicalComplex.asFunctor, Functor.mapHomologicalComplex]
      exact (hh.trans ht).trans h0.symm
    refine ⟨γ, hγ, hgen, ?_⟩
    ext k : 1
    obtain ⟨i, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change (m.inv ≫ β.app P).f (i + 1) = (roosAugment γ hγ).f (i + 1)
    apply (cancel_mono (roosχ X i).hom).1
    apply biprod.hom_ext
    · simp only [HomologicalComplex.comp_f, Category.assoc, roosAugment_χ,
        biprod.lift_fst]
      simpa only [X, Category.assoc, comp_zero] using
        congrArg (fun f ↦ m.inv.f (i + 1) ≫ f) (hβ.1 P i)
    · simp only [roosAugment_χ, biprod.lift_snd]
      apply (isLimitOfPreserves (HomologicalComplex.eval _ _ (i + 1))
        (limit.isLimit (Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n))))).hom_ext
      intro n
      change _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n.as).f (i + 1) =
        _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n.as).f (i + 1)
      simp only [Category.assoc, ← roosEval_f]
      change (γ n.as).f (i + 1) = ((Pi.lift γ) ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n.as).f (i + 1)
      rw [Pi.lift_π]


end SheafOfModules
