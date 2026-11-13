/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.FlatRingedIdealCompleteEquivalence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: Basic

The constant and completed coefficient sheaves and the kernel-ideal completeness predicate.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940.
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The constant ring sheaf (Stacks, Tag 099L). -/
abbrev constant : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)

/-- The finite coefficient sheaf at exponent n+1 (Stacks, Tag 099L). -/
abbrev finite (n : ℕ) : Sheaf J CommRingCat.{u} :=
  constant J (A ⧸ I ^ (n + 1))

/-- The quotient map of constant ring sheaves (Stacks, Tag 099L). -/
def quotient (n : ℕ) : constant J A ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The finite quotient transition (Stacks, Tag 099L). -/
def transition (n : ℕ) : finite J A I (n + 1) ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- The actual inverse sequence of finite constant ring sheaves (Stacks, Tag 099L). -/
def finiteSystem : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u} :=
  Functor.ofOpSequence (transition J A I)

/-- The sheafwise completion, as the limit of the specified sequence (Stacks, Tag 093M). -/
def completed : Sheaf J CommRingCat.{u} := limit (finiteSystem J A I)

/-- The canonical finite projection (Stacks, Tag 093M). -/
def projection (n : ℕ) : completed J A I ⟶ finite J A I n :=
  limit.π (finiteSystem J A I) (op n)

/-- Quotient maps form a cone (Stacks, Tag 093M). -/
theorem quotient_step (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (constant J A)).map (homOfLE (Nat.le_succ n)).op ≫
        quotient J A I n =
      quotient J A I (n + 1) ≫ (finiteSystem J A I).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map, finiteSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  change _ = (constantSheaf J CommRingCat).map _ ≫ (constantSheaf J CommRingCat).map _
  rw [← Functor.map_comp]
  congr 1

/-- The quotient cone, using the actual quotient maps (Stacks, Tag 093M). -/
def quotientCone : Cone (finiteSystem J A I) where
  pt := constant J A
  π := NatTrans.ofOpSequence (quotient J A I) (quotient_step J A I)

/-- The canonical map from constant to completed coefficients (Stacks, Tag 093M). -/
def coefficientMap : constant J A ⟶ completed J A I :=
  limit.lift _ (quotientCone J A I)

attribute [local irreducible] completed

variable {J A I}

/-- The existing category of module sheaves, with commutativity forgotten (Stacks, Tag 099L). -/
abbrev Mod (O : Sheaf J CommRingCat.{u}) := ringedSiteModules.{u} (siteModuleRings O)

/-- Cochain complexes of these module sheaves (Stacks, Tag 099L). -/
abbrev Cx (O : Sheaf J CommRingCat.{u}) := CochainComplex (Mod O) ℤ

/-- The standard derived localization, rather than an additional size hypothesis (Stacks, Tag 099L).
-/
abbrev D (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (Mod O) _ _ (HasDerivedCategory.standard _)

/-- The standard localization functor (Stacks, Tag 099L). -/
abbrev Q (O : Sheaf J CommRingCat.{u}) : Cx O ⥤ D O :=
  @DerivedCategory.Q (Mod O) _ _ (HasDerivedCategory.standard _)

/-- Ordinary restriction of scalars, exactly Mathlib's functor (Stacks, Tag 099I). -/
abbrev res {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : Mod B ⥤ Mod R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Exact derived restriction of scalars (Stacks, Tag 099I). -/
def dres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : D B ⥤ D R :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  siteDerivedRestrictScalars φ

/-- Constant global sections supplied by the sheafification unit (Stacks, Tag 093M). -/
def constantSection (a : A) : ((constant J A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a,
    fun f ↦ ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).naturality f) a |>.symm⟩

/-- Images of constant sections in a coefficient algebra (Stacks, Tag 093M). -/
def algebraSection {O : Sheaf J CommRingCat.{u}} (φ : constant J A ⟶ O) (a : A) :
    (O.obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ φ.hom.app U ((constantSection (J := J) a).val U),
    fun f ↦ (ConcreteCategory.congr_hom (φ.hom.naturality f) _).symm.trans
      (congrArg (φ.hom.app _) ((constantSection (J := J) a).property f))⟩

/-- The kernel of a ring-sheaf map is a genuine ideal subsheaf with these sections
(Stacks, Tag 093M). -/
theorem kernelIdeal_existsUnique {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) :
    ∃! K : RingedSiteIdeal O,
      ∀ U : C, K.sections U = RingHom.ker (q.hom.app (op U)).hom := by
  let K : RingedSiteIdeal O :=
    { sections := fun U ↦ RingHom.ker (q.hom.app (op U)).hom
      restriction := by
        intro U V g a ha
        change q.hom.app (op V) (O.obj.map g.op a) = 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [h, ha, map_zero]
      local_mem := by
        intro U a T hT ha
        change q.hom.app (op U) a = 0
        have hS : Presieve.IsSheaf J (S.obj ⋙ forget CommRingCat) :=
          (isSheaf_iff_isSheaf_of_type J _).mp
            ((sheafCompose J (forget CommRingCat)).obj S).property
        apply (hS.isSeparated T hT).ext
        intro V g hg
        change S.obj.map g.op (q.hom.app (op U) a) = S.obj.map g.op 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [← h, map_zero]
        exact ha V g hg }
  refine ⟨K, fun _ ↦ rfl, ?_⟩
  intro L hL
  have h : L.sections = K.sections := funext hL
  have hext (M N : RingedSiteIdeal O) (h : M.sections = N.sections) : M = N := by
    cases M
    cases N
    dsimp only at h
    cases h
    rfl
  exact hext L K h

/-- The specified kernel ideal subsheaf, selected by its unique sections formula (Stacks, Tag 093M).
-/
def kernelIdeal {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) : RingedSiteIdeal O :=
  (kernelIdeal_existsUnique q).exists.choose

/-- The existing local internal-Hom completeness predicate, at the standard localization
(Stacks, Tags 0999 and 099I). -/
def IsComplete {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) (M : D O) : Prop :=
  @IsLocallyDerivedRingedIdealComplete C _ J O
    (HasDerivedCategory.standard _)
    (fun _ ↦ HasDerivedCategory.standard _)
    (kernelIdeal q).module (kernelIdeal q).inclusion M

end CategoryTheory.ConstantCompletion
