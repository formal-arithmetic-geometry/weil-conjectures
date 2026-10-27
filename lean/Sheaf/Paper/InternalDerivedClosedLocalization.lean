/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Sheaf.Paper.NativeDerivedRestrictionData
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.Paper.InternalSectionMonoidalNormalization
import Sheaf.Paper.ProEtaleDerivedRestrictionClosed
import Sheaf.Paper.ScalarPerfectFiniteFree
import all Sheaf.CategoryTheory.RingedSitePerfectDuality
import Mathlib.LinearAlgebra.Dimension.Free
import all Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses

/-! # Closed derived transport and covering localization

Source: blueprint main-20261015, det-lem-int-tensor-product.proof.md, first paragraph;
Stacks Project, Tags 08JB, 08JH and 08JJ.
(blueprint: lem-sfb-internal-derived-closed-localization).

The native tensor is the existing uncompleted K-flat tensor. The target closed
structure is tied to its K-flat representatives by `TensorComparison` and
`CoefficientTensorModels`. All comparison equations refer to actual evaluation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [instance 50000] HasDerivedCategory.ofIsGrothendieckAbelian
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open WeilConjectures AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

namespace AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization

section Closed
variable {C : Type a} [Category.{b} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The native tensor-Hom counit, with Hom in the first tensor slot.
Source: Stacks 08J9 (blueprint: lem-sfb-internal-derived-closed-localization). -/
def evaluation (M N : C) : (ihom M).obj N ⊗ M ⟶ N :=
  (β_ _ _).hom ≫ (ihom.ev M).app N

/-- Right-slot transposition for the actual closed adjunction, using Koszul exchange.
Source: Stacks 08J9 (blueprint: lem-sfb-internal-derived-closed-localization). -/
def transpose (V M N : C) (f : V ⊗ M ⟶ N) : V ⟶ (ihom M).obj N :=
  MonoidalClosed.curry ((β_ M V).hom ≫ f)

/-- The canonical u_N: associate, evaluate, apply the unit, and transpose.
Source: blueprint first paragraph; Stacks 08JJ
(blueprint: lem-sfb-internal-derived-closed-localization). -/
def evaluationTranspose (M N : C) :
    N ⊗ (ihom M).obj (𝟙_ C) ⟶ (ihom M).obj N :=
  transpose _ M N ((α_ _ _ _).hom ≫
    N ◁ evaluation M (𝟙_ C) ≫ (ρ_ N).hom)

variable {D : Type c} [Category.{d} D] [MonoidalCategory D]
  [BraidedCategory D] [MonoidalClosed D]

/-- Comparison of duals, using the existing evaluation mate and the unit comparison.
Source: Stacks 08JB, 08JJ (blueprint: lem-sfb-internal-derived-closed-localization). -/
def dualComparison (F : C ⥤ D) [F.Monoidal] (M : C) :
    F.obj ((ihom M).obj (𝟙_ C)) ⟶ (ihom (F.obj M)).obj (𝟙_ D) :=
  (Functor.LaxMonoidal.ihomComparison F M).natTrans.app (𝟙_ C) ≫
    (ihom (F.obj M)).map (Functor.Monoidal.εIso F).inv

end Closed

/-- Agreement of the strong tensor comparison with the specified representative comparison.
Source: Stacks 06YU (blueprint: lem-sfb-internal-derived-closed-localization). -/
def TensorTransport
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (t : Functor.uncurry.obj (curriedTensor C) ⋙ F ≅ (F.prod F) ⋙ S.tensor) : Prop :=
  ∀ M N : C, (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m M N).inv =
    t.hom.app (M, N)

/-- The tensor comparison carries the actual source braiding to the target symmetry.
Source: Stacks 06YU (blueprint: lem-sfb-internal-derived-closed-localization). -/
def SymmetricTransport
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (s : @SymmetricCategory D _ S.monoidal) : Prop :=
  ∀ M N : C,
    (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m M N).hom ≫
        F.map (β_ M N).hom =
      (s.braiding _ _).hom ≫
        (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m N M).hom

/-- Sectionwise u_N for the specified K-injective Hom and K-flat tensor models.
Source: Stacks 08JJ (blueprint: lem-sfb-internal-derived-closed-localization). -/
def sectionEvaluationTranspose {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) (M N : D) :
    S.tensor.obj (N, H.obj (op M, S.monoidal.tensorUnit)) ⟶ H.obj (op M, N) :=
  S.transpose _ M N
    ((S.monoidal.associator _ _ _).hom ≫
      S.tensor.map
        (X := (N, S.tensor.obj (H.obj (op M, S.monoidal.tensorUnit), M)))
        (Y := (N, S.monoidal.tensorUnit))
        (𝟙 N, S.evaluation M S.monoidal.tensorUnit) ≫
      (S.monoidal.rightUnitor N).hom)

/-- The actual dual comparison induced by a sectionwise Hom comparison.
Source: Stacks 08J9, 08JJ (blueprint: lem-sfb-internal-derived-closed-localization). -/
def sectionDualComparison
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (unit : S.monoidal.tensorUnit ≅ F.obj (𝟙_ C))
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅
      (F.op.prod F) ⋙ H) (M : C) :
    F.obj ((ihom M).obj (𝟙_ C)) ⟶ H.obj (op (F.obj M), S.monoidal.tensorUnit) :=
  θ.hom.app (op M, 𝟙_ C) ≫ H.map (𝟙 (op (F.obj M)), unit.inv)

/-- Exact preservation of counits, adjunction transposes, and the canonical u_N.
The tensor and unit maps are those of the specified strong monoidal functor.
Source: Stacks 08J9, 08JJ (blueprint: lem-sfb-internal-derived-closed-localization). -/
def ClosedTransport
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C]
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅
      (F.op.prod F) ⋙ H) : Prop :=
  (∀ M N : C,
    F.map (evaluation M N) = ((@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m) _ _).inv ≫
      S.tensor.map
        (X := (F.obj ((ihom M).obj N), F.obj M))
        (Y := (H.obj (op (F.obj M), F.obj N), F.obj M))
        (θ.hom.app (op M, N), 𝟙 (F.obj M)) ≫ S.evaluation (F.obj M) (F.obj N)) ∧
  (∀ (V M N : C) (f : V ⊗ M ⟶ N),
    F.map (transpose V M N f) ≫ θ.hom.app (op M, N) =
      S.transpose _ _ _
        ((@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m V M).hom ≫ F.map f)) ∧
  (∀ M N : C,
    F.map (evaluationTranspose M N) ≫ θ.hom.app (op M, N) =
      ((@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m) N ((ihom M).obj (𝟙_ C))).inv ≫
        S.tensor.map
          (X := (F.obj N, F.obj ((ihom M).obj (𝟙_ C))))
          (Y := (F.obj N, H.obj (op (F.obj M), S.monoidal.tensorUnit)))
          (𝟙 (F.obj N), sectionDualComparison S F
            (@Functor.CoreMonoidal.εIso C _ _ D _ S.monoidal F m) θ M) ≫
        sectionEvaluationTranspose S (F.obj M) (F.obj N))



/-- Canonical closed comparison for a specified strong monoidal restriction functor.
Source: Stacks 08JB (blueprint: lem-sfb-internal-derived-closed-localization). -/
def RestrictionClosedTransport
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] (F : C ⥤ D) [F.Monoidal] : Prop :=
  (∀ M N : C, IsIso ((Functor.LaxMonoidal.ihomComparison F M).natTrans.app N)) ∧
  (∀ (V M N : C) (f : V ⊗ M ⟶ N),
    F.map (transpose V M N f) ≫
      (Functor.LaxMonoidal.ihomComparison F M).natTrans.app N =
    transpose _ _ _ (Functor.LaxMonoidal.μ F V M ≫ F.map f)) ∧
  (∀ M N : C,
    F.map (evaluationTranspose M N) ≫
      (Functor.LaxMonoidal.ihomComparison F M).natTrans.app N =
    Functor.OplaxMonoidal.δ F N ((ihom M).obj (𝟙_ C)) ≫
      (𝟙 (F.obj N) ⊗ₘ dualComparison F M) ≫
      evaluationTranspose (F.obj M) (F.obj N))

/-- Recover the functor from its existing monoidal structure, retaining its fixed instances.
Source: Stacks 06YU (blueprint: lem-sfb-internal-derived-closed-localization). -/
def monoidalUnderlying
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    {F : C ⥤ D} (_m : F.Monoidal) : C ⥤ D := F

/-- Reuse the strong monoidal structure without resynthesizing its underlying tensor data.
Source: Stacks 06YU (blueprint: lem-sfb-internal-derived-closed-localization). -/
instance monoidalUnderlyingMonoidal
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    {F : C ⥤ D} (m : F.Monoidal) : (monoidalUnderlying m).Monoidal := m

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})

/-- Each covering chart, as an object of the small pro-etale site.
Source: Stacks 098K (blueprint: lem-sfb-internal-derived-closed-localization). -/
def coverObject (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) (i : 𝒰.I₀) :
    X.ProEt :=
  letI : WeaklyEtale (𝒰.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀) ⟨i⟩
  Scheme.ProEt.mk (𝒰.f i)

/-- The canonical K-flat derived restriction, with its endpoints fixed explicitly.
Source: Stacks 08JB (blueprint: lem-sfb-internal-derived-closed-localization). -/
abbrev derivedRestriction {Y : Scheme.{u}} (f : Y ⟶ X) :=
  (CondensedRing.nativeDerivedRestrictionData Λ f).functor

/-- The existing canonical tensorator and unit make derived restriction monoidal.
Source: Stacks 06YU (blueprint: lem-sfb-internal-derived-closed-localization). -/
instance restrictionMonoidal {Y : Scheme.{u}} (f : Y ⟶ X) :
    (derivedRestriction Λ X f).Monoidal :=
  (CondensedRing.nativeDerivedRestrictionData Λ f).monoidal

/-- Covering localization for the canonical derived inverse-image functor.
Its tensorator is the K-flat comparison in Derived.Monoidal; its Hom comparison
is the existing adjunction mate, rather than a chosen isomorphism.
Source: Stacks 08JB (blueprint: lem-sfb-internal-derived-closed-localization). -/
def CoveringLocalization (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) : Prop :=
  (∀ i : 𝒰.I₀, exactFunctor _ _ (CondensedRing.upperStar Λ.X (𝒰.f i))) ∧
  (∀ i : 𝒰.I₀, RestrictionClosedTransport
    (derivedRestriction Λ X (𝒰.f i))) ∧
  (∀ (M N : DerivedCategory (Internal Λ.X X)) (f : M ⟶ N),
    IsIso f ↔ ∀ i : 𝒰.I₀,
      IsIso ((derivedRestriction Λ X (𝒰.f i)).map f))


set_option backward.isDefEq.respectTransparency false in
/-- Compatible scalar maps on the base, whose restrictions supply the chart maps.
Source: blueprint first paragraph; Stacks 03CY
(blueprint: lem-sfb-internal-derived-closed-localization). -/
def ScalarMap (A : Type (u + 1)) [CommRing A] :=
  @Quiver.Hom (Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) inferInstance
    (SheafOfModules.scalarPerfectRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) A)
    (ring Λ.X X)

/-- The scalar local-model hypothesis, using literal slice restriction and ordinary
termwise extension of the constant scalar complex. Bounds are chosen inside each chart.
Source: blueprint first paragraph; Stacks 08JH
(blueprint: lem-sfb-internal-derived-closed-localization). -/
def HasScalarCoverModels (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    (A : Type (u + 1)) [CommRing A]
    (φ : ScalarMap Λ X A)
    (M : DerivedCategory (Internal Λ.X X)) : Prop :=
  ∀ i : 𝒰.I₀, ∃ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (∃ l h : ℤ, ∀ n : ℤ, n < l ∨ h < n → IsZero (P.X n)) ∧
    (∀ n : ℤ, Module.Free A (P.X n) ∧ Module.Finite A (P.X n)) ∧
    Nonempty ((ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
      (Scheme.ProEt.topology X) (ring Λ.X X) (coverObject X 𝒰 i)).obj
        ((forward Λ.X X).obj M) ≅
      DerivedCategory.Q.obj (SheafOfModules.scalarPerfectChartComplex
        (Scheme.ProEt.topology X) A φ (coverObject X 𝒰 i) P))


/-- Every scalar finite-free covering model has invertible native evaluation transpose.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-internal-derived-closed-localization). -/
def ScalarCoverConclusion (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A]
    (φ : ScalarMap Λ X A)
    (M : DerivedCategory (Internal Λ.X X)),
    HasScalarCoverModels Λ X 𝒰 A φ M →
    ∀ N : DerivedCategory (Internal Λ.X X), IsIso (evaluationTranspose M N)

set_option backward.isDefEq.respectTransparency false

section
variable {C : Type a} [Category.{b} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
private theorem untranspose_transpose
    (hβ : ∀ M N : C, (β_ M N).hom ≫ (β_ N M).hom = 𝟙 _) (V M N : C) (f : V ⊗ M ⟶ N) :
    transpose V M N f ▷ M ≫
      AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M N = f := by
  unfold transpose AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation
  rw [BraidedCategory.braiding_naturality_left_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rw [← Category.assoc, hβ, Category.id_comp]

private theorem comparison_transpose
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅ (F.op.prod F) ⋙ H)
    (hβ : ∀ M N : C, (β_ M N).hom ≫ (β_ N M).hom = 𝟙 _)
    (he : ∀ M N : C,
      F.map (AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M N) =
        (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m _ _).inv ≫
        S.tensor.map (X := (F.obj ((ihom M).obj N), F.obj M))
          (Y := (H.obj (op (F.obj M), F.obj N), F.obj M))
          (θ.hom.app (op M, N), 𝟙 (F.obj M)) ≫
          S.evaluation (F.obj M) (F.obj N))
    (V M N : C) (f : V ⊗ M ⟶ N) :
    F.map (transpose V M N f) ≫ θ.hom.app (op M, N) =
      S.transpose _ _ _
        ((@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m V M).hom ≫ F.map f) := by
  let := S.monoidal
  let := m.toMonoidal
  apply (S.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change ((S.adjunction (F.obj M)).homEquiv _ _).symm _ = _
  rw [Adjunction.homEquiv_symm_apply]
  change (F.map (transpose V M N f) ≫ θ.hom.app (op M, N)) ▷ F.obj M ≫
    S.evaluation (F.obj M) (F.obj N) = _
  rw [comp_whiskerRight, Category.assoc]
  have hev := he M N
  have hh : θ.hom.app (op M, N) ▷ F.obj M ≫
      S.evaluation (F.obj M) (F.obj N) =
      (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m _ _).hom ≫
        F.map (AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M N) := by
    rw [hev, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    simp only [CoefficientClosedStructure.tensor, CategoryTheory.MonoidalCategory.tensor,
      tensorHom_id]
  rw [hh]
  change F.map (transpose V M N f) ▷ F.obj M ≫
    Functor.LaxMonoidal.μ F _ _ ≫ F.map _ = Functor.LaxMonoidal.μ F _ _ ≫ _
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp]
  rw [untranspose_transpose hβ]

private theorem comparison_u
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅ (F.op.prod F) ⋙ H)
    (hβ : ∀ M N : C, (β_ M N).hom ≫ (β_ N M).hom = 𝟙 _)
    (he : ∀ M N : C,
      F.map (AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M N) =
        (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m _ _).inv ≫
        S.tensor.map (X := (F.obj ((ihom M).obj N), F.obj M))
          (Y := (H.obj (op (F.obj M), F.obj N), F.obj M))
          (θ.hom.app (op M, N), 𝟙 (F.obj M)) ≫
          S.evaluation (F.obj M) (F.obj N)) (M N : C) :
    F.map (evaluationTranspose M N) ≫ θ.hom.app (op M, N) =
      (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m N ((ihom M).obj (𝟙_ C))).inv ≫
        S.tensor.map (X := (F.obj N, F.obj ((ihom M).obj (𝟙_ C))))
          (Y := (F.obj N, H.obj (op (F.obj M), S.monoidal.tensorUnit)))
          (𝟙 (F.obj N), sectionDualComparison S F
            (@Functor.CoreMonoidal.εIso C _ _ D _ S.monoidal F m) θ M) ≫
        sectionEvaluationTranspose S (F.obj M) (F.obj N) := by
  let := S.monoidal
  let := m.toMonoidal
  unfold evaluationTranspose
  rw [comparison_transpose S F m θ hβ he]
  apply (S.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = ((S.adjunction (F.obj M)).homEquiv _ _).symm _
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_naturality_left_symm]
  change _ = _ ≫ _ ≫ ((S.adjunction (F.obj M)).homEquiv _ _).symm
    ((S.adjunction (F.obj M)).homEquiv _ _ _)
  rw [Equiv.symm_apply_apply]
  simp only [sectionDualComparison, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor, id_tensorHom]
  change Functor.LaxMonoidal.μ F _ _ ≫ F.map _ =
    Functor.OplaxMonoidal.δ F N _ ▷ F.obj M ≫
      (F.obj N ◁ (θ.hom.app (op M, 𝟙_ C) ≫
        H.map (X := (op (F.obj M), F.obj (𝟙_ C)))
          (Y := (op (F.obj M), 𝟙_ D))
          (𝟙 (op (F.obj M)), Functor.OplaxMonoidal.η F))) ▷ F.obj M ≫
      (α_ _ _ _).hom ≫ F.obj N ◁ S.evaluation (F.obj M) (𝟙_ D) ≫ (ρ_ _).hom
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc]
  have hn := (S.adjunction (F.obj M)).counit.naturality
    (Functor.OplaxMonoidal.η F)
  change H.map (X := (op (F.obj M), F.obj (𝟙_ C)))
      (Y := (op (F.obj M), 𝟙_ D)) (𝟙 _, Functor.OplaxMonoidal.η F) ▷ F.obj M ≫
      S.evaluation _ _ = S.evaluation _ _ ≫ Functor.OplaxMonoidal.η F at hn
  have hd : (θ.hom.app (op M, 𝟙_ C) ≫
      H.map (X := (op (F.obj M), F.obj (𝟙_ C)))
          (Y := (op (F.obj M), 𝟙_ D))
          (𝟙 (op (F.obj M)), Functor.OplaxMonoidal.η F)) ▷ F.obj M ≫
      S.evaluation (F.obj M) (𝟙_ D) =
      Functor.LaxMonoidal.μ F _ _ ≫
        F.map (AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M
          (𝟙_ C)) ≫ Functor.OplaxMonoidal.η F := by
    rw [comp_whiskerRight, Category.assoc, hn]
    rw [he]
    simp only [Category.assoc]
    change _ = (m.μIso _ _).hom ≫ (m.μIso _ _).inv ≫ _
    rw [Iso.hom_inv_id_assoc]
    simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor, tensorHom_id]
  rw [hd]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [Functor.Monoidal.map_associator]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.Monoidal.map_rightUnitor]
  change (m.μIso _ _).hom ≫ (m.μIso _ _).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rfl

private theorem closed_transport
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D)
    (m : @Functor.CoreMonoidal C _ _ D _ S.monoidal F)
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅ (F.op.prod F) ⋙ H)
    (hβ : ∀ M N : C, (β_ M N).hom ≫ (β_ N M).hom = 𝟙 _)
    (he : ∀ M N : C,
      F.map (AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.evaluation M N) =
        (@Functor.CoreMonoidal.μIso C _ _ D _ S.monoidal F m _ _).inv ≫
        S.tensor.map (X := (F.obj ((ihom M).obj N), F.obj M))
          (Y := (H.obj (op (F.obj M), F.obj N), F.obj M))
          (θ.hom.app (op M, N), 𝟙 (F.obj M)) ≫
          S.evaluation (F.obj M) (F.obj N)) :
    ClosedTransport S F m θ := by
  exact ⟨he, comparison_transpose S F m θ hβ he, comparison_u S F m θ hβ he⟩

end

section
universe aa bb cc dd
variable {C : Type aa} [Category.{bb} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
    {D : Type cc} [Category.{dd} D] [MonoidalCategory D]
  [BraidedCategory D] [MonoidalClosed D]

private theorem native_uncurry_injective {V M N : D}
    {f g : V ⟶ (ihom M).obj N}
    (h : f ▷ M ≫ evaluation M N = g ▷ M ≫ evaluation M N) : f = g := by
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (β_ V M).hom).1
  simpa only [MonoidalClosed.uncurry_eq,
    ← BraidedCategory.braiding_naturality_left_assoc, evaluation, Category.assoc] using h

private theorem transpose_precomp {V W M N : D} (q : V ⟶ W) (f : W ⊗ M ⟶ N) :
    q ≫ transpose W M N f = transpose V M N (q ▷ M ≫ f) := by
  unfold transpose
  rw [← MonoidalClosed.curry_natural_left]
  rw [BraidedCategory.braiding_naturality_right_assoc]

private theorem restriction_transport (F : C ⥤ D) [F.Monoidal]
    (hb : ∀ M N, Functor.LaxMonoidal.μ F M N ≫ F.map (β_ M N).hom =
      (β_ (F.obj M) (F.obj N)).hom ≫ Functor.LaxMonoidal.μ F N M)
    (h : ∀ M N, IsIso ((Functor.LaxMonoidal.ihomComparison F M).natTrans.app N)) :
    RestrictionClosedTransport F := by
  let : F.Braided := { toMonoidal := inferInstance, braided := hb }
  have ht (V M N : C) (f : V ⊗ M ⟶ N) :
      F.map (transpose V M N f) ≫
        (Functor.LaxMonoidal.ihomComparison F M).natTrans.app N =
      transpose _ _ _ (Functor.LaxMonoidal.μ F V M ≫ F.map f) := by
    apply MonoidalClosed.uncurry_injective
    unfold transpose
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
      Functor.LaxMonoidal.ihomComparison_ev, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp, MonoidalClosed.whiskerLeft_curry_ihom_ev_app,
      MonoidalClosed.uncurry_curry]
    rw [Functor.map_comp, ← Category.assoc, Functor.Braided.braided]
    rw [Category.assoc]
  have he (M N : C) :
      (Functor.LaxMonoidal.ihomComparison F M).natTrans.app N ▷ F.obj M ≫
        evaluation (F.obj M) (F.obj N) =
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (evaluation M N) := by
    unfold evaluation
    rw [reassoc_of% (BraidedCategory.braiding_naturality_left
      ((Functor.LaxMonoidal.ihomComparison F M).natTrans.app N) (F.obj M)),
      Functor.LaxMonoidal.ihomComparison_ev]
    rw [Functor.map_comp, ← Category.assoc, ← Functor.Braided.braided, Category.assoc]
  refine ⟨h, ht, ?_⟩
  intro M N
  unfold evaluationTranspose
  rw [ht]
  rw [transpose_precomp, transpose_precomp]
  congr 1
  simp only [id_tensorHom]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc]
  have hn : (ihom (F.obj M)).map (Functor.OplaxMonoidal.η F) ▷ F.obj M ≫
      evaluation (F.obj M) (𝟙_ D) =
      evaluation (F.obj M) (F.obj (𝟙_ C)) ≫ Functor.OplaxMonoidal.η F := by
    unfold evaluation
    rw [BraidedCategory.braiding_naturality_left_assoc]
    have hnat := (ihom.ev (F.obj M)).naturality (Functor.OplaxMonoidal.η F)
    change F.obj M ◁ (ihom (F.obj M)).map _ ≫ (ihom.ev (F.obj M)).app _ =
      (ihom.ev (F.obj M)).app _ ≫ Functor.OplaxMonoidal.η F at hnat
    simpa only [Category.assoc] using congrArg ((β_ _ _).hom ≫ ·) hnat
  have hd : dualComparison F M ▷ F.obj M ≫ evaluation (F.obj M) (𝟙_ D) =
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (evaluation M (𝟙_ C)) ≫
        Functor.OplaxMonoidal.η F := by
    unfold dualComparison
    rw [comp_whiskerRight, Category.assoc]
    change _ ≫ ((ihom (F.obj M)).map (Functor.OplaxMonoidal.η F) ▷ F.obj M ≫ _) = _
    rw [hn, ← Category.assoc, he, Category.assoc]
  rw [hd]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [Functor.Monoidal.map_associator]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.map_rightUnitor]
  simp only [Functor.Monoidal.μ_δ_assoc]
end

private theorem scalar_package (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (φ : ScalarMap Λ X A) (U : X.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hf : ∀ n, Module.Free A (P.X n) ∧ Module.Finite A (P.X n)) :
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite.{u + 1, u, u + 1}
      (((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ.X X)).over U)
      (SheafOfModules.scalarPerfectChartComplex.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) A φ U P)) := by
  classical
  have term (n : ℤ) : ∃ k : ℕ,
      Nonempty ((SheafOfModules.scalarPerfectChartFunctor.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) A φ U).obj (P.X n) ≅
          ∏ᶜ fun _ : Fin k ↦ SheafOfModules.unit.{u, u + 1, u + 1}
            (((sheafCompose (Scheme.ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ.X X)).over U)) := by
    have := (hf n).1
    have := (hf n).2
    obtain hA | hA := subsingleton_or_nontrivial A
    · let : Subsingleton (P.X n) := Module.subsingleton A (P.X n)
      let b : P.X n ≃ₗ[A] (Fin 0 → A) := LinearEquiv.ofSubsingleton _ _
      obtain ⟨e, _⟩ := SheafOfModules.exists_scalarPerfectChartFiniteFreeIso
        (Scheme.ProEt.topology X) A φ U 0
      exact ⟨0, ⟨(SheafOfModules.scalarPerfectChartFunctor.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) A φ U).mapIso b.toModuleIso ≪≫ e⟩⟩
    let b := Module.finBasis A (P.X n)
    obtain ⟨e, _⟩ := SheafOfModules.exists_scalarPerfectChartFiniteFreeIso
      (Scheme.ProEt.topology X) A φ U (Module.finrank A (P.X n))
    exact ⟨_, ⟨(SheafOfModules.scalarPerfectChartFunctor.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) A φ U).mapIso b.equivFun.toModuleIso ≪≫ e⟩⟩
  choose k e using term
  exact ⟨{ N := k
           i := fun n ↦ (e n).some.hom
           p := fun n ↦ (e n).some.inv
           splitting := fun n ↦ (e n).some.hom_inv_id }⟩

section
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (O : D) (uO : S.monoidal.tensorUnit ≅ O)
    (P N : D)
private theorem unit_evaluation : S.tensor.map (𝟙 N, H.map (𝟙 (op P), uO.hom)) ≫
    ringedSiteDualEvaluation S O uO P N = sectionEvaluationTranspose S P N := by
  let := S.monoidal
  apply (S.transpose _ P N).symm.injective
  unfold ringedSiteDualEvaluation sectionEvaluationTranspose
  change ((S.adjunction P).homEquiv _ _).symm (_ ≫
    ((S.adjunction P).homEquiv _ _) _) =
    ((S.adjunction P).homEquiv _ _).symm (((S.adjunction P).homEquiv _ _) _)
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor, id_tensorHom]
  change (N ◁ H.map (𝟙 (op P), uO.hom)) ▷ P ≫
    (α_ _ _ _).hom ≫ N ◁ S.evaluation P O ≫ N ◁ uO.inv ≫ (ρ_ N).hom =
    (α_ _ _ _).hom ≫ N ◁ S.evaluation P (𝟙_ D) ≫ (ρ_ N).hom
  rw [MonoidalCategory.associator_naturality_middle_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hn := (S.adjunction P).counit.naturality uO.hom
  change H.map (𝟙 (op P), uO.hom) ▷ P ≫ S.evaluation P O =
    S.evaluation P (𝟙_ D) ≫ uO.hom at hn
  rw [hn]
  simp
end

private theorem cover_top (X : Scheme.{u}) (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (Scheme.ProEt.topology X).CoversTop (coverObject X 𝒰) := by
  have : ∀ i, WeaklyEtale (𝒰.f i) := fun i ↦
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀) ⟨i⟩
  intro V
  apply (Scheme.ProEt.topology X).superset_covering _
    (Scheme.ProEt.ofArrows_baseChange_mem_topology V 𝒰.f 𝒰.mem₀)
  rintro T f ⟨-, a, -, ⟨i⟩, rfl⟩
  refine ⟨i, ⟨MorphismProperty.Over.homMk (a.left ≫ pullback.snd V.hom (𝒰.f i)) ?_⟩⟩
  change (a.left ≫ pullback.snd V.hom (𝒰.f i)) ≫ 𝒰.f i = T.hom
  rw [Category.assoc, ← pullback.condition]
  exact MorphismProperty.Over.w a

private theorem local_section
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    [∀ U : C, IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))]
    (S : RingedSiteDualityModel.{u + 1, u, u, u + 1} J R)
    {ι : Type v} (Y : ι → C) (hY : J.CoversTop Y)
    (P N : DerivedCategory (SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (hmodels : ∀ i : ι, ∃ E : CochainComplex (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (Y i))) ℤ,
      (∃ l h : ℤ, ∀ n, n < l ∨ h < n → IsZero (E.X n)) ∧
      Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) ∧
      Nonempty ((ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        J R (Y i)).obj P ≅ DerivedCategory.Q.obj E)) :
    IsIso (sectionEvaluationTranspose S.closed P N) := by
  classical
  obtain ⟨MU⟩ : Nonempty (∀ U : C,
      RingedSiteDualityModel.{u + 1, u, u, u + 1} (J.over U) (R.over U)) :=
    ⟨fun U ↦ (ringedSiteDualityMaps_exists.{u + 1, u, u, u + 1}
      (J.over U) (R.over U)).some⟩
  obtain ⟨d⟩ : Nonempty (∀ U : C,
      RestrictionData.{u + 1, u, u, u + 1, u + 1} J R U S (MU U)) :=
    ⟨fun U ↦ (restrictionData_nonempty.{u + 1, u, u, u + 1, u + 1}
      J R U S (MU U)).some⟩
  let F (U : C) := (d U).F
  have e (U : C) : DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.localizedSystemRestriction.{u + 1, u, u} R U).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
    (d U).e ≪≫ Functor.isoWhiskerRight
      (restrictionComplexIso.{u + 1, u, u, u + 1} J R U) DerivedCategory.Q
  have hlocal (i : ι) :
      IsIso ((F (Y i)).map (ringedSiteDualEvaluation S.closed
        (ringedSiteDualityUnit.{u + 1, u, u, u + 1} J R) S.unitIso
        P N)) := by
    let U := Y i
    let r := ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1} J R U
    let q : F U ≅ r := Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
      ((e U) ≪≫ (ringedSliceLocalizationIso.{u + 1, u, u, u + 1, u + 1} J R U).symm)
    obtain ⟨E, hb, ⟨pE⟩, ⟨p⟩⟩ := hmodels i
    have hp := evaluation_transport_source (MU U).closed
      (ringedSiteDualityUnit.{u + 1, u, u, u + 1} (J.over U) (R.over U))
      (MU U).unitIso (q.app _ ≪≫ p) ((F U).obj N)
      (strict_evaluation.{u + 1, u, u, u + 1} (J.over U) (R.over U)
        (MU U) E hb pE ((F U).obj N))
    exact (d U).evaluation_isIso _ N hp
  have hi : IsIso (ringedSiteDualEvaluation S.closed
      (ringedSiteDualityUnit.{u + 1, u, u, u + 1} J R) S.unitIso P N) :=
    derived_iso_local.{u + 1, u, u, u + 1, u + 1} J R F e Y hY _ hlocal
  rw [← unit_evaluation S.closed _ S.unitIso]
  have := hi
  exact IsIso.comp_isIso' (S.closed.tensor.mapIso ((Iso.refl N).prod
    ((derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J R).mapIso
      ((Iso.refl _).prod S.unitIso)))).isIso_hom hi

-- Inlining the instance avoids expanding the chart functor during conversion.
set_option linter.style.haveILetI false in
private theorem scalar_section (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    (S : RingedSiteDualityModel.{u + 1, u, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ.X X))
    (A : Type (u + 1)) [CommRing A] (φ : ScalarMap Λ X A)
    (M : DerivedCategory (Internal Λ.X X))
    (hM : HasScalarCoverModels Λ X 𝒰 A φ M)
    (N : DerivedCategory (Modules Λ.X X)) :
    IsIso (sectionEvaluationTranspose S.closed ((forward Λ.X X).obj M) N) := by
  classical
  let J := Scheme.ProEt.topology X
  let R := ring Λ.X X
  let : HasSheafify J CommRingCat.{u + 1} :=
    inferInstanceAs (HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  let (U : X.ProEt) : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) := by
    exact sectionModulesGrothendieck (J.over U) (R.over U)
  apply local_section J R S (coverObject X 𝒰) (cover_top X 𝒰)
  intro i
  let U := coverObject X 𝒰 i
  obtain ⟨P, hb, hf, hp⟩ := hM i
  have hC := SheafOfModules.scalarPerfectConstantFunctor_additive J A
  have hE := SheafOfModules.scalarPerfectExtensionFunctor_additive (J.over U)
    ((J.overPullback CommRingCat.{u + 1} U).map φ)
  letI := CategoryTheory.module_overFunctor_preservesZero
    (SheafOfModules.scalarPerfectRingUnderlying.{u + 1, u, u + 1} J
      (SheafOfModules.scalarPerfectRing.{u + 1, u, u + 1} J A)) U
  have : (SheafOfModules.scalarPerfectChartFunctor.{u + 1, u, u + 1}
      J A φ U).PreservesZeroMorphisms :=
    inferInstanceAs ((SheafOfModules.scalarPerfectConstantFunctor J A ⋙
      SheafOfModules.overFunctor _ U ⋙
      SheafOfModules.scalarPerfectExtensionFunctor.{u + 1, u, u + 1} (J.over U)
        ((J.overPullback CommRingCat.{u + 1} U).map φ)).PreservesZeroMorphisms)
  have hb' : ∃ l h : ℤ, ∀ n, n < l ∨ h < n →
      IsZero ((SheafOfModules.scalarPerfectChartComplex.{u + 1, u, u + 1} J A φ U P).X n) := by
    obtain ⟨l, h, hb⟩ := hb
    exact ⟨l, h, fun n hn ↦
      (SheafOfModules.scalarPerfectChartFunctor.{u + 1, u, u + 1} J A φ U).map_isZero (hb n hn)⟩
  obtain ⟨pE⟩ := scalar_package Λ X A φ U P hf
  exact ⟨_, hb', ⟨pE⟩, hp⟩


private theorem reflects_u
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D) [F.ReflectsIsomorphisms]
    (m : @Functor.CoreMonoidal _ _ _ _ _ S.monoidal F)
    (θ : Functor.uncurry.obj MonoidalClosed.internalHom ⋙ F ≅ (F.op.prod F) ⋙ H)
    (hc : ClosedTransport S F m θ)
    (M N : C) [IsIso (sectionEvaluationTranspose S (F.obj M) (F.obj N))] :
    IsIso (evaluationTranspose M N) := by
  let := S.monoidal
  have hu := hc.2.2 M N
  have hd : IsIso (sectionDualComparison S F m.εIso θ M) := by
    unfold sectionDualComparison
    infer_instance
  have hc : IsIso (F.map (evaluationTranspose M N) ≫ θ.hom.app (op M, N)) := by
    rw [hu]
    infer_instance
  have hm : IsIso (F.map (evaluationTranspose M N)) :=
    IsIso.of_isIso_comp_right _ (θ.hom.app (op M, N))
  exact isIso_of_reflects_iso _ F

private theorem symmetry_of_comparison
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type c} [Category.{d} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (F : C ⥤ D) [F.Faithful]
    (m : @Functor.CoreMonoidal _ _ _ _ _ S.monoidal F)
    (s : @SymmetricCategory D _ S.monoidal)
    (hs : SymmetricTransport S F m s) (M N : C) :
    (β_ M N).hom ≫ (β_ N M).hom = 𝟙 _ := by
  let := S.monoidal
  apply F.map_injective
  rw [Functor.map_comp, CategoryTheory.Functor.map_id]
  apply (cancel_epi (m.μIso M N).hom).1
  rw [← Category.assoc, hs M N, Category.assoc, hs N M,
    ← Category.assoc, s.symmetry, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency true

-- Prevent conversion from expanding geometric pullback while comparing native instances.
attribute [local irreducible] internalBraiding CondensedRing.monoidal_leftDerivedUpperStar
  CondensedRing.nativeDerivedRestrictionData CondensedRing.dataOfMonoidal
  AlgebraicGeometry.ProEtale.upperStar AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftAdjoint

-- Inlining keeps both occurrences of the specified monoidal field identical.
set_option linter.style.haveILetI false in
private theorem restriction_for_arrow
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    [IsIso (condensedPullbackHom Λ.X f)] :
    RestrictionClosedTransport (derivedRestriction Λ X f) := by
  set_option backward.isDefEq.respectTransparency false in
    have h := CondensedRing.proetale_derived_restriction_closed Λ f
    dsimp only at h
    change @RestrictionClosedTransport _ _ _ _ _ _ _ _ _ _
      (CondensedRing.nativeDerivedRestrictionData Λ f).functor
      (CondensedRing.nativeDerivedRestrictionData Λ f).monoidal
    generalize CondensedRing.nativeDerivedRestrictionData Λ f = d at h ⊢
    letI := d.monoidal
    exact restriction_transport d.functor h.2 h.1

/-- The exact section-action equivalence identifies the native uncompleted derived
closed symmetric tensor, its actual evaluation and transposition, and covering
restriction. Locally bounded scalar finite-free models make the global u_N invertible.

Source: main-20261015, det-lem-int-tensor-product.proof.md, first paragraph;
Stacks 08JB, 08JH, 08JJ (blueprint: lem-sfb-internal-derived-closed-localization).

Proof plan, following the six steps of the node:
1. Apply lem-pe-internal-section-tensor-comparison to the pulled-back ring object.
   Its exact section equivalence and pure-tensor comparisons descend along K-flat
   representatives. Use lem-sfb-module-object-ringed-site-derived-comparison for
   the K-injective Hom model, its evaluation equation and its slice normalization.
   Coherence follows on K-flat representatives from the ordinary symmetric
   monoidal coherence. Transposition follows by the counit characterization.
2. Resolve each fixed argument by a flat-term K-flat complex (lem-pc-kflat-resolution).
   Lem-weil-pbc-kflat-fixed-tensor-triangulated supplies triangles and shifts;
   exact derived factorization transports them through the section equivalence.
3. Expand u_N as the transpose of associate, evaluate, and apply the right unit.
   Step 1 carries each actual map, hence its transpose, to the sectionwise map.
4. Identify each chart site with the slice by weakly-etale localization. Exact
   restriction and lem-weil-pbc-ringed-slice-evaluation-transpose identify the
   tensor, Hom, counit and transpose for arbitrary unbounded inputs. The coefficient
   isomorphism transports the action. Ringed derived monoidal comparisons identify
   the K-flat tensorator with the canonical pullback tensorator; apply to step 3.
5. Lem-zl-condensed-cover-restriction-conservative detects invertibility on the
   cover, including the empty cover of the empty scheme, without any bound.
6. On each chart substitute its scalar finite-free model. The signed comparison
   of lem-sfb-finite-free-dual-chain-comparison identifies local u_N with its
   invertible chain comparison for every unbounded N, without coefficient flatness.
   Steps 4 and 5 give the global assertion. The bounds never leave their charts. -/
theorem internal_derived_closed_localization :
    exactFunctor _ _ (equivalence Λ.X X).functor ∧
    (forward Λ.X X).IsEquivalence ∧
    (∃ (S : CoefficientClosedStructure (hom Λ.X X))
      (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ.X X) S)
      (t : TensorComparison Λ.X X S T)
      (m : @Functor.CoreMonoidal _ _ _ _ _ S.monoidal (forward Λ.X X))
      (s : @SymmetricCategory _ _ S.monoidal)
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ.X X) ⋙ forward Λ.X X ≅
        ((forward Λ.X X).op.prod (forward Λ.X X)) ⋙ hom Λ.X X),
      TensorTransport S (forward Λ.X X) m t.iso ∧
      SymmetricTransport S (forward Λ.X X) m s ∧
      ClosedTransport S (forward Λ.X X) m θ) ∧
    (∀ M : DerivedCategory (Internal Λ.X X),
      (tensorLeft M).IsTriangulated ∧ (tensorRight M).IsTriangulated) ∧
    (∀ (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
      (_hcoeff : ∀ i : 𝒰.I₀, IsIso (condensedPullbackHom Λ.X (𝒰.f i))),
      CoveringLocalization Λ X 𝒰 ∧ ScalarCoverConclusion Λ X 𝒰) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    obtain ⟨S, t, m, θ, ht, hs, he⟩ := internal_section_monoidal_normalization Λ X
    have : (forward Λ.X X).Faithful := by unfold forward; infer_instance
    have hβ := symmetry_of_comparison S.closed (forward Λ.X X) m S.symmetric hs
    have hev : ∀ M N : DerivedCategory (Internal Λ.X X),
        (forward Λ.X X).map (evaluation M N) =
          (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.closed.monoidal
            (forward Λ.X X) m _ _).inv ≫
          S.closed.tensor.map
            (X := ((forward Λ.X X).obj ((ihom M).obj N), (forward Λ.X X).obj M))
            (Y := ((hom Λ.X X).obj (op ((forward Λ.X X).obj M),
              (forward Λ.X X).obj N), (forward Λ.X X).obj M))
            (θ.hom.app (op M, N), 𝟙 _) ≫
            S.closed.evaluation ((forward Λ.X X).obj M) ((forward Λ.X X).obj N) := by
      intro M N
      rw [ht]
      exact he M N
    have hc := closed_transport S.closed (forward Λ.X X) m θ hβ hev
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    · unfold forward
      infer_instance
    · exact ⟨S.closed, S.models, t, m, S.symmetric, θ, ht, hs,
        hc⟩
    · intro M
      exact ⟨inferInstance, inferInstance⟩
    · intro 𝒰 hcoeff
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro i
        exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
      · intro i
        let : WeaklyEtale (𝒰.f i) :=
          (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀) ⟨i⟩
        let := hcoeff i
        exact restriction_for_arrow Λ (𝒰.f i)
      · intro M N f
        have h := (condensed_cover_restriction_conservative Λ X 𝒰).1 M N f
        refine h.trans ?_
        constructor <;> intro hf i
        · exact (CondensedRing.nativeDerivedRestriction_isIso_map_iff Λ (𝒰.f i) f).2 (hf i)
        · exact (CondensedRing.nativeDerivedRestriction_isIso_map_iff Λ (𝒰.f i) f).1 (hf i)
      · intro A _ φ M hM N
        have hi := scalar_section Λ X 𝒰 S A φ M hM ((forward Λ.X X).obj N)
        exact reflects_u S.closed (forward Λ.X X) m θ hc M N

end AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization
