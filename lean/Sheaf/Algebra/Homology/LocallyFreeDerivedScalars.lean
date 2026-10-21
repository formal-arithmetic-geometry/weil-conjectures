/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # Derived scalar extension of locally finite free module sheaves

Source: Stacks Project, Modules on Sites, Tags 0GN1 and 08FC; Cohomology on Sites,
Tags 06YQ and 06YY (blueprint: lem-sfb-locally-free-derived-scalars).

The ordinary functor and its universal derived comparison are those of
`DerivedChangeOfRingsCochainModel`. Its object and map equations fix ordinary extension
as sheafification of sectionwise scalar extension, with the new ring acting on the left.
The degree-zero comparison below is its counit followed by the standard single-complex
isomorphism. In particular it is not an arbitrarily selected isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wB

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

private theorem sliceEssentiallySmall (U : C) : EssentiallySmall.{r} (Over U) := by
  let : LocallySmall.{r} C := locallySmall_of_essentiallySmall C
  exact inferInstanceAs (EssentiallySmall.{r} (CostructuredArrow (𝟭 C) U))

-- Scalar extension sends the structure module to the new structure module.
-- Sectionwise this is B tensor_R R = B; sheafification then fixes the target.
open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarUnitIso
    {B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) :
    changeOfRings φ (unit (derivedChangeRingIndependentCoefficients J R)) ≅
      unit (derivedChangeRingIndependentCoefficients J B) := by
  let O := derivedChangeRingIndependentCoefficients J R
  let A := derivedChangeRingIndependentCoefficients J B
  let e (V : Cᵒᵖ) :
      (changeOfRingsPresheaf φ (unit O)).obj V ≅ (unit A).val.obj V := by
    let := (φ.hom.app V).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V)
      (B.obj.obj V) (B.obj.obj V)).toModuleIso
  let ep : changeOfRingsPresheaf φ (unit O) ≅ (unit A).val :=
    PresheafOfModules.isoMk e (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (e Y).hom (changeOfRingsMap φ (unit O) f
        ((1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x)) =
          B.obj.map f ((e X).hom
            ((1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x))
      erw [Classical.choose_spec (exists_changeOfRingsMap φ (unit O) f) 1 x, map_one]
      change (φ.hom.app Y) (R.obj.map f x) * 1 =
        B.obj.map f ((φ.hom.app X) x * 1)
      simp only [mul_one]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) x)
  exact (PresheafOfModules.sheafification.{r} (R := A) (𝟙 _)).mapIso ep ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).counit.app (unit A))

-- Scalar extension commutes with restriction to the slice. The underlying
-- presheaves have identical pure tensors, and slice sheafification supplies the iso.
open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarOverIso
    {B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] :
    (changeOfRings φ M).over U ≅
      changeOfRings ((J.overPullback CommRingCat.{r} U).map φ) (M.over U) := by
  let ψ := (J.overPullback CommRingCat.{r} U).map φ
  let A := derivedChangeRingIndependentCoefficients J B
  let P := changeOfRingsPresheaf φ M
  let ep : changeOfRingsPresheaf ψ (M.over U) ≅
      (PresheafOfModules.pushforward.{r} (F := Over.forget U) (𝟙 _)).obj P :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change changeOfRingsMap ψ (M.over U) f
        ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
          (φ.hom.app (Opposite.op X.unop.left)).hom] x) =
        changeOfRingsMap φ M ((Over.forget U).op.map f)
          ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
            (φ.hom.app (Opposite.op X.unop.left)).hom] x)
      rw [show changeOfRingsMap ψ (M.over U) f
          ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
            (φ.hom.app (Opposite.op X.unop.left)).hom] x) = _ from
          Classical.choose_spec (exists_changeOfRingsMap ψ (M.over U) f) 1 x]
      exact (Classical.choose_spec
        (exists_changeOfRingsMap φ M ((Over.forget U).op.map f)) 1 x).symm)
  have := overSheafificationMap_isIso.{u, v, r, r} A U P
  exact ((PresheafOfModules.sheafification.{r} (R := A.over U) (𝟙 _)).mapIso ep ≪≫
    asIso (overSheafificationMap.{u, v, r, r} A U P)).symm

/-- The canonical degree-zero scalar comparison, formed from the universal derived counit
and the natural isomorphism commuting an additive functor with a single complex.
Source: Stacks Project, Tag 06YY, identity K-flat resolution computation
(blueprint: lem-sfb-locally-free-derived-scalars). -/
noncomputable def locallyFreeScalarComparison
    {B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wB}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))]
    (D : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
    D.T.obj (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ⟶
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (D.E.obj M)) :=
  D.ε.app ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.E (.up ℤ) 0).hom.app M)

set_option backward.isDefEq.respectTransparency false in
/-- A module sheaf locally finite free on slice sites is flat, its single complex is
K-flat, and its canonical derived scalar comparison is invertible for every ring map.
Scalar extension preserves each local finite rank, and the comparisons commute with maps.
Source: Stacks Project, Modules on Sites, Tags 0GN1, 08FC and Section 03EK;
Cohomology on Sites, Tags 06YQ, 06YT and 06YY.

Proof:
1. Evaluate each finite-free chart at the terminal object of the slice. Evaluation
preserves finite products, so the section module is a finite power of the section
ring and is flat. Apply the algebraic equational criterion to each restricted
relation and then the independent-universe local relation criterion for site-flatness.
2. The single complex has flat terms: degree zero is M, and the remaining terms
are zero. Apply the independent-universe bounded-above flat criterion for K-flatness.
3. The cochain model's canonical counit computes derived extension on this K-flat
complex. Compose it with the single-complex isomorphism to obtain the stated comparison.
4. Sectionwise scalar extension commutes with slice restriction. The sheafification
comparison on slices promotes this to sheaves. It sends the structure module to the
new structure module by the explicit isomorphism B tensor_R R = B. On the slice, the
ordinary additive extension functor of an existing cochain model preserves finite
products. Transporting a given finite-free chart through these isomorphisms preserves
its rank, including rank zero. No flatness of the target ring is used.
5. Naturality of the counit and the single-complex isomorphism gives the displayed
square, for every target module and every module morphism.
(blueprint: lem-sfb-locally-free-derived-scalars). -/
theorem locallyFree_derived_scalars
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (hM : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧
      ∀ (U : C) (f : U ⟶ X), S f → ∃ n : ℕ,
        Nonempty (M.over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J R).over U)))) :
    IsFlatOnSite (R := R) M ∧
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ∧
    ∀ (B : Sheaf J CommRingCat.{r}) (φ : R ⟶ B)
      [HasDerivedCategory.{wR}
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
      [HasDerivedCategory.{wB}
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))]
      (D : DerivedChangeOfRingsCochainModel φ),
      IsIso (locallyFreeScalarComparison D M) ∧
      (∀ (U : C) (n : ℕ),
        Nonempty (M.over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J R).over U))) →
        Nonempty ((D.E.obj M).over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J B).over U)))) ∧
      (∀ (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
        (a : M ⟶ N),
        D.T.map (DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map a)) ≫
            locallyFreeScalarComparison D N =
          locallyFreeScalarComparison D M ≫
            DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map (D.E.map a))) := by
  have hflat : IsFlatOnSite (R := R) M := by
    classical
    apply isFlatOnSite_of_local_equationalCriterion R M
    intro X n a s hs
    obtain ⟨S, hS, h⟩ := hM X
    refine ⟨S, hS, ?_⟩
    intro U f hf
    obtain ⟨k, ⟨e⟩⟩ := h U f hf
    let O := (derivedChangeRingIndependentCoefficients J R).over U
    let ev := evaluation O (Opposite.op (Over.mk (𝟙 U)))
    let e' := ev.mapIso e ≪≫
      PreservesProduct.iso ev (fun _ : Fin k ↦ unit O) ≪≫
      ModuleCat.piIsoPi (fun _ : Fin k ↦ ev.obj (unit O))
    have : Module.Flat (R.obj.obj (Opposite.op U))
        (Fin k → ev.obj (unit O)) := by
      change Module.Flat (R.obj.obj (Opposite.op U))
        (Fin k → R.obj.obj (Opposite.op U))
      infer_instance
    have : Module.Flat (R.obj.obj (Opposite.op U)) (M.val.obj (Opposite.op U)) :=
      Module.Flat.of_linearEquiv e'.toLinearEquiv
    have heq : (∑ p : Fin n, R.obj.map f.op (a p) • M.val.map f.op (s p)) = 0 := by
      have hh := congrArg (fun z ↦ M.val.map f.op z) hs
      rw [map_sum, map_zero] at hh
      simpa only [M.val.map_smul] using! hh
    exact Module.Flat.isTrivialRelation_of_sum_smul_eq_zero heq
  have hkflat : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) := by
    apply isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [HomologicalComplex.single_obj_X_self] using hflat
    · let N := ((HomologicalComplex.single _ (.up ℤ) 0).obj M).X i
      have hN : IsZero N := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      apply isFlatOnSite_of_local_equationalCriterion R N
      intro U _n _a _s _hs
      refine ⟨⊤, J.top_mem U, ?_⟩
      intro V _f _hf
      refine ⟨0, (fun _ ↦ Fin.elim0), Fin.elim0, ?_, fun q ↦ Fin.elim0 q⟩
      intro _p
      have : Subsingleton (N.val.obj (Opposite.op V)) :=
        ModuleCat.subsingleton_of_isZero
          ((evaluation (derivedChangeRingIndependentCoefficients J R)
            (Opposite.op V)).map_isZero hN)
      exact @Subsingleton.elim (N.val.obj (Opposite.op V)) this _ _
  refine ⟨hflat, hkflat, ?_⟩
  intro B φ _ _ D
  have : IsIso (D.ε.app ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) :=
    D.computes _ hkflat
  refine ⟨?_, ?_, ?_⟩
  · unfold locallyFreeScalarComparison
    infer_instance
  · intro U n hfree
    obtain ⟨e⟩ := hfree
    let : EssentiallySmall.{r} (Over U) := sliceEssentiallySmall U
    let : (J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
      inferInstance
    obtain ⟨hS, hW⟩ : HasSheafify (J.over U) AddCommGrpCat.{r} ∧
        (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r} :=
      coefficientSheafification.{max u v, v, r} (J.over U)
    let := hS
    let := hW
    let O := (derivedChangeRingIndependentCoefficients J R).over U
    let ψ := (J.overPullback CommRingCat.{r} U).map φ
    let := HasDerivedCategory.standard
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients.{r, max u v, v}
        (J.over U) ((J.overPullback CommRingCat.{r} U).obj R)))
    let := HasDerivedCategory.standard
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients.{r, max u v, v}
        (J.over U) ((J.overPullback CommRingCat.{r} U).obj B)))
    obtain ⟨D'⟩ := nonempty_derivedChangeOfRingsCochainModel.{max u v, v, r,
      max (r + 1) u v, max (r + 1) u v} ψ
    refine ⟨(overFunctor (derivedChangeRingIndependentCoefficients J B) U).mapIso
      (eqToIso (D.obj_eq M)) ≪≫ scalarOverIso φ M U ≪≫
      eqToIso (D'.obj_eq (M.over U)).symm ≪≫ D'.E.mapIso e ≪≫
      PreservesProduct.iso D'.E (fun _ : Fin n ↦ unit O) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ eqToIso (D'.obj_eq (unit O)) ≪≫ scalarUnitIso ψ)⟩
  · intro N a
    dsimp only [locallyFreeScalarComparison]
    have hε := D.ε.naturality ((HomologicalComplex.single _ (.up ℤ) 0).map a)
    dsimp only [Functor.comp_map] at hε
    rw [← Category.assoc, hε]
    simp only [Category.assoc, ← Functor.map_comp]
    have hs :=
      (HomologicalComplex.singleMapHomologicalComplex D.E (.up ℤ) 0).hom.naturality a
    dsimp only [Functor.comp_map] at hs
    rw [hs]


end SheafOfModules
