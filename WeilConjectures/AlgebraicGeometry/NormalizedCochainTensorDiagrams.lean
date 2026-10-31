/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDerivedTensorModels
import WeilConjectures.AlgebraicGeometry.CanonicalCochainTensorComparison
import WeilConjectures.SixFunctors.RingedDerivedTensorDiagrams
import WeilConjectures.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Coherence from the normalized cochain tensor square

Source: Stacks 07A4 and 0G7E. A comparison characterized on flat K-flat complexes
is the canonical comparison, so its coherence follows from canonicalTensorDiagrams.
(blueprint: lem-pur-normalized-cochain-tensor-diagrams).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory HomologicalComplex₂.total
  CategoryTheory.CochainPullback.comparison HomologicalComplex.single

namespace CategoryTheory.FiniteDerivedTensorModels

attribute [local irreducible] legacyComparison canonical_model
  SheafOfModules.RingedTensorEdge.tensorComparison
  SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison

attribute [local semireducible] SheafOfModules.monoidalCategory

/-- The cochain counit followed by the normalized ordinary unit comparison.
Source: Stacks 07A4 and 03EL.
(blueprint: lem-pur-normalized-cochain-tensor-diagrams). -/
def cochainUnitComparison {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f)
    (F : Y.D ⥤ X.D)
    (εc : DerivedCategory.Q ⋙ F ⟶ CochainPullback.pull f ⋙ DerivedCategory.Q) :
    F.obj Y.closed.monoidal.tensorUnit ⟶ X.closed.monoidal.tensorUnit :=
  F.map Y.coherence.unitIso.hom ≫
    εc.app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
    DerivedCategory.Q.map (CochainPullback.unit.{u, u, u, u, u} f k).hom ≫ X.coherence.unitIso.inv

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem derived_right_exists {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (F : Y.D ⥤ X.D)
    (εc : DerivedCategory.Q ⋙ F ⟶ CochainPullback.pull f ⋙ DerivedCategory.Q)
    (hcomputes : ∀ P, Y.corner.mateFlat P → IsIso (εc.app P))
    (ε : DerivedCategory.Qh ⋙ F ⟶ f.L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso Y.modules (.up ℤ)))
    (heq : ∀ P : CochainComplex Y.modules ℤ,
      ε.app ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P) = εc.app P) :
    ∃ RF : X.D ⥤ Y.D, Nonempty (F ⊣ RF) := by
  let := f.moduleAdj.right_adjoint_additive
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions X.J X.A).1
  obtain ⟨RF, η, hRF, _⟩ := CategoryTheory.exists_derived f.V
  let π := HomotopyCategory.quotient Y.modules (.up ℤ)
  let GF := f.L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  let H : Set (HomotopyCategory Y.modules (.up ℤ)) := {T | Y.corner.mateFlat T.as}
  have hres : ∀ T : HomotopyCategory Y.modules (.up ℤ),
      ∃ (T' : HomotopyCategory Y.modules (.up ℤ)) (s : T' ⟶ T),
        T' ∈ H ∧ HomotopyCategory.quasiIso Y.modules (.up ℤ) s := by
    intro T
    obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
    obtain ⟨P, p, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients T
    exact ⟨π.obj P, π.map p, ⟨hp, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩
  have hinv : ∀ (T T' : HomotopyCategory Y.modules (.up ℤ)) (s : T ⟶ T'),
      T ∈ H → T' ∈ H → HomotopyCategory.quasiIso Y.modules (.up ℤ) s →
        IsIso (GF.map s) := by
    intro T T' s hT hT' hs
    have hc (V : HomotopyCategory Y.modules (.up ℤ)) (hV : V ∈ H) : IsIso (ε.app V) := by
      obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective V
      rw [heq]
      exact hcomputes P hV
    have := hc T hT
    have := hc T' hT'
    have hiso : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.modules (.up ℤ)) s hs
    have hn := ε.naturality s
    have : IsIso (ε.app T ≫ GF.map s) := by
      rw [← hn]
      change IsIso (F.map (DerivedCategory.Qh.map s) ≫ ε.app T')
      infer_instance
    exact (isIso_comp_left_iff _ _).1 this
  obtain ⟨adj, _⟩ := derivedAdjunctionOfResolvingClass f.L f.V f.moduleAdj H hres hinv
    F ε hε RF η hRF
  exact ⟨RF, ⟨adj⟩⟩

set_option maxHeartbeats 800000 in
-- Elaborate the normalized tensor square together with all four coherence equations.
/-- The representative square forces all coherence equations for its specified maps.
Source: Stacks 07A4 and 0G7E, with ordinary scalar-action units from 03EL.
(blueprint: lem-pur-normalized-cochain-tensor-diagrams).

Proof: descend the universal counit through the homotopy quotient with unchanged
components. Flat K-flat resolutions and the computation hypothesis show the
localized ordinary pullback inverts resolving quasi-isomorphisms. Resolving-class
adjunction against the K-injective right-derived functor supplies a right adjoint
to this same F. Package the canonical tensor edge with its recorded site models.
The unique representative characterization identifies its tensor comparison with nu.
The ordinary scalar-action unit and the identity quotient comparisons identify its
unit map with cochainUnitComparison. Apply canonicalTensorDiagrams, and conjugate
its two inverse-unitor identities by the forward unitors to obtain the stated laws.
-/
theorem normalized_cochain_tensor_diagrams {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (F : Y.D ⥤ X.D)
    (εc : DerivedCategory.Q ⋙ F ⟶ CochainPullback.pull f ⋙ DerivedCategory.Q)
    (nu : Y.closed.tensor ⋙ F ≅ (F.prod F) ⋙ X.closed.tensor)
    (huniversal : F.IsLeftDerivedFunctor εc
      (HomologicalComplex.quasiIso Y.modules (.up ℤ)))
    (hcomputes : ∀ P, Y.corner.mateFlat P → IsIso (εc.app P))
    (hnormalized : ∀ (P Q : CochainComplex Y.modules ℤ)
      (hP : Y.corner.mateFlat P) (hQ : Y.corner.mateFlat Q),
      ∃ (hP' : X.corner.mateFlat ((CochainPullback.pull f).obj P))
        (hQ' : X.corner.mateFlat ((CochainPullback.pull f).obj Q)),
        F.map (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom ≫
            nu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            X.closed.tensor.map (Prod.mkHom (εc.app P) (εc.app Q)) =
          εc.app (P ⊗ Q) ≫ DerivedCategory.Q.map (CochainPullback.comparison f k P Q).hom ≫
            (X.model.iso X.J X.A X.closed ((CochainPullback.pull f).obj P)
              ((CochainPullback.pull f).obj Q) hP'.1 hQ'.1).hom) :
    IsIso (cochainUnitComparison f k F εc) ∧
    (∀ M N P : Y.D,
      (nu).hom.app (Y.closed.tensor.obj (M, N), P) ≫
          X.closed.tensor.map (Prod.mkHom ((nu).hom.app (M, N))
            (𝟙 (F.obj P))) ≫
          (X.closed.monoidal.associator (F.obj M) (F.obj N) (F.obj P)).hom =
        F.map (Y.closed.monoidal.associator M N P).hom ≫
          (nu).hom.app (M, Y.closed.tensor.obj (N, P)) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (F.obj M))
            ((nu).hom.app (N, P)))) ∧
    (∀ M : Y.D,
      (nu).hom.app (Y.closed.monoidal.tensorUnit, M) ≫
          X.closed.tensor.map (Prod.mkHom (cochainUnitComparison f k F εc) (𝟙 (F.obj M))) ≫
          (X.closed.monoidal.leftUnitor (F.obj M)).hom =
        F.map (Y.closed.monoidal.leftUnitor M).hom) ∧
    (∀ M : Y.D,
      (nu).hom.app (M, Y.closed.monoidal.tensorUnit) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (F.obj M)) (cochainUnitComparison f k F εc)) ≫
          (X.closed.monoidal.rightUnitor (F.obj M)).hom =
        F.map (Y.closed.monoidal.rightUnitor M).hom) ∧
    (∀ M N : Y.D,
      (nu).hom.app (M, N) ≫
          (X.symmetry.toBraidedCategory.braiding (F.obj M) (F.obj N)).hom =
        F.map (Y.symmetry.toBraidedCategory.braiding M N).hom ≫
          (nu).hom.app (N, M)) := by
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  obtain ⟨ε, hε, heq⟩ := exists_homotopy_leftDerived_comparison f.L F εc huniversal
  obtain ⟨RF, ⟨adj⟩⟩ := derived_right_exists f F εc hcomputes ε hε heq
  let e : SheafOfModules.RingedTensorEdge Y.corner X.corner := {
    inverse := f.uInv
    direct := f.uPush
    adjunction := f.adj
    finiteLimits := f.finiteLimits
    inverseRing := f.RI
    algebraic := f.I
    ringMap := f.coefficient
    pullback := f.L
    object_eq := f.hobj
    map_eq := f.hmap
    additive := f.additive
    ordinaryTensor := legacyComparison f k
    pushforward := f.V
    moduleAdjunction := f.moduleAdj
    left := F
    epsilon := ε
    isLeftDerived := hε
    right := RF
    derivedAdjunction := adj }
  let rY := canonical_model Y
  let rX := canonical_model X
  have hc (P : CochainComplex Y.modules ℤ) :
      derivedPullbackComplexComparison f.L F ε P = εc.app P :=
    (complexComparison_eq_component f.L F ε P).trans (heq P)
  have hn : e.tensorComparison rY rX = nu := by
    have := f.finiteLimits
    unfold SheafOfModules.RingedTensorEdge.tensorComparison
    exact canonicalComparison_eq f k F εc nu ε hε heq hnormalized
  obtain ⟨j, hj, hunit⟩ := unit_presentation f k
  have hu : canonicalDerivedUnitComparison e j = cochainUnitComparison f k F εc := by
    unfold canonicalDerivedUnitComparison cochainUnitComparison
    dsimp only [e, Site.corner]
    erw [hc, hunit]
    with_unfolding_all rfl
  obtain ⟨ha, hα, hl, hr, hβ⟩ := canonicalTensorDiagrams e rY rX
    (canonical_model_eq Y) (canonical_model_eq X) j hj
  erw [hn] at hα hl hr hβ
  erw [hu] at ha hl hr
  dsimp only [CoefficientClosedStructure.tensor, tensor] at nu
  dsimp only [e, Iso.app, CoefficientClosedStructure.tensor, tensor, Functor.prod_obj,
    Functor.comp_obj] at hα hl hr hβ ⊢
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · intro M N P
    erw [tensorHom_id, id_tensorHom]
    exact hα M N P
  · intro M
    have hh := congrArg (fun z ↦ F.map (Y.closed.monoidal.leftUnitor M).hom ≫ z ≫
      (X.closed.monoidal.leftUnitor (F.obj M)).hom) (hl M)
    erw [tensorHom_id]
    have hh' := hh.symm
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← F.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp] at hh'
    erw [Category.assoc] at hh'
    with_unfolding_all exact hh'
  · intro M
    have hh := congrArg (fun z ↦ F.map (Y.closed.monoidal.rightUnitor M).hom ≫ z ≫
      (X.closed.monoidal.rightUnitor (F.obj M)).hom) (hr M)
    erw [id_tensorHom]
    have hh' := hh.symm
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← F.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp] at hh'
    erw [Category.assoc] at hh'
    with_unfolding_all exact hh'
  · exact hβ

end CategoryTheory.FiniteDerivedTensorModels
