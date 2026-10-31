/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectReductionRoosData
import WeilConjectures.AlgebraicGeometry.PerfectReductionTowerResolution
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final

/-! # Universal scalar extension of a whole constant-coefficient tower

Source: Stacks Tags 06YS, 06YY and 06XN.
(blueprint: lem-sp-perfect-reduction-tower-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone

namespace CategoryTheory.PerfectReductionRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)


variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- Scalar extension on strict towers admits a universal derived pair computing on
all levelwise K-flat complexes.

Source: Stacks Tags 06YS, 06YY, 06XN
(blueprint: lem-sp-perfect-reduction-tower-extension).

Proof: The sequence-site resolution theorem supplies a levelwise K-flat strict
resolution of every complex. Evaluation detects quasi-isomorphisms, so scalar
extension preserves those between levelwise K-flat complexes. Apply the resolving-class
left-derived construction on the homotopy category of strict towers. Its counit is
invertible on the resolving class. Precompose with the full essentially surjective
homotopy quotient and transport along the canonical quotient/localization comparison;
pointwise right Kan extension is preserved by these operations. Thus the transferred
cochain counit has the required universal property and the same invertible components. -/
theorem exists_towerExtension
    (m : ℕ) (d : DerivedChangeOfRingsCochainModel (powerProjection R t m)) :
    ∃ e : TowerExtension d.E,
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ,
        (∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R)
          (P.asFunctor.obj (op n))) → IsIso (e.ε.app P) := by
  classical
  let A := ℕᵒᵖ ⥤ Modules R
  let B := ℕᵒᵖ ⥤ Modules (powerRing R t m)
  let E : A ⥤ B := (Functor.whiskeringRight ℕᵒᵖ _ _).obj d.E
  let good (P : CochainComplex A ℤ) : Prop :=
    ∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (P.asFunctor.obj (op n))
  have hpres {P Q : CochainComplex A ℤ} (f : P ⟶ Q)
      (hP : good P) (hQ : good Q) (hf : QuasiIso f) :
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    have he := (HomologicalComplex.quasiIso_iff_evaluation f).1 hf n
    exact d.preserves
      (((evaluation ℕᵒᵖ (Modules R)).obj n).mapHomologicalComplex (.up ℤ) |>.map f)
      (hP n.unop) (hQ n.unop) he
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, good K ∧
      (HomotopyCategory.quotient A (.up ℤ)).obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := constantTower_kFlatResolution R K
    refine ⟨(HomotopyCategory.quotient A (.up ℤ)).obj L,
      (HomotopyCategory.quotient A (.up ℤ)).map f,
      ⟨L, fun n ↦ (hL n).1, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    let q := HomotopyCategory.quotient A (.up ℤ)
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf : QuasiIso f :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpres f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, _htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine ⟨{ F := T, ε := β, universal := ⟨hβ.isRightKanExtension⟩ }, ?_⟩
  intro K hK
  have := hcomp (q.obj K) ⟨K, hK, rfl⟩
  dsimp [β, α]
  infer_instance

end CategoryTheory.PerfectReductionRoos
