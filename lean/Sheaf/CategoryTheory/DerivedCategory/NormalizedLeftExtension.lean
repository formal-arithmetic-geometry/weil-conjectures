/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility

/-! # Normalized derivation of an ordinary left extension

Source: Stacks 06XN, 09T5 and 0FND.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe a av b bv dA dB
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{dB} D]

/-- Derived data for a fixed ordinary adjunction. The universal property determines
its functor and comparison up to unique isomorphism.
Source: Stacks 06XN (blueprint: lem-pur-normalized-left-extension). -/
structure SystemLeftExtensionDerivation
    (R : D ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (E : A ⥤ D) [E.Additive] (adj : E ⊣ R) (p : CochainComplex A ℤ → Prop) where
  derived : DerivedCategory A ⥤ DerivedCategory D
  comparison : DerivedCategory.Q ⋙ derived ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison (HomologicalComplex.quasiIso A (.up ℤ))
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, p P → IsIso (comparison.app P)
  [shift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  adjunction : derived ⊣ R.mapDerivedCategory
  transpose : ∀ (P : CochainComplex A ℤ) (K : CochainComplex D ℤ)
    (f : (E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (comparison.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R.mapDerivedCategoryFactors.inv.app K


/-- Include the fixed ordinary adjunction in its derived package.
Source: Stacks 06XN (blueprint: lem-pur-normalized-left-extension). -/
def SystemLeftExtensionDerivation.toExtension
    {R : D ⥤ A} [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {E : A ⥤ D} [E.Additive] {adj : E ⊣ R} {p : CochainComplex A ℤ → Prop}
    (d : SystemLeftExtensionDerivation R E adj p) : SystemDerivedLeftExtension R p where
  ordinary := E
  ordinaryAdj := adj
  derived := d.derived
  comparison := d.comparison
  universal := d.universal
  pointwise := d.pointwise
  computes := d.computes
  shift := d.shift
  triangulated := d.triangulated
  adjunction := d.adjunction
  transpose := d.transpose

/-- Derive an additive left adjoint on any resolving class on which it preserves
quasi-isomorphisms, retaining the representative-normalized derived transpose.
Source: Stacks 06XN, 09T5 and 0FND
(blueprint: lem-pur-normalized-left-extension).
Proof: pass the resolving class to the homotopy category. The resolving-class theorem
constructs the pointwise universal left derived pair, triangulated and computing on
the class. Transfer its pointwise Kan property through the full essentially surjective
homotopy quotient to cochains. Exactness of the right adjoint makes its denominator
ind-diagrams essentially constant at the identity stage. The resolving class makes
the left denominator pro-diagrams essentially constant. Derived adjoint compatibility
then supplies the adjunction and its normalized Hom formula on homotopy objects;
the cochain compatibility lemma transfers that formula to every cochain map. -/
theorem nonempty_normalizedLeftExtension
    (R : D ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (E : A ⥤ D) [E.Additive] (adj : E ⊣ R)
    (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (f : L ⟶ K), p L ∧ QuasiIso f)
    (inv : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L),
      p K → p L → QuasiIso f →
        QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    Nonempty (SystemLeftExtensionDerivation R E adj p) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WD := HomotopyCategory.quasiIso D (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := D)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, p K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X), X' ∈ P ∧ WA s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := res K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → WA s → IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := inv f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh WD _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory D) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor WA := hpw
  let : T.IsLeftDerivedFunctor ε WA := huniv
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε WA)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  obtain ⟨_, _, _, _, htwoA, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : WA.HasTwoOutOfThreeProperty := htwoA
  obtain ⟨hleftD, _, _, _, _, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated D
  let : WD.HasLeftCalculusOfFractions := hleftD
  have hL : ∀ M : HomotopyCategory A (.up ℤ),
      ∃ X : DerivedCategory D, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget WA ⊤ M ⋙ Over.forget M ⋙ F) X := by
    intro M
    obtain ⟨X, u, hX, _⟩ := Functor.resolvingClass_essentialConstancy WA F P hres hinv M
    exact ⟨X, hX⟩
  let U := R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := A)
  have hU : WD.IsInvertedBy U := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Qh.map f) := Localization.inverts DerivedCategory.Qh WD f hf
    exact (NatIso.isIso_map_iff R.mapDerivedCategoryFactorsh f).1 (by
      change IsIso (R.mapDerivedCategory.map (DerivedCategory.Qh.map f))
      infer_instance)
  have hR : ∀ K : HomotopyCategory D (.up ℤ),
      ∃ X : DerivedCategory A, IsEssentiallyConstantIndDiagram
        (MorphismProperty.Under.forget WD ⊤ K ⋙ Under.forget K ⋙ U) X := by
    intro K
    exact ⟨U.obj K, inverted_indDiagram WD U hU K⟩
  have hRF := Functor.isRightDerivedFunctor_of_inverts WD
    R.mapDerivedCategory R.mapDerivedCategoryFactorsh
  obtain ⟨d, hd⟩ := exists_derived_adjunction_compatibility
    R E adj hR hL R.mapDerivedCategory T R.mapDerivedCategoryFactorsh.inv ε hRF huniv
  obtain ⟨hshift, htriang⟩ := htri
  let : T.CommShift ℤ := hshift
  refine ⟨{ derived := T
            comparison := β
            universal := ⟨hβ.isRightKanExtension⟩
            pointwise := ?_
            computes := ?_
            shift := hshift
            triangulated := htriang
            adjunction := d
            transpose := ?_ }⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro K hK
    have := hcomp (q.obj K) ⟨K, hK, rfl⟩
    dsimp [β, α]
    infer_instance
  · apply adjunction_cochain_transpose E R adj T β ε ?_ d hd
    intro K
    dsimp [β, α, i, j]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
      Quotient.lift.isLift_inv, Functor.comp_obj]
    erw [T.map_id, DerivedCategory.Qh.map_id]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id,
      Category.comp_id, Category.comp_id]

end SheafOfModules
