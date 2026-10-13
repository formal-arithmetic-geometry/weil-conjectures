/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.PerfectTensorHomDuality
import Sheaf.CategoryTheory.MonoidalProjectionConjugate
import Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration
import Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Sheaf.AlgebraicGeometry.DerivedTensorRightCoproducts
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Sheaf.AlgebraicGeometry.DerivedTensorQCohClosure
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # The pinned quasi-coherent projection formula

Source: Stacks Project, Tag 08EU, with perfect generation (Tag 09IS) and
perfect tensor-Hom duality (Tags 0B54 and 0A9T).
(blueprint: lem-sc-right-adjoint-tensor-comparison-projection).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- Projection formula isomorphisms with the pinned inverse equation.
Source: Stacks Project, Tag 08EU; perfect generation is Tag 09IS.
Proof: fix E = c(O_Y) and use hRf to regard Rf_*E as quasi-coherent. For perfect K,
tensor-Hom duality identifies the displayed mate with the conjugate of the
monoidal tensorator at its dual, so it is invertible. The mates are natural in K.
Their isomorphism locus is stable under retracts by naturality, under shifts and
cones by projectionComparison_triangles, and under coproducts because pullback
is a left adjoint, tensor preserves coproducts, and direct image preserves
coproducts of quasi-coherent objects. Perfect generation therefore puts every K
in this locus. Invert its canonical component to obtain pf; its inverse is the
specified mate by construction.
(blueprint: lem-sc-right-adjoint-tensor-comparison-projection) -/
theorem exists_rightAdjointTensorComparison_projection
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z) :
    ∃ pf : ∀ K : schemeDerivedQCohCategory Y,
      (schemeDerivedDirectImage f).obj
          (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
        K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
      ∀ K, (pf K).inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) := by
  classical
  let E := c.obj ⟨𝟙_ _, hO⟩
  let RE : schemeDerivedQCohCategory Y :=
    ⟨(schemeDerivedDirectImage f).obj E.obj, hRf E⟩
  let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
    IsIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj
        RE.obj).inv ≫
          (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))
  have hperfect (K : schemeDerivedQCohCategory Y)
      (hK : Scheme.perfectSubcategory Y K.obj) : P K := by
    obtain ⟨L, ⟨pair⟩, _⟩ := perfect_tensor_hom_duality Y K hK
    let : ExactPairing K.obj L.obj := pair
    let F := derivedPullback f
    let R := schemeDerivedDirectImage f
    let : ExactPairing (F.obj K.obj) (F.obj L.obj) := ExactPairing.map F K.obj L.obj
    let b₁ := (tensorLeftAdjunction K.obj L.obj).comp a
    let b₂ := a.comp (tensorLeftAdjunction (F.obj K.obj) (F.obj L.obj))
    have h : IsIso ((conjugateEquiv b₁ b₂
        (Functor.Monoidal.commTensorLeft F L.obj).hom).app E.obj) := by
      infer_instance
    change IsIso _
    rw [← monoidal_projection_conjugate F R a K.obj L.obj E.obj]
    exact h
  let τ : (schemeDerivedQCohProperty Y).ι ⋙
      tensorRight RE.obj ⟶
      (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight E.obj ⋙ schemeDerivedDirectImage f :=
    { app := fun K ↦ (a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj
          RE.obj).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj)
      naturality := by
        intro K L g
        change g.hom ▷ RE.obj ≫ _ =
          _ ≫ (schemeDerivedDirectImage f).map
            ((derivedPullback f).map g.hom ▷ E.obj)
        apply a.homEquiv_naturality_left_square
        simp only [Functor.Monoidal.μIso_inv]
        rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left]
        simp only [Category.assoc]
        rw [← whisker_exchange] }
  have hretract (A B : schemeDerivedQCohCategory Y) (hB : P B)
      (r : Retract A.obj B.obj) : P A := by
    let r' : Retract A B :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := ObjectProperty.hom_ext _ r.retract }
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
      (τ.retractArrowApp r') hB
  obtain ⟨hshift, hcone⟩ := projectionComparison_triangles f a E
  have hsum (J : Type u) (K : J → schemeDerivedQCohCategory Y)
      (S : schemeDerivedCategory Y) (ι : ∀ j, (K j).obj ⟶ S)
      (hc : IsColimit (Cofan.mk S ι)) (B : schemeDerivedQCohCategory Y)
      (e : B.obj ≅ S) (hK : ∀ j, P (K j)) : P B := by
    let q : Cofan K := Cofan.mk B (fun j ↦ ObjectProperty.homMk (ι j ≫ e.inv))
    have hq : IsColimit q := by
      refine Cofan.IsColimit.mk q
        (fun s ↦ ObjectProperty.homMk (e.hom ≫
          hc.desc (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)))) ?_ ?_
      · intro s j
        apply ObjectProperty.hom_ext _
        simpa [q, Category.assoc] using hc.fac
          (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩
      · intro s m hm
        apply ObjectProperty.hom_ext _
        apply (cancel_epi e.inv).mp
        change e.inv ≫ m.hom = e.inv ≫ e.hom ≫ _
        rw [Iso.inv_hom_id_assoc]
        apply hc.hom_ext
        intro ⟨j⟩
        simpa [q, Category.assoc] using (congrArg (fun φ ↦ φ.hom) (hm j)).trans
          (hc.fac (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩).symm
    let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
    let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete J) :=
      schemeDerivedQCohClosedUnderCoproducts Y J
    let : PreservesColimitsOfShape (Discrete J) (derivedPullback f) :=
      a.leftAdjoint_preservesColimits.preservesColimitsOfShape
    let : PreservesColimitsOfShape (Discrete J) (tensorRight E.obj) :=
      derivedTensorRight_preservesCoproducts Z E.obj J
    let : PreservesColimitsOfShape (Discrete J) (tensorRight RE.obj) :=
      derivedTensorRight_preservesCoproducts Y RE.obj J
    let G := (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj
    have hqcG (A : schemeDerivedQCohCategory Y) : schemeDerivedQCohProperty Z (G.obj A) :=
      canonical_derivedTensor_preserve_QCoh Z _ E.obj
        ((derivedPullback_tensor_preserve_QCoh f).1 A.obj A.property) E.property
    let : PreservesColimit (Discrete.functor K ⋙ G) (schemeDerivedDirectImage f) := by
      apply (preservesColimit_iff_of_iso_diagram (schemeDerivedDirectImage f)
        (Discrete.natIsoFunctor (F := Discrete.functor K ⋙ G))).mpr
      exact derivedDirectImagePreservesDirectSums f J
        (fun j ↦ ⟨G.obj (K j), hqcG (K j)⟩)
    let : PreservesColimit (Discrete.functor K) (G ⋙ schemeDerivedDirectImage f) :=
      comp_preservesColimit _ _
    let : PreservesColimit (Discrete.functor K)
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
          tensorRight E.obj ⋙ schemeDerivedDirectImage f) := by
      change PreservesColimit (Discrete.functor K) (G ⋙ schemeDerivedDirectImage f)
      infer_instance
    have : ∀ j : Discrete J,
        IsIso ((Functor.whiskerLeft (Discrete.functor K) τ).app j) := fun j ↦ hK j.as
    have : IsIso (Functor.whiskerLeft (Discrete.functor K) τ) :=
      NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit (Discrete.functor K) τ q hq
  have hclosure :
      (∀ (A B : schemeDerivedQCohCategory Y), P A → Nonempty (A ≅ B) → P B) ∧
      (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
        ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
      (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
        ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
          T ∈ Pretriangulated.distinguishedTriangles →
          Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
          ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C) ∧
      (∀ (A B : schemeDerivedQCohCategory Y), P B →
        Nonempty (Retract A.obj B.obj) → P A) ∧
      (∀ (J : Type u) (K : J → schemeDerivedQCohCategory Y),
        ∀ (S : schemeDerivedCategory Y) (ι : ∀ j, (K j).obj ⟶ S),
          IsColimit (Cofan.mk S ι) →
          ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ S) →
            (∀ j, P (K j)) → P B) := by
    refine ⟨?_, hshift, hcone, ?_, ?_⟩
    · intro A B hA ⟨e⟩
      exact hretract B A hA
        (((schemeDerivedQCohProperty Y).ι.mapIso e).symm.retract)
    · intro A B hB ⟨r⟩
      exact hretract A B hB r
    · intro J K S ι hc B ⟨e⟩ hK
      exact hsum J K S ι hc B e hK
  have hle : perfectLocalizingClosure Y ≤ P := by
    apply sInf_le
    exact ⟨hperfect, hclosure⟩
  have hP : ∀ K : schemeDerivedQCohCategory Y, P K := by
    intro K
    apply hle K
    rw [derivedQCohPerfectGeneration Y]
    trivial
  refine ⟨fun K ↦ ?_, ?_⟩
  · have : IsIso ((a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj RE.obj).inv ≫
          (derivedPullback f).obj K.obj ◁ a.counit.app E.obj)) := hP K
    exact (asIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj RE.obj).inv ≫
        (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))).symm
  · intro K
    rfl
end AlgebraicGeometry
