/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictDerivedComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictTensorNormalized
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Strict representatives for finite coefficient extension

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private theorem coefficientSequenceNormalized_of_iso
    {X Y : coefficientSequenceDerived l E W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E W X) :
    IsNormalizedCoefficientSequence l E W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y =
    (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem coefficientExtensionGoodRepresentative
    (K : DerivedCategory (Mod C R)) :
    ∃ P : ((HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  classical
  obtain ⟨P, q, hq, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have : QuasiIso q := hq
  exact ⟨⟨P, hP⟩, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

variable (A : CoefficientExtensionSystems l E L ι W)

/-- Native scalar extension has simultaneous strict representatives on K-flat complexes.
Source: current blueprint, `det-def-sfb-derived-extension-of-scalars`, K-flat computation
(blueprint: stage3-pur-extension-strict-representatives).
Proof: apply ordinary extension of scalars degreewise to the full subcategory of K-flat
complexes. The universal left-derived counit is natural on complexes and invertible on
this subcategory, hence gives the displayed natural isomorphism. For an arbitrary derived
object choose a K-flat resolution of a complex representing it. Invert its localized
quasi-isomorphism, apply derived extension, and compose with the same counit component.
The isomorphism cancellation identity gives the final equation. This includes the zero
complex and identity scalar maps and requires no flatness of the ring morphism. -/
theorem coefficientExtensionStrictRepresentative_exists :
    let good := (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat
    ∃ model :
        (good.ι ⋙ DerivedCategory.Q) ⋙ (Mod.extendScalars φ).leftDerivedFunctor ≅
          (good.ι ⋙ (Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)) ⋙
            DerivedCategory.Q,
      (∀ P, model.hom.app P =
        (Mod.extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).obj P.obj)) ∧
      ∀ K : DerivedCategory (Mod C R),
        ∃ (P : good.FullSubcategory) (eP : DerivedCategory.Q.obj P.obj ≅ K)
          (e : (Mod.extendScalars φ).leftDerivedFunctor.obj K ≅
            DerivedCategory.Q.obj
              (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P.obj)),
          (Mod.extendScalars φ).leftDerivedFunctor.map eP.hom ≫ e.hom =
            model.hom.app P := by
  classical
  let good := (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat
  let ε : (good.ι ⋙ DerivedCategory.Q) ⋙ (Mod.extendScalars φ).leftDerivedFunctor ⟶
      (good.ι ⋙ (Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    { app := fun P ↦ (Mod.extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).obj P.obj)
      naturality := fun P P' f ↦ by
        exact (Mod.extendScalars φ).leftDerivedFunctorCounit.naturality
          ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).map f.hom) }
  have hi (P : good.FullSubcategory) : IsIso (ε.app P) :=
    (Mod.extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P.obj P.property
  have : IsIso ε := (NatTrans.isIso_iff_isIso_app ε).2 hi
  let model := asIso ε
  refine ⟨model, fun _ ↦ rfl, ?_⟩
  intro K
  obtain ⟨P, ⟨eP⟩⟩ := coefficientExtensionGoodRepresentative K
  refine ⟨P, eP, (Mod.extendScalars φ).leftDerivedFunctor.mapIso eP.symm ≪≫
    model.app P, ?_⟩
  change (Mod.extendScalars φ).leftDerivedFunctor.map eP.hom ≫
      ((Mod.extendScalars φ).leftDerivedFunctor.map eP.inv ≫ model.hom.app P) =
    model.hom.app P
  rw [← Category.assoc, ← (Mod.extendScalars φ).leftDerivedFunctor.map_comp,
    eP.hom_inv_id, (Mod.extendScalars φ).leftDerivedFunctor.map_id, Category.id_comp]

end WeilConjectures
