/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.TensorSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.WeaklyEtaleRestriction

/-!
# Tensoring with modules pulled back through a weakly étale scheme

Let `C` be an acyclic K-flat complex of module objects over `Λ_Y`, `v : V ⟶ Y` weakly étale and
`h : S ⟶ V`, with `S` the spectrum of a w-contractible ring. For every module object `G` over
`Λ_V`, the global sections of `(h ≫ v)^* C ⊗ h^* G` form an acyclic complex
(`AlgebraicGeometry.ProEtale.CondensedRing.acyclic_modSections_tensorRight_upperStar_comp`):
this complex is the global sections of `h^* (v^* C ⊗ G)`, and `v^* C ⊗ G` is acyclic since `C` is
acyclic and K-flat (`acyclic_tensorRight_upperStar_of_weaklyEtale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj

namespace HomologicalComplex

variable {C D ι : Type*} [Category C] [Category D] [Abelian C] [Abelian D] {c : ComplexShape ι}

/-- An exact functor sends acyclic complexes to acyclic complexes. -/
lemma Acyclic.map_of_preservesHomology {K : HomologicalComplex C c} (hK : K.Acyclic)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    ((F.mapHomologicalComplex c).obj K).Acyclic := fun n ↦ by
  have h := hK n
  rw [exactAt_iff] at h ⊢
  exact h.map F

/-- Acyclicity of the image of a complex under a composite of three functors, applied degreewise
all at once or one after the other. -/
lemma acyclic_mapHomologicalComplex_comp₃_iff {E F : Type*} [Category E] [Category F]
    [Abelian E] [Abelian F] (G₁ : C ⥤ D) (G₂ : D ⥤ E) (G₃ : E ⥤ F) [G₁.PreservesZeroMorphisms]
    [G₂.PreservesZeroMorphisms] [G₃.PreservesZeroMorphisms] (K : HomologicalComplex C c) :
    (((G₁ ⋙ G₂ ⋙ G₃).mapHomologicalComplex c).obj K).Acyclic ↔
      ((G₃.mapHomologicalComplex c).obj ((G₂.mapHomologicalComplex c).obj
        ((G₁.mapHomologicalComplex c).obj K))).Acyclic :=
  Iff.rfl

end HomologicalComplex

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Pulling back along `h ≫ v` and tensoring with `h^* G` is pulling back along `v`, tensoring
with `G` and pulling back along `h`. -/
noncomputable def upperStarCompTensorRightIso {S V Y : Scheme.{u}} (h : S ⟶ V) (v : V ⟶ Y)
    (G : Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (h ≫ v)^*⟦Λ⟧ ⋙ tensorRight ((h)^*⟦Λ⟧.obj G) ≅
      (v)^*⟦Λ⟧ ⋙ tensorRight G ⋙ (h)^*⟦Λ⟧ :=
  Functor.isoWhiskerRight (upperStarComp Λ h v) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.Monoidal.commTensorRight (h)^*⟦Λ⟧ G)

/-- **Tensoring with pulled back modules.** For `C` acyclic and K-flat over `Λ_Y`, `v : V ⟶ Y`
weakly étale, `h : S ⟶ V` with `S ≅ Spec R`, `R` w-contractible, and `G` a module object over
`Λ_V`, the global sections of `(h ≫ v)^* C ⊗ h^* G` form an acyclic complex. -/
theorem acyclic_modSections_tensorRight_upperStar_comp {S V Y : Scheme.{u}} (h : S ⟶ V)
    (v : V ⟶ Y) [WeaklyEtale v] {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : S ≅ Spec R)
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (G : Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    ((((h ≫ v)^*⟦Λ⟧ ⋙ tensorRight ((h)^*⟦Λ⟧.obj G) ⋙
      modSections (ProEt.mk (𝟙 S))).mapHomologicalComplex (.up ℤ)).obj C).Acyclic := by
  have := preservesHomology_modSections (B := condensedRingObj Λ S)
    (ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} (W := ProEt.mk (𝟙 S)) hR e)
  have h₁ := ((acyclic_tensorRight_upperStar_of_weaklyEtale v Λ C hC hC' G).map_of_preservesHomology
    (h)^*⟦Λ⟧).map_of_preservesHomology (modSections (ProEt.mk (𝟙 S)))
  have e₁ : (h ≫ v)^*⟦Λ⟧ ⋙ tensorRight ((h)^*⟦Λ⟧.obj G) ⋙ modSections (ProEt.mk (𝟙 S)) ≅
      (v)^*⟦Λ⟧ ⋙ tensorRight G ⋙ (h)^*⟦Λ⟧ ⋙ modSections (ProEt.mk (𝟙 S)) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (upperStarCompTensorRightIso Λ h v G) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _)
  have h₂ : ((((v)^*⟦Λ⟧ ⋙ tensorRight G ⋙ (h)^*⟦Λ⟧ ⋙
      modSections (ProEt.mk (𝟙 S))).mapHomologicalComplex (.up ℤ)).obj C).Acyclic := h₁
  exact h₂.of_iso ((NatIso.mapHomologicalComplex e₁.symm (.up ℤ)).app C)

end AlgebraicGeometry.ProEtale.CondensedRing
