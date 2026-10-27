/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.TensorSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Reduction to w-contractible schemes

A complex of module objects on `X_proét` is acyclic as soon as its sections over all objects
`w : S ⟶ X` with `S` the spectrum of a w-contractible ring are
(`AlgebraicGeometry.ProEtale.acyclic_of_forall_isWContractibleRing'`), and these sections are
global sections of pullbacks to `S`. So the acyclicity of `f^* C ⊗ N` reduces to the acyclicity of
the global sections of `g^* C ⊗ N'` for all `g : S ⟶ Y` and module objects `N'` on `S`
(`AlgebraicGeometry.ProEtale.CondensedRing.acyclic_tensorRight_upperStar_of_forall`).
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (P : C → Prop)

/-- The version for sheaves of abelian groups of
`CategoryTheory.GrothendieckTopology.exact_iff_of_forall_exists`: if every object of the site is
covered by weakly contractible objects satisfying `P`, exactness of a short complex of sheaves of
abelian groups is detected on sections over objects satisfying `P`. -/
lemma exact_iff_of_forall_exists_ab [HasSheafify J Ab.{w}]
    [J.WEqualsLocallyBijective Ab.{w}] [J.HasSheafCompose (forget Ab.{w})]
    (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
      (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
    (hPW : ∀ W, P W → J.IsWeaklyContractible.{w} W)
    (S : ShortComplex (Sheaf J Ab.{w})) :
    S.Exact ↔ ∀ W, P W → (S.map (sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op W))).Exact := by
  have key (W : C) : (S.map (sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op W))).Exact ↔
      Function.Surjective ((kernel.lift S.g S.f S.zero).hom.app (op W)) := by
    rw [ShortComplex.exact_map_iff_epi_map_kernel_lift, AddCommGrpCat.epi_iff_surjective]
    rfl
  simp_rw [key]
  rw [ShortComplex.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun h W hW ↦ hPW W hW ((sheafCompose J (forget _)).map _)
    ((Presheaf.isLocallySurjective_iff_whisker_forget J _).1 h), fun h ↦ ⟨fun {V} s ↦ ?_⟩⟩
  obtain ⟨ι, W, f, hW, hcov⟩ := hP V
  refine J.superset_covering ?_ hcov
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  exact (Presheaf.imageSieve _ s).downward_closed (h _ (hW i) _) a

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}} {B : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj B] [IsCommMonObj B]

omit [IsCommMonObj B] in
/-- **Detection of acyclicity on w-contractible objects.** A complex of module objects over a
ring object of abelian pro-étale sheaves is acyclic if its sections over every object `W` with
`W.left ≅ Spec R`, for `R` a w-contractible ring, form an acyclic complex. -/
lemma acyclic_of_forall_isWContractibleRing
    (K : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) B) ℤ)
    (h : ∀ (W : X.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R] (_ : W.left ≅ Spec R),
      (((modSections W).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff, ← ShortComplex.exact_map_iff_of_faithful _ (Mod.forget B),
    GrothendieckTopology.exact_iff_of_forall_exists_ab.{u + 1, u}
      (fun W : X.ProEt ↦ ∃ R : CommRingCat.{u}, IsWContractibleRing R ∧ Nonempty (W.left ≅ Spec R))
      (fun V ↦ Scheme.ProEt.exists_isWContractibleRing_cover V)
      (fun W ⟨R, hR, ⟨e⟩⟩ ↦ ProEt.isWeaklyContractible_of_iso e)]
  rintro W ⟨R, hR, ⟨e⟩⟩
  exact h W R e n

omit [IsCommMonObj B] in
/-- Variant of `acyclic_of_forall_isWContractibleRing` with the test objects given by weakly étale
morphisms `w : S ⟶ X` from spectra `S` of w-contractible rings. -/
lemma acyclic_of_forall_isWContractibleRing'
    (K : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) B) ℤ)
    (h : ∀ (S : Scheme.{u}) (w : S ⟶ X) [WeaklyEtale w] (R : CommRingCat.{u})
      [IsWContractibleRing R] (_ : S ≅ Spec R),
      (((modSections (ProEt.mk w)).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    K.Acyclic :=
  acyclic_of_forall_isWContractibleRing K fun W R _ e ↦
    have := W.prop
    h W.left W.hom R e

variable {S : Scheme.{u}} (w : S ⟶ X) [WeaklyEtale w]

/-- The object `w : S ⟶ X` of the small pro-étale site of `X` is the image under the localization
functor of the terminal object of the small pro-étale site of `S`. -/
noncomputable def overMapMkIdIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale w)).obj (ProEt.mk (𝟙 S)) ≅
      ProEt.mk w where
  hom := MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp _)
  inv := MorphismProperty.Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  hom_inv_id := MorphismProperty.Over.Hom.ext (by simp)
  inv_hom_id := MorphismProperty.Over.Hom.ext (by simp)

/-- The sections over `w : S ⟶ X` of an abelian sheaf `F` on `X_proét` are the global sections of
its pullback to `S`, i.e. the sections over the terminal object of `S_proét`. -/
noncomputable def upperStarSectionsIso :
    (w)^*[Ab.{u + 1}] ⋙ sheafToPresheaf _ _ ⋙
        (CategoryTheory.evaluation _ _).obj (op (ProEt.mk (𝟙 S))) ≅
      sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op (ProEt.mk w)) :=
  Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction Ab.{u + 1} w inferInstance) _ ≪≫
    NatIso.ofComponents (fun F ↦ F.obj.mapIso (overMapMkIdIso w).op.symm) (fun φ ↦
      (φ.hom.naturality (overMapMkIdIso w).inv.op).symm)

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The underlying sheaf of the pullback `f^* M` of a module object is the pullback of the
underlying sheaf, the extension of scalars along the isomorphism `α_f` being restriction of
scalars along its inverse. -/
noncomputable def upperStarCompForgetIso {X' Y : Scheme.{u}} (f : X' ⟶ Y) :
    (f)^*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ X') ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ (f)^*[Ab.{u + 1}] :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
      (Functor.isoWhiskerRight (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
        (Mod.forget (condensedRingObj Λ X'))) ≪≫ Iso.refl _

/-- The sections over `w : S ⟶ X` of a module object over `Λ_X` are the global sections of its
pullback to `S`. -/
noncomputable def upperStarModSectionsIso :
    (w)^*⟦Λ⟧ ⋙ modSections (ProEt.mk (𝟙 S)) ≅ modSections (ProEt.mk w) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (upperStarCompForgetIso Λ w) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (upperStarSectionsIso w)

/-- For `w : S ⟶ X` weakly étale and a module object `N` over `Λ_X`, the functor
`M ↦ Γ(w, f^* M ⊗ N)` is the functor `M ↦ Γ(S, (w ≫ f)^* M ⊗ w^* N)` of global sections over
`S`. -/
noncomputable def sectionsTensorUpperStarIso {Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (w ≫ f)^*⟦Λ⟧ ⋙ tensorRight ((w)^*⟦Λ⟧.obj N) ⋙ modSections (ProEt.mk (𝟙 S)) ≅
      (f)^*⟦Λ⟧ ⋙ tensorRight N ⋙ modSections (ProEt.mk w) :=
  Functor.isoWhiskerRight (upperStarComp Λ w f) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (f)^*⟦Λ⟧ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.Monoidal.commTensorRight (w)^*⟦Λ⟧ N) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tensorRight N) (upperStarModSectionsIso w Λ))

omit [WeaklyEtale w] in
/-- **Reduction to w-contractible schemes.** Let `f : X ⟶ Y` and `C` a complex of module
objects over `Λ_Y`. If, for every scheme `S ≅ Spec R` with `R` w-contractible and every
`g : S ⟶ Y`, the global sections of `g^* C ⊗ N` form an acyclic complex for all module objects
`N` over `Λ_S`, then `f^* C ⊗ N` is acyclic for every module object `N` over `Λ_X`. -/
theorem acyclic_tensorRight_upperStar_of_forall {Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (H : ∀ (S : Scheme.{u}) (R : CommRingCat.{u}) [IsWContractibleRing R] (_ : S ≅ Spec R)
      (g : S ⟶ Y) (N : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      ((((g)^*⟦Λ⟧ ⋙ tensorRight N ⋙ modSections (ProEt.mk (𝟙 S))).mapHomologicalComplex
        (.up ℤ)).obj C).Acyclic)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj
      (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj C)).Acyclic := by
  refine acyclic_of_forall_isWContractibleRing' _ fun S w _ R _ e ↦ ?_
  have h : ((((f)^*⟦Λ⟧ ⋙ tensorRight N ⋙ modSections (ProEt.mk w)).mapHomologicalComplex
      (.up ℤ)).obj C).Acyclic := (H S R e (w ≫ f) ((w)^*⟦Λ⟧.obj N)).of_iso
    ((NatIso.mapHomologicalComplex (sectionsTensorUpperStarIso w Λ f N) (.up ℤ)).app C)
  exact h

end CondensedRing

end AlgebraicGeometry.ProEtale
