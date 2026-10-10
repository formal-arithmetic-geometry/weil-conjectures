/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.ExistsStage
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The diagram of stage schemes

The scheme attached to a stage is the pushout of `Dⱼ ⟵ Wⱼ ⟶ Spec A` along open immersions.
This file defines the resulting diagram `ExtensionData.stageDiagram` of schemes indexed by the
stages and shows that its transition morphisms are affine.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})
variable {E}

/-- (Implementation) The open immersion of `Wⱼ` into the stage `Dⱼ`. -/
noncomputable abbrev Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.WD.obj j ⟶ E.N.D.obj j.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).app j

instance (E : ExtensionData.{u}) (j : Over E.i₀) : IsOpenImmersion (E.Wι j) :=
  inferInstanceAs (IsOpenImmersion ((opensDiagramι E.N.D E.i₀ E.W₀).app j))

@[reassoc]
lemma WD_map_Wι {j j' : Over E.i₀} (k : j ⟶ j') :
    E.WD.map k ≫ E.Wι j' = E.Wι j ≫ E.N.D.map k.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).naturality k

/-- (Implementation) The first projection from the coefficient algebra of a stage to the
sections of `V`. -/
noncomputable def Stage.φ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.X, E.V) :=
  CommRingCat.ofHom ((RingHom.fst _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.φ_apply (T : E.Stage) (a : ↥T.A) :
    T.φ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 := rfl

/-- (Implementation) The map of coefficient algebras attached to a morphism of stages. -/
noncomputable def Stage.Hom.algHom {T T' : E.Stage} (f : T ⟶ T') :
    CommRingCat.of ↥T'.A ⟶ CommRingCat.of ↥T.A :=
  CommRingCat.ofHom
    ((AlgHom.codRestrict ((resAlgHom f.base).comp T'.A.val) T.A
      (fun a ↦ f.map_mem _ a.2)).toRingHom)

@[simp] lemma Stage.Hom.algHom_coe {T T' : E.Stage} (f : T ⟶ T') (a : ↥T'.A) :
    ((f.algHom a : ↥T.A) : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) =
      ((a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).1,
        E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).2) := rfl

lemma Stage.Hom.algHom_ρ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.ρ = T'.ρ ≫ E.res f.base := rfl

lemma Stage.Hom.algHom_φ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.φ = T'.φ := rfl

@[simp] lemma Stage.Hom.algHom_id (T : E.Stage) : (𝟙 T : T ⟶ T).algHom = 𝟙 _ := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact E.res_id _ _

@[simp] lemma Stage.Hom.algHom_comp {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).algHom = g.algHom ≫ f.algHom := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact (E.res_res g.base f.base _).symm

@[reassoc (attr := simp)]
lemma Stage.Hom.SpecMap_φ {T T' : E.Stage} (f : T ⟶ T') :
    Spec.map T.φ ≫ Spec.map f.algHom = Spec.map T'.φ := by
  rw [← Spec.map_comp, Stage.Hom.algHom_φ]

lemma Stage.toSpec_comp_SpecMap_algHom {T T' : E.Stage} (f : T ⟶ T') :
    T.toSpec ≫ Spec.map f.algHom = E.WD.map f.base ≫ T'.toSpec := by
  rw [Stage.toSpec, Stage.toSpec, Category.assoc, ← Spec.map_comp, Stage.Hom.algHom_ρ,
    Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Elaborating the pushout functor forces repeated defeq checks between the two
-- `Algebra` structures on the coefficient algebra of a stage.
/-- (Implementation) The system of stage schemes: the scheme attached to a stage is the
gluing of the Noetherian stage `Dⱼ` and the affine scheme `Spec A` along `Wⱼ`. -/
noncomputable def stageDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} where
  obj T := pushout (E.Wι T.j) T.toSpec
  map {T T'} f := pushout.map _ _ _ _ (E.N.D.map f.base.left) (Spec.map f.algHom)
    (E.WD.map f.base) (WD_map_Wι f.base).symm (Stage.toSpec_comp_SpecMap_algHom f)
  map_id T := by
    have hb : (𝟙 T : T ⟶ T).base.left = 𝟙 T.j.left := rfl
    have h2 := Stage.Hom.algHom_id T
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc, hb, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [pushout.inr_desc, h2, Spec.map_id, Category.id_comp, Category.comp_id]
  map_comp {T T' T''} f g := by
    have hb : (f ≫ g).base.left = f.base.left ≫ g.base.left := rfl
    have h2 := Stage.Hom.algHom_comp f g
    refine pushout.hom_ext ?_ ?_
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc, hb, CategoryTheory.Functor.map_comp,
        Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, h2, Spec.map_comp, Category.assoc]

@[simp] lemma stageDiagram_obj (T : E.Stage) :
    E.stageDiagram.obj T = pushout (E.Wι T.j) T.toSpec := rfl

@[reassoc (attr := simp)]
lemma inl_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inl (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      E.N.D.map f.base.left ≫ pushout.inl (E.Wι T'.j) T'.toSpec :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inr (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      Spec.map f.algHom ≫ pushout.inr (E.Wι T'.j) T'.toSpec :=
  pushout.inr_desc _ _ _

@[simp] lemma opensRange_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    (E.Wι j).opensRange = E.N.D.map j.hom ⁻¹ᵁ E.W₀ :=
  Scheme.Opens.opensRange_ι _

/-- (Implementation) The `Wⱼ`-squares of the system of stages are cartesian. -/
lemma isPullback_Wι {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) (E.Wι T.j) (E.Wι T'.j) (E.N.D.map f.base.left) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (WD_map_Wι f.base).symm ?_
  rw [opensRange_Wι, opensRange_Wι, ← Scheme.Hom.comp_preimage, ← E.N.D.map_comp, Over.w f.base]

set_option maxHeartbeats 1600000 in
-- The basic opens of the tautological elements have to be compared through
-- `Spec.map` of the coefficient algebra map, which unfolds the stage structure.
/-- (Implementation) The `Spec A`-squares of the system of stages are cartesian. -/
lemma isPullback_toSpec {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) T.toSpec T'.toSpec (Spec.map f.algHom) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Stage.toSpec_comp_SpecMap_algHom f) ?_
  rw [T.opensRange_toSpec, T'.opensRange_toSpec, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun l ↦ ?_
  rw [SpecMap_preimage_basicOpen]
  congr 1
  refine Subtype.ext ?_
  rw [Stage.Hom.algHom_coe, Stage.coe_h, Stage.coe_h, f.res_r]

lemma isPullback_pushout_inl {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.N.D.map f.base.left) (pushout.inl (E.Wι T.j) T.toSpec)
      (pushout.inl (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inl_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma isPullback_pushout_inr {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (Spec.map f.algHom) (pushout.inr (E.Wι T.j) T.toSpec)
      (pushout.inr (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inr_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

instance (T : E.Stage) : CompactSpace (E.stageDiagram.obj T) :=
  have : CompactSpace (E.N.D.obj T.j.left) := inferInstance
  have : CompactSpace (Spec (CommRingCat.of ↥T.A)) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum ↥T.A))
  inferInstanceAs (CompactSpace ↑(pushout (E.Wι T.j) T.toSpec))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A))) :=
  have : Algebra.FiniteType ℤ ↥T.A := (Subalgebra.fg_iff_finiteType _).mp T.hAfg
  inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of ↥T.A))))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.stageDiagram.obj T)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.stageDiagram.obj T))
    (pushout.desc (specULiftZIsTerminal.from (E.N.D.obj T.j.left))
      (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A)))
      (specULiftZIsTerminal.hom_ext _ _))]
  exact IsZariskiLocalAtSource.pushout_desc (E.Wι T.j) T.toSpec _ inferInstance inferInstance

instance isAffineHom_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    IsAffineHom (E.stageDiagram.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (IsOpenImmersion.pushoutCover (E.Wι T'.j) T'.toSpec)
  rintro (_ | _)
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inl (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inl f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inl f).flip.isoPullback_hom_snd]
    infer_instance
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inr (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inr f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inr f).flip.isoPullback_hom_snd]
    infer_instance

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
