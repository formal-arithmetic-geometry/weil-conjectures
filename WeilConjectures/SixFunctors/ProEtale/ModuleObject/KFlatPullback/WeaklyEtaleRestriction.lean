/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor

/-!
# Acyclic K-flat complexes stay acyclic after weakly étale pullback and tensoring

Let `Λ` be a commutative condensed ring and `v : V ⟶ Y` a weakly étale morphism of schemes. For an
acyclic K-flat complex `C` of `Λ_Y`-modules and a `Λ_V`-module `G`, the complex `v^* C ⊗ G`
(termwise relative tensor product) is acyclic
(`AlgebraicGeometry.ProEtale.CondensedRing.acyclic_tensorRight_upperStar_of_weaklyEtale`).

## The argument

* The extension by zero `v_!` on abelian pro-étale sheaves is faithful
  (`AlgebraicGeometry.ProEtale.faithful_weaklyEtaleLowerShriek`): the unit `H ⟶ v^* v_! H` is a
  monomorphism. On presheaves, the unit `H(W) ⟶ (Lan H)(v W)` of the left Kan extension along the
  localization functor is split injective, a retraction being given by the summand of the lifts
  of `W` agreeing with its structure morphism
  (`AlgebraicGeometry.ProEtale.injective_lanUnit_app_app_overMap`); the unit of sheafification is
  locally injective, and stays so after restriction along the cocontinuous localization functor.
  Hence `v_!` on module objects is faithful as well, and being exact, it reflects acyclicity.
* The pullback `v^*` of module objects commutes with internal homs, as `v^*` on sheaves does and
  the extension of scalars along the isomorphism `α_v` is a monoidal equivalence; hence the
  projection map `v_!(v^* M ⊗ N) ⟶ M ⊗ v_! N` is an isomorphism, naturally in `M`.
* Therefore `v_!(v^* C ⊗ G) ≅ C ⊗ v_! G`, which is acyclic since `C` is acyclic and K-flat
  (`CochainComplex.acyclic_tensorRight_of_kFlat`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {V Y : Scheme.{u}} (v : V ⟶ Y) [WeaklyEtale v]

/-- The unit `F(W) ⟶ (Lan F)(v W)` of the left Kan extension of a presheaf `F` along the
localization functor of a weakly étale `v : V ⟶ Y` is injective: a retraction is given on the
component of a lift `W ⟶ Z` of `W` by restriction along it if it is a morphism over `V`, and by
zero otherwise. -/
lemma injective_lanUnit_app_app_overMap (F : V.ProEtᵒᵖ ⥤ Ab.{u + 1}) (W : V.ProEt) :
    Function.Injective (((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale v)).op.lanUnit.app F).app (op W)) := by
  classical
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale v)
  let hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension (G.op.lan.obj F)
    (G.op.lanUnit.app F) (op (G.obj W))
  let s : Cocone (CostructuredArrow.proj G.op (op (G.obj W)) ⋙ F) :=
    { pt := F.obj (op W)
      ι :=
        { app j := if h : j.hom.unop.left ≫ j.left.unop.hom = W.hom then
              F.map (MorphismProperty.Over.homMk (A := W) (B := j.left.unop) j.hom.unop.left h
                trivial).op
            else 0
          naturality j j' φ := by
            have hφ : j.hom.unop.left = j'.hom.unop.left ≫ φ.left.unop.left := by
              have := congrArg (fun f ↦ f.unop.left) (CostructuredArrow.w φ)
              exact this.symm
            have hw : φ.left.unop.left ≫ j.left.unop.hom = j'.left.unop.hom :=
              MorphismProperty.Over.w φ.left.unop
            have hiff : j.hom.unop.left ≫ j.left.unop.hom = W.hom ↔
                j'.hom.unop.left ≫ j'.left.unop.hom = W.hom := by
              rw [hφ, Category.assoc, hw]
            dsimp
            by_cases h' : j'.hom.unop.left ≫ (unop j'.left).hom = W.hom
            · rw [dif_pos h', dif_pos (hiff.2 h'), Category.comp_id, ← F.map_comp]
              congr 1
              apply Quiver.Hom.unop_inj
              ext
              simp [hφ]
            · rw [dif_neg h', dif_neg (fun h ↦ h' (hiff.1 h))]
              simp } }
  have key : (G.op.lanUnit.app F).app (op W) ≫ hc.desc s = 𝟙 _ := by
    have h := hc.fac s (CostructuredArrow.mk (Y := op W) (𝟙 (G.op.obj (op W))))
    simp [s] at h
    refine h.trans (Eq.trans ?_ (F.map_id (op W)))
    congr 1
  intro a b hab
  have ha := ConcreteCategory.congr_hom key a
  have hb := ConcreteCategory.congr_hom key b
  simp only [ConcreteCategory.comp_apply] at ha hb
  have hab' := congrArg (hc.desc s).hom hab
  exact (ha.symm.trans hab').trans hb

/-- The unit `H ⟶ v^* v_! H` of the extension by zero along a weakly étale morphism is a
monomorphism. -/
instance mono_weaklyEtaleLowerShriekAdjunction_unit_app
    (H : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) :
    Mono ((weaklyEtaleLowerShriekAdjunction Ab.{u + 1} v).unit.app H) := by
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale v)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1}
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology Y)
  have e : (adj.unit.app H).hom = G.op.lanUnit.app H.obj ≫
      Functor.whiskerLeft G.op (toSheafify (Scheme.ProEt.topology Y) (G.op.lan.obj H.obj)) := by
    have := Adjunction.map_restrictFullyFaithful_unit_app
      (L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1}
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology Y))
      (R := G.sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology Y))
      ((G.op.lanAdjunction Ab.{u + 1}).comp
      (sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}))
      (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) H
    simp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at this
    exact this
  have : Presheaf.IsLocallyInjective (Scheme.ProEt.topology V) (adj.unit.app H).hom := by
    rw [e]
    have : Presheaf.IsLocallyInjective (Scheme.ProEt.topology V) (G.op.lanUnit.app H.obj) :=
      Presheaf.isLocallyInjective_of_injective _ _ fun W ↦
        injective_lanUnit_app_app_overMap v H.obj W.unop
    have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale v)).IsCocontinuous
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology Y) := inferInstance
    have := Presheaf.isLocallyInjective_whisker (Scheme.ProEt.topology V)
      (Scheme.ProEt.topology Y) (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale v))
      (toSheafify (Scheme.ProEt.topology Y) (G.op.lan.obj H.obj))
    exact Presheaf.isLocallyInjective_comp _ _ _
  have := Sheaf.mono_of_isLocallyInjective (adj.unit.app H)
  simpa [weaklyEtaleLowerShriekAdjunction] using this

/-- The extension by zero along a weakly étale morphism is faithful. -/
instance faithful_weaklyEtaleLowerShriek : (weaklyEtaleLowerShriek Ab.{u + 1} v).Faithful :=
  (weaklyEtaleLowerShriekAdjunction Ab.{u + 1} v).faithful_L_of_mono_unit_app

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The extension by zero on module objects along a weakly étale morphism is faithful. -/
instance faithful_weaklyEtaleLowerShriek : (weaklyEtaleLowerShriek Λ v).Faithful := by
  have : (weaklyEtaleLowerShriek Λ v ⋙ Mod.forget (condensedRingObj Λ Y)).Faithful := by
    rw [weaklyEtaleLowerShriek_comp_forget]
    infer_instance
  exact Functor.Faithful.of_comp _ (Mod.forget _)

omit [IsCommMonObj Λ] in
/-- The extension by zero along a weakly étale morphism reflects acyclicity of complexes of
module objects, being exact and faithful. -/
lemma acyclic_of_acyclic_mapHomologicalComplex_weaklyEtaleLowerShriek
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V)) ℤ)
    (hK : (((weaklyEtaleLowerShriek Λ v).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  intro n
  have h := hK n
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact (ShortComplex.exact_map_iff_of_faithful _ (weaklyEtaleLowerShriek Λ v)).1 h

/-- The extension of scalars along the isomorphism `α_v : v^* Λ_Y ⟶ Λ_V` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom_of_weaklyEtale :
    (Mod.extendScalars (condensedPullbackHom Λ v)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ v)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ v)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ v)).symm

/-- The pullback of module objects along a weakly étale morphism commutes with internal homs. -/
instance isIso_ihomComparison_upperStar_of_weaklyEtale
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (Functor.LaxMonoidal.ihomComparison (v)^*⟦Λ⟧ M).natTrans := by
  have := fun Z ↦ ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} v Z
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  erw [Functor.LaxMonoidal.ihomComparison_comp_app ((v)^*[Ab.{u + 1}].mapMod _)
    (Mod.extendScalars (condensedPullbackHom Λ v))]
  infer_instance

/-- **The projection formula on module objects for a weakly étale morphism**: the projection
map `v_!(v^* M ⊗ N) ⟶ M ⊗ v_! N` is an isomorphism. -/
instance isIso_projectionMap_weaklyEtaleLowerShriekUpperStarAdjunction
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (Functor.Monoidal.projectionMap (weaklyEtaleLowerShriekUpperStarAdjunction Λ v) M) :=
  Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ M

/-- **Weakly étale pullback and tensoring preserve acyclic K-flat complexes.** For an acyclic
K-flat complex `C` of `Λ_Y`-modules and a `Λ_V`-module `G`, the complex `v^* C ⊗ G` is acyclic:
its extension by zero is `C ⊗ v_! G` by the projection formula, and `v_!` reflects acyclicity. -/
theorem acyclic_tensorRight_upperStar_of_weaklyEtale
    (C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (G : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (((tensorRight G).mapHomologicalComplex (.up ℤ)).obj
      (((v)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj C)).Acyclic := by
  refine acyclic_of_acyclic_mapHomologicalComplex_weaklyEtaleLowerShriek v Λ _ fun n ↦ ?_
  let adj := weaklyEtaleLowerShriekUpperStarAdjunction Λ v
  let e : ((weaklyEtaleLowerShriek Λ v).mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight G).mapHomologicalComplex (.up ℤ)).obj
        (((v)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj C)) ≅
      ((tensorRight ((weaklyEtaleLowerShriek Λ v).obj G)).mapHomologicalComplex (.up ℤ)).obj C :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ asIso ((Functor.Monoidal.projectionMap adj (C.X n)).app G))
      (fun i j _ ↦ by
        simpa using (Functor.Monoidal.projectionMap_naturality_left adj (C.d i j) G).symm)
  exact (CochainComplex.acyclic_tensorRight_of_kFlat C hC' hC _ n).of_iso e.symm

end CondensedRing

end AlgebraicGeometry.ProEtale
