/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-! # The injective-coproduct form of finite-dimensional derived continuity -/

@[expose] public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Functor

set_option autoImplicit false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- Finite cohomological dimension and acyclicity of sums of injectives suffice for
unbounded derived coproduct preservation. Source: the abstract argument of
Stacks Project, Tag 0F11, with its injective-sum acyclicity isolated as a hypothesis.
(blueprint: stage3-finite-cd-injective-coproducts).

Proof: Choose K-injective representatives with injective components for each member
of the family. Their termwise coproduct represents the derived coproduct because
direct sums in the source Grothendieck category are exact. Every component of this
sum is F-acyclic by hypothesis. Finite cohomological dimension makes the canonical
derived-functor comparison invertible on any complex of F-acyclic objects, without
a lower bound. Compare these canonical maps on the individual representatives and
their sum. Underived F preserves the termwise coproduct; naturality on each
coprojection transports its universal property to the derived image. -/
theorem preservesColimitsOfShape_rightDerivedFunctor_of_injectiveCoproducts
    [IsGrothendieckAbelian.{w} C]
    [HasInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hJ : ∀ X : J → C, (∀ j, Injective (X j)) → F.rightAcyclic (∐ X)) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor where
  preservesColimit {G} := by
    let I (j : J) := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj
      (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩))
    have hι (j : J) : IsIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w}
        C).app (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩)))) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
        ((CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C _).2)
    let e : Discrete.functor (fun j ↦ DerivedCategory.Q.obj (I j)) ≅ G :=
      Discrete.natIso fun j ↦ (asIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{w} C).app
          (DerivedCategory.Q.objPreimage (G.obj ⟨j.as⟩))))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso _
    suffices PreservesColimit (Discrete.functor fun j ↦ DerivedCategory.Q.obj (I j))
        F.rightDerivedFunctor from preservesColimit_of_iso_diagram _ e
    -- K-injective representatives have injective components.
    have hinj (j : J) (n : ℤ) : Injective ((I j).X n) :=
      CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} _ n
    -- the coproduct of the complexes `I j` is a complex of `F`-acyclic objects
    have hP (n : ℤ) : F.rightAcyclic ((∐ I).X n) :=
      F.rightAcyclic.prop_of_iso
        (PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) I).symm
        (hJ _ fun j ↦ hinj j n)
    -- the comparison maps `F(K) ⟶ RF(K)`, natural in `K`
    let v (K : CochainComplex C ℤ) : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) ⟶
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)
    have nat {K L : CochainComplex C ℤ} (f : K ⟶ L) :
        DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f) ≫ v L =
          v K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
      have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
      simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
      simp only [v, DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
      rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
        DerivedCategory.quotientCompQhIso_hom_naturality]
    have hv (K : CochainComplex C ℤ) (hK : ∀ n, F.rightAcyclic (K.X n)) : IsIso (v K) := by
      have := F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic d hF K hK
      dsimp only [v]
      infer_instance
    have hu (j : J) : IsIso (v (I j)) :=
      hv _ fun n ↦ have := hinj j n; rightAcyclic_of_injective _
    have huP : IsIso (v (∐ I)) := hv _ hP
    -- the image under `F` of the coproduct cofan is a coproduct in `D(D)`
    have hFc : IsColimit (Cofan.mk (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ I)))
        fun j ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι I j))) :=
      DerivedCategory.isColimitCofanMkQObj
        ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) I (Sigma.ι I)).1
          (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct I)))
    refine preservesColimit_of_preserves_colimit_cocone
      (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct I))
      ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
    refine (IsColimit.equivOfNatIsoOfIso (Discrete.natIso fun j ↦ asIso (v (I j.as))) _ _
      (Cocone.ext (asIso (v (∐ I))) fun j ↦ ?_)) hFc
    dsimp
    rw [Category.assoc, nat]
    simp

end CategoryTheory.Functor
