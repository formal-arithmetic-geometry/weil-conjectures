/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective

/-! # Morphisms from the coefficient unit under derived point sections

Source: latest blueprint, the global-sections adjunction in def-trf-trace-class
(blueprint: lem-trf-point-unit-sections-bijective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe w v u w' v' u'

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem homology_map_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (n : ℤ) (N : DerivedCategory C) :
    Function.Bijective (fun f : (singleFunctor C n).obj P ⟶ N ↦
      (homologyFunctor C n).map f) := by
  let e := (singleFunctorCompHomologyFunctorIso C n).app P
  constructor
  · intro f g h
    apply (homSingleEquivOfProjective P n N).injective
    change e.inv ≫ (homologyFunctor C n).map f =
      e.inv ≫ (homologyFunctor C n).map g
    exact congrArg (e.inv ≫ ·) h
  · intro h
    obtain ⟨f, hf⟩ := (homSingleEquivOfProjective P n N).surjective (e.inv ≫ h)
    refine ⟨f, ?_⟩
    apply (cancel_epi e.inv).1
    exact hf

private theorem homology_map_bijective_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (n : ℤ) (U N : DerivedCategory C)
    (e : U ≅ (singleFunctor C n).obj P) :
    Function.Bijective (fun f : U ⟶ N ↦ (homologyFunctor C n).map f) := by
  have h := homology_map_bijective P n N
  constructor
  · intro f g hfg
    have : e.inv ≫ f = e.inv ≫ g := h.1 (by simp only [Functor.map_comp, hfg])
    exact (cancel_epi e.inv).1 this
  · intro f
    obtain ⟨g, hg⟩ := h.2 ((homologyFunctor C n).map e.inv ≫ f)
    dsimp only at hg
    refine ⟨e.hom ≫ g, ?_⟩
    dsimp only
    rw [Functor.map_comp, hg, ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem map_bijective_of_source_iso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (P U N : C) (e : U ≅ P)
    (h : Function.Bijective (fun f : P ⟶ N ↦ F.map f)) :
    Function.Bijective (fun f : U ⟶ N ↦ F.map f) := by
  constructor
  · intro f g hfg
    have : e.inv ≫ f = e.inv ≫ g := h.1 (by simp only [Functor.map_comp, hfg])
    exact (cancel_epi e.inv).1 this
  · intro f
    obtain ⟨g, hg⟩ := h.2 (F.map e.inv ≫ f)
    dsimp only at hg
    refine ⟨e.hom ≫ g, ?_⟩
    dsimp only
    rw [Functor.map_comp, hg, ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem exact_derived_map_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : C) [Projective P] [Projective (F.obj P)]
    (hF : ∀ M, Function.Bijective (fun f : P ⟶ M ↦ F.map f))
    (N : DerivedCategory C) :
    Function.Bijective (fun f : (singleFunctor C 0).obj P ⟶ N ↦
      F.mapDerivedCategory.map f) := by
  let U := (singleFunctor C 0).obj P
  let HC := homologyFunctor C 0
  let HD := homologyFunctor D 0
  let E := F.mapDerivedCategoryHomologyFunctorIso 0
  have hC := homology_map_bijective P 0 N
  have hD := homology_map_bijective_iso (F.obj P) 0
    (F.mapDerivedCategory.obj U) (F.mapDerivedCategory.obj N)
    ((F.mapDerivedCategorySingleFunctor 0).app P)
  have hH := map_bijective_of_source_iso F P (HC.obj U) (HC.obj N)
    ((singleFunctorCompHomologyFunctorIso C 0).app P) (hF (HC.obj N))
  have hn (f : U ⟶ N) :
      F.map (HC.map f) ≫ E.hom.app N =
        E.hom.app U ≫ HD.map (F.mapDerivedCategory.map f) := E.hom.naturality f
  constructor
  · intro f g hfg
    dsimp only at hfg
    apply hC.1
    apply hH.1
    apply (cancel_mono (E.hom.app N)).1
    rw [hn, hn, hfg]
  · intro f
    obtain ⟨h, hh⟩ := hH.2
      (E.hom.app U ≫ HD.map f ≫ E.inv.app N)
    obtain ⟨g, hg⟩ := hC.2 h
    change HC.map g = h at hg
    change F.map h = _ at hh
    refine ⟨g, hD.1 ?_⟩
    change HD.map (F.mapDerivedCategory.map g) = HD.map f
    apply (cancel_epi (E.hom.app U)).1
    rw [← hn, hg, hh]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
      NatIso.cancel_natIso_hom_left]
    exact Category.comp_id _

private theorem coyoneda_map_bijective
    {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type v} [CommRing R] (P : C) (c : R →+* (End P)ᵐᵒᵖ)
    (hc : Function.Surjective (fun a ↦ (c a).unop)) (M : C) :
    Function.Bijective (fun f : P ⟶ M ↦ (coyonedaSections c).map f) := by
  constructor
  · intro f g h
    have := congrArg (fun q ↦ q (𝟙 P)) h
    change 𝟙 P ≫ f = 𝟙 P ≫ g at this
    simpa using this
  · intro g
    refine ⟨g (𝟙 P), ?_⟩
    ext t
    obtain ⟨a, rfl⟩ := hc t
    change (c a).unop ≫ g (𝟙 P) = g ((c a).unop)
    have h := g.hom.map_smul a (𝟙 P)
    simpa only [coyonedaSections_smul, Category.comp_id] using h.symm

open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

private theorem point_scalar_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k] :
    Function.Bijective (fun a : MonObj.Γ Λ ↦
      Mod.regularEndRingHom (condensedRingScalarSections Λ (Spec (.of k)) a)) := by
  let F := upperStarFromPoint (Spec (.of k))
  have : F.IsEquivalence := inferInstance
  have : PreservesColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  exact F.bijective_regularEndRingHom_comp_mapFunctor Λ
    (Functor.FullyFaithful.ofFullyFaithful _)

private theorem point_sections_unit_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k] :
    Function.Bijective (LinearMap.toSpanSingleton (MonObj.Γ Λ)
      ((condensedRingCoefficientSections Λ (Spec (.of k))).obj
        (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ) (𝟙 _)) := by
  have heq : ⇑(LinearMap.toSpanSingleton (MonObj.Γ Λ)
      ((condensedRingCoefficientSections Λ (Spec (.of k))).obj
        (Mod.regular (condensedRingObj Λ (Spec (.of k))))) (𝟙 _)) =
      (fun a ↦ Mod.regularEndRingHom
        (condensedRingScalarSections Λ (Spec (.of k)) a)) := by
    funext a
    change Mod.regularEndRingHom _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [heq]
  exact point_scalar_bijective Λ k

private theorem map_bijective_of_natIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F G : C ⥤ D) (e : G ≅ F) (U N : C)
    (h : Function.Bijective (fun f : U ⟶ N ↦ F.map f)) :
    Function.Bijective (fun f : U ⟶ N ↦ G.map f) := by
  have heq : (fun f : U ⟶ N ↦ G.map f) =
      ⇑((e.app U).symm.homCongr (e.app N).symm) ∘ (fun f : U ⟶ N ↦ F.map f) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom]
    change G.map f = e.hom.app U ≫ F.map f ≫ e.inv.app N
    rw [← e.hom.naturality_assoc]
    simp
  rw [heq]
  exact ((e.app U).symm.homCongr (e.app N).symm).bijective.comp h

/-- Actual derived point sections are bijective on maps from the regular coefficient unit.

Source: the global-sections adjunction identifying the trace class in
literature/blueprint/latest/blueprint/sec-trace-formula/sk-d-pairing/def-trf-trace-class.md
(blueprint: lem-trf-point-unit-sections-bijective).

Proof: the regular coefficient module P is projective at a separably closed point.
Pullback of condensed modules to that point is fully faithful, so global scalars give
all endomorphisms of P. Thus the identity is a basis of its scalar section module F(P).
Evaluation at that identity makes f ↦ F(f) bijective on maps from P. Both P and F(P)
are projective. Maps from their degree-zero complexes are therefore detected and
exhausted by degree-zero homology. Exactness of F and naturality of its canonical
homology comparison transfer the ordinary-map bijection to termwise derivation.
Finally conjugate by the canonical comparison from total right derivation to termwise
derivation. This proves the specified map, for arbitrary unbounded targets.
-/
theorem finite_point_unit_sections_map_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k]
    [HasDerivedCategory.{w} (Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))]
    [HasDerivedCategory.{w'} (ModuleCat.{u + 1} (MonObj.Γ Λ))]
    (N : DerivedCategory.{w} (Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))) :
    Function.Bijective (fun f :
      (singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ⟶ N ↦
      ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor :
        DerivedCategory.{w} (Mod
          (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))) ⥤
          DerivedCategory.{w'} (ModuleCat.{u + 1} (MonObj.Γ Λ))).map f) := by
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  let P := Mod.regular (condensedRingObj Λ (Spec (.of k)))
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  let e : ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ) ≅ F.obj P :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton (MonObj.Γ Λ) (F.obj P) (show F.obj P from 𝟙 P))
      (point_sections_unit_bijective Λ k)).toModuleIso
  have : Projective (F.obj P) := Projective.of_iso e inferInstance
  have hc := point_scalar_bijective Λ k
  have hF (M) : Function.Bijective (fun f : P ⟶ M ↦ F.map f) :=
    coyoneda_map_bijective P _ hc.2 M
  have h := exact_derived_map_bijective F P hF N
  exact map_bijective_of_natIso F.mapDerivedCategory F.rightDerivedFunctor
    F.rightDerivedFunctorIsoMapDerivedCategory _ N h

end AlgebraicGeometry.ProEtale.CondensedRing
