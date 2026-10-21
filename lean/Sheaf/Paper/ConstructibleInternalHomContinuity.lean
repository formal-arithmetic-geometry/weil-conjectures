/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import all Sheaf.Algebra.Homology.RHomContinuityTriangleClosure
import Sheaf.Paper.BoundedFiniteModelGeneration
import Sheaf.Paper.FiniteLocalModelRHomContinuity
import all Sheaf.Paper.ClosedSupportBoundedContinuity
import Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.Paper.CartesianCoefficients

/-!
# Continuity of constructible-source derived internal Hom

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.8.12,
6.3.14 and the local support argument of 6.7.13. The internal filtered-colimit
assertion is the additional local devissage claim of the DAG, rather than the
verbatim global direct-sum assertion of the paper
(blueprint: lem-sfb-constructible-internal-hom-continuity).

We use the equivalent formulation on every cohomology module sheaf. The cocone
is obtained by applying localization, the recorded closed derived internal Hom,
and cohomology to the actual termwise-colimit cocone. Thus its legs are the
canonical evaluation-induced maps, and no complex representative is chosen.
-/

@[expose] public section

set_option autoImplicit false
-- This module has the public theorem below; scanning imported private helpers is unnecessary.
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

universe a b d v w

attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.homComplexFunctor CategoryTheory.derivedInternalHomOfUniverses
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  HasDerivedCategory.ofIsGrothendieckAbelian

private def HomContinuous
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{w} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) : Prop :=
  ∀ (I : Type v) [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CochainComplex A ℤ) (c : ℤ),
    (∀ i, (DerivedCategory.Q.obj (M.obj i)).IsGE c) →
    ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q).mapCocone
        (colimit.cocone M)))

private theorem continuous_iso
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{w} B] [Abelian B] [HasDerivedCategory.{w} B]
    {F G : DerivedCategory A ⥤ DerivedCategory B} (e : F ≅ G)
    (hF : HomContinuous F) : HomContinuous G := by
  intro I _ _ M c hM q
  obtain ⟨hc⟩ := hF I M c hM q
  exact ⟨IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor B q))) hc⟩

private theorem continuous_post_iff
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    [IsGrothendieckAbelian.{v} B] (F : DerivedCategory A ⥤ DerivedCategory B) :
    HomContinuous F ↔
      ∀ (I : Type v) [SmallCategory I] [IsFiltered I]
        (M : I ⥤ CochainComplex A ℤ) (c : ℤ),
        (∀ i, (DerivedCategory.Q.obj (M.obj i)).IsGE c) → ∀ q : ℤ,
        IsIso (colimit.post M
          (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)) := by
  constructor
  · intro h I _ _ M c hM q
    exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1 (h I M c hM q)
  · intro h I _ _ M c hM q
    exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (h I M c hM q)

private theorem continuous_precomp
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    [IsGrothendieckAbelian.{v} B]
    {D : Type d} [Category.{v} D] [Abelian D] [HasDerivedCategory.{v} D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesColimitsOfSize.{v, v} F]
    {G : DerivedCategory B ⥤ DerivedCategory D}
    (hG : HomContinuous G) : HomContinuous (F.mapDerivedCategory ⋙ G) := by
  intro I _ _ M c hM q
  let E := F.mapHomologicalComplex (.up ℤ)
  have hE (i : I) : (DerivedCategory.Q.obj ((M ⋙ E).obj i)).IsGE c := by
    let := hM i
    let hFC : (F.mapDerivedCategory.obj (DerivedCategory.Q.obj (M.obj i))).IsGE c :=
      F.isGE_mapDerivedCategory_obj (DerivedCategory.Q.obj (M.obj i)) c
    have : DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.Q ⋙ F.mapDerivedCategory).obj (M.obj i)) c := hFC
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (F.mapDerivedCategoryFactors.app (M.obj i)) c
  obtain ⟨hc⟩ := hG I (M ⋙ E) c hE q
  let H := DerivedCategory.Q ⋙ G ⋙ DerivedCategory.homologyFunctor D q
  have hp : PreservesColimit (M ⋙ E) H :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit _) hc
  have hc' : IsColimit ((E ⋙ H).mapCocone (colimit.cocone M)) :=
    isColimitOfPreserves H (isColimitOfPreserves E (colimit.isColimit M))
  exact ⟨IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm
      (G ⋙ DerivedCategory.homologyFunctor D q)) hc'⟩

private theorem continuous_postcomp
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    {D : Type d} [Category.{v} D] [Abelian D] [HasDerivedCategory.{v} D]
    [IsGrothendieckAbelian.{v} D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesColimitsOfSize.{v, v} F]
    {G : DerivedCategory D ⥤ DerivedCategory A}
    (hG : HomContinuous G) : HomContinuous (G ⋙ F.mapDerivedCategory) := by
  intro I _ _ M c hM q
  obtain ⟨hc⟩ := hG I M c hM q
  exact ⟨IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerLeft (DerivedCategory.Q ⋙ G)
      (F.mapDerivedCategoryHomologyFunctorIso q))
    (isColimitOfPreserves F hc)⟩

private theorem continuous_model_iff
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    [IsGrothendieckAbelian.{v} B]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (E : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (e : DerivedCategory.Q ⋙ F ≅ E ⋙ DerivedCategory.Q) :
    HomContinuous F ↔
      ∀ (I : Type v) [SmallCategory I] [IsFiltered I]
        (M : I ⥤ CochainComplex A ℤ) (c : ℤ),
        (∀ i, (DerivedCategory.Q.obj (M.obj i)).IsGE c) →
        IsIso (DerivedCategory.Q.map (colimit.post M E)) := by
  constructor
  · intro h I _ _ M c hM
    rw [DerivedCategory.isIso_iff]
    intro q
    let H := DerivedCategory.homologyFunctor B q
    have := complexHomologyPreserves (A := B) I q
    have : PreservesColimitsOfShape I (DerivedCategory.Q ⋙ H) :=
      preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors B q).symm
    have : IsIso (colimit.post M ((DerivedCategory.Q ⋙ F) ⋙ H)) :=
      (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1 (h I M c hM q)
    have hp : IsIso (colimit.post M (E ⋙ (DerivedCategory.Q ⋙ H))) :=
      post_isIso_natIso _ _ (Functor.isoWhiskerRight e H) M
    change IsIso (colimit.post M (E ⋙ (DerivedCategory.Q ⋙ H))) at hp
    rw [← colimit.post_post M E (DerivedCategory.Q ⋙ H)] at hp
    exact (isIso_comp_left_iff _ _).mp hp
  · intro h I _ _ M c hM q
    let H := DerivedCategory.homologyFunctor B q
    have := complexHomologyPreserves (A := B) I q
    have : PreservesColimitsOfShape I (DerivedCategory.Q ⋙ H) :=
      preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors B q).symm
    have := h I M c hM
    have : IsIso (colimit.post M ((E ⋙ DerivedCategory.Q) ⋙ H)) := by
      change IsIso (colimit.post M (E ⋙ (DerivedCategory.Q ⋙ H)))
      rw [← colimit.post_post M E (DerivedCategory.Q ⋙ H)]
      have : IsIso ((DerivedCategory.Q ⋙ H).map (colimit.post M E)) :=
        inferInstanceAs (IsIso (H.map (DerivedCategory.Q.map (colimit.post M E))))
      infer_instance
    have := post_isIso_natIso _ _ (Functor.isoWhiskerRight e.symm H) M
    exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 this

private theorem continuous_comp_model
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    [IsGrothendieckAbelian.{v} B]
    {D : Type d} [Category.{v} D] [Abelian D] [HasDerivedCategory.{v} D]
    [IsGrothendieckAbelian.{v} D]
    (F : DerivedCategory A ⥤ DerivedCategory B) (G : DerivedCategory B ⥤ DerivedCategory D)
    (E : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (e : DerivedCategory.Q ⋙ F ≅ E ⋙ DerivedCategory.Q)
    (hF : HomContinuous F) (hG : HomContinuous G) (d : ℤ)
    (hb : ∀ (N : DerivedCategory A) (c : ℤ), N.IsGE c → (F.obj N).IsGE (c + d)) :
    HomContinuous (F ⋙ G) := by
  intro I _ _ M c hM q
  let H := DerivedCategory.Q ⋙ G ⋙ DerivedCategory.homologyFunctor D q
  have hE (i : I) : (DerivedCategory.Q.obj ((M ⋙ E).obj i)).IsGE (c + d) := by
    let hFC : (F.obj (DerivedCategory.Q.obj (M.obj i))).IsGE (c + d) :=
      hb _ c (hM i)
    have : DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.Q ⋙ F).obj (M.obj i)) (c + d) := hFC
    exact DerivedCategory.TStructure.t.isGE_of_iso (e.app (M.obj i)) _
  have hp := (continuous_model_iff F E e).mp hF I M c hM
  have hq : IsIso (colimit.post (M ⋙ E) H) :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
      (hG I (M ⋙ E) (c + d) hE q)
  have : IsIso (colimit.post M (E ⋙ H)) := by
    rw [← colimit.post_post M E H]
    have : IsIso (H.map (colimit.post M E)) :=
      inferInstanceAs (IsIso ((G ⋙ DerivedCategory.homologyFunctor D q).map
        (DerivedCategory.Q.map (colimit.post M E))))
    infer_instance
  have hs : IsIso (colimit.post M
      ((E ⋙ DerivedCategory.Q) ⋙ (G ⋙ DerivedCategory.homologyFunctor D q))) := this
  have := post_isIso_natIso _ _
    (Functor.isoWhiskerRight e.symm (G ⋙ DerivedCategory.homologyFunctor D q)) M
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 this

private theorem continuous_reflect_postcomp
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    {F : A ⥤ B} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsEquivalence] {G : DerivedCategory A ⥤ DerivedCategory A}
    (h : HomContinuous (G ⋙ F.mapDerivedCategory)) : HomContinuous G := by
  intro I _ _ M c hM q
  obtain ⟨hc⟩ := h I M c hM q
  have hc' := IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerLeft (DerivedCategory.Q ⋙ G)
      (F.mapDerivedCategoryHomologyFunctorIso q).symm) hc
  exact ⟨isColimitOfReflects F hc'⟩

private theorem continuous_equivalence_iff
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    [IsGrothendieckAbelian.{v} B]
    (E : A ≌ B) [E.functor.Additive] [E.inverse.Additive]
    (F : DerivedCategory A ⥤ DerivedCategory A)
    (G : DerivedCategory B ⥤ DerivedCategory B)
    (e : F ⋙ E.functor.mapDerivedCategory ≅ E.functor.mapDerivedCategory ⋙ G) :
    HomContinuous F ↔ HomContinuous G := by
  constructor
  · intro h
    have h' := continuous_iso e (continuous_postcomp E.functor h)
    have h'' := continuous_precomp E.inverse h'
    exact continuous_iso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E.mapDerivedCategory.counitIso G ≪≫ Functor.leftUnitor G) h''
  · intro h
    exact continuous_reflect_postcomp
      (continuous_iso e.symm (continuous_precomp E.functor h))

private theorem bound_equivalence_iff
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    {B : Type b} [Category.{v} B] [Abelian B] [HasDerivedCategory.{v} B]
    (E : A ≌ B) [E.functor.Additive] [E.inverse.Additive]
    (F : DerivedCategory A ⥤ DerivedCategory A)
    (G : DerivedCategory B ⥤ DerivedCategory B)
    (e : F ⋙ E.functor.mapDerivedCategory ≅ E.functor.mapDerivedCategory ⋙ G) :
    (∃ d : ℤ, ∀ c N, N.IsGE c → (F.obj N).IsGE (c + d)) ↔
    (∃ d : ℤ, ∀ c N, N.IsGE c → (G.obj N).IsGE (c + d)) := by
  let D := E.mapDerivedCategory
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, fun c N hN ↦ ?_⟩
    have := hN
    have hN' := E.inverse.isGE_mapDerivedCategory_obj N c
    have := hd c (D.inverse.obj N) hN'
    have hFE := E.functor.isGE_mapDerivedCategory_obj (F.obj (D.inverse.obj N)) (c + d)
    have : DerivedCategory.TStructure.t.IsGE
        ((F ⋙ E.functor.mapDerivedCategory).obj (D.inverse.obj N)) (c + d) := hFE
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (e.app (D.inverse.obj N) ≪≫ G.mapIso (D.counitIso.app N)) (c + d)
  · rintro ⟨d, hd⟩
    refine ⟨d, fun c N hN ↦ ?_⟩
    have := hN
    have hN' := E.functor.isGE_mapDerivedCategory_obj N c
    have hGN := hd c (D.functor.obj N) hN'
    have : DerivedCategory.TStructure.t.IsGE
        ((E.functor.mapDerivedCategory ⋙ G).obj N) (c + d) := hGN
    have hFN := DerivedCategory.TStructure.t.isGE_of_iso (e.app N).symm (c + d)
    have : (D.functor.obj (F.obj N)).IsGE (c + d) := hFN
    have hFI := E.inverse.isGE_mapDerivedCategory_obj (D.functor.obj (F.obj N)) (c + d)
    have : DerivedCategory.TStructure.t.IsGE
        ((D.functor ⋙ D.inverse).obj (F.obj N)) (c + d) := hFI
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (D.unitIso.symm.app (F.obj N)) (c + d)

private theorem nonemptyFourth
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*} {D : Sort*}
    {P : ∀ a b, C a b → D → Prop} (h : ∃ a b c d, P a b c d) : Nonempty D := by
  obtain ⟨a, b, c, d, _⟩ := h
  exact ⟨d⟩

private theorem fixedSourceComparison
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (H : Cᵒᵖ ⥤ C ⥤ C) (G : Dᵒᵖ × D ⥤ D) (F : C ⥤ D)
    (e : Functor.uncurry.obj H ⋙ F ≅ (F.op.prod F) ⋙ G) (K : C) :
    Nonempty (H.obj (Opposite.op K) ⋙ F ≅
      F ⋙ (Functor.curry.obj G).obj (Opposite.op (F.obj K))) := by
  refine ⟨NatIso.ofComponents (fun N ↦ e.app (Opposite.op K, N)) ?_⟩
  intro N N' f
  have hn := e.hom.naturality (Prod.mkHom (𝟙 (Opposite.op K)) f)
  change F.map ((H.map (𝟙 (Opposite.op K))).app N ≫
      (H.obj (Opposite.op K)).map f) ≫ e.hom.app (Opposite.op K, N') =
    e.hom.app (Opposite.op K, N) ≫
      G.map (Prod.mkHom ((F.map (𝟙 K)).op) (F.map f)) at hn
  simpa only [H.map_id, NatTrans.id_app, Category.id_comp, F.map_id, op_id,
    Functor.comp_map, Iso.app_hom, Functor.curry_obj_obj_map] using hn

private noncomputable def closedFormulaIso
    {A : Type a} [Category.{v} A] {B : Type b} [Category.{w} B]
    (H : Aᵒᵖ ⥤ A ⥤ A) (G : Bᵒᵖ ⥤ B ⥤ B) (push : B ⥤ A) (pull : A ⥤ B)
    (z : ∀ (P : B) (N : A), (H.obj (Opposite.op (push.obj P))).obj N ≅
      push.obj ((G.obj (Opposite.op P)).obj (pull.obj N)))
    (hz : ∀ (P P' : B) (N N' : A) (a : P' ⟶ P) (b : N ⟶ N'),
      ((H.map (push.map a).op).app N ≫ (H.obj (Opposite.op (push.obj P'))).map b) ≫
        (z P' N').hom =
      (z P N).hom ≫ push.map ((G.map a.op).app (pull.obj N) ≫
        (G.obj (Opposite.op P')).map (pull.map b)))
    (P : B) : H.obj (Opposite.op (push.obj P)) ≅
      pull ⋙ G.obj (Opposite.op P) ⋙ push :=
  NatIso.ofComponents (z P) (by
    intro N N' f
    simpa only [push.map_id, op_id, H.map_id, G.map_id, NatTrans.id_app,
      Category.id_comp, Functor.comp_map] using hz P P N N' (𝟙 P) f)

namespace AlgebraicGeometry.ProEtale

private noncomputable instance ringedModulesDerived
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1}
      (CategoryTheory.RingedHomUniverses.Modules.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ModuleObjectRingedComparison.ring Λ.X X)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

open ModuleObjectRingedComparison in
private theorem nativeHomComparison
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory (Internal Λ.X X)) :
    Nonempty ((CondensedRing.derivedHom Λ.X X).obj (Opposite.op K) ⋙ forward Λ.X X ≅
      forward Λ.X X ⋙ CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ.X X) ((forward Λ.X X).obj K)) := by
  obtain ⟨θ⟩ := nonemptyFourth (moduleObject_ringedSite_derived_comparison Λ.X X)
  exact fixedSourceComparison _ _ _ θ K

private structure NativeContinuous
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory (CondensedRing.supportModules Λ.X X)) : Prop where
  continuity : HomContinuous ((CondensedRing.derivedHom Λ.X X).obj (Opposite.op K))
  bounded : ∃ d : ℤ, ∀ (c : ℤ) (N : DerivedCategory (CondensedRing.supportModules Λ.X X)),
    N.IsGE c → (((CondensedRing.derivedHom Λ.X X).obj (Opposite.op K)).obj N).IsGE (c + d)

open ModuleObjectRingedComparison CategoryTheory.RingedHomUniverses in
private theorem nativeContinuous_iff
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory (Internal Λ.X X)) :
    NativeContinuous Λ X K ↔
      BoundedTargetHomContinuous.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ.X X) ((forward Λ.X X).obj K) := by
  let J := Scheme.ProEt.topology X
  let R := ring Λ.X X
  let E := equivalence Λ.X X
  let D := E.mapDerivedCategory
  let G := CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 1}
    J R (D.functor.obj K)
  let F := (CondensedRing.derivedHom Λ.X X).obj (Opposite.op K)
  obtain ⟨e⟩ := nativeHomComparison Λ X K
  have hc : HomContinuous F ↔ HomContinuous G :=
    continuous_equivalence_iff E F G e
  have hm : HomContinuous G ↔
      (∀ (L : CategoryTheory.RingedHomUniverses.Complex.{u + 1, u, u} J R),
        Nonempty (DerivedCategory.Q.obj L ≅ D.functor.obj K) →
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
          [HasColimitsOfShape I (CategoryTheory.RingedHomUniverses.Modules.{u + 1, u, u} J R)]
          (M : I ⥤ CategoryTheory.RingedHomUniverses.Complex.{u + 1, u, u} J R) (c : ℤ),
          (∀ i, (DerivedCategory.Q.obj (M.obj i)).IsGE c) →
          IsIso (DerivedCategory.Q.map (colimit.post M
            (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R L)))) := by
    constructor
    · intro h L he I _ _ _ M c hM
      obtain ⟨eL⟩ := he
      have h' := continuous_iso
        ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J R)).mapIso
          eL.op) h
      exact (continuous_model_iff _ _
        (homFixed_derivedIso.{u + 1, u, u, u + 1} J R L)).mp h' I M c hM
    · intro h
      let L := DerivedCategory.Q.objPreimage (D.functor.obj K)
      let eL := DerivedCategory.Q.objObjPreimageIso (D.functor.obj K)
      have h' := (continuous_model_iff _ _ (homFixed_derivedIso.{u + 1, u, u, u + 1} J R L)).mpr
        (fun I _ _ M c hM ↦ h L ⟨eL⟩ I M c hM)
      exact continuous_iso
        ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J R)).mapIso
          eL.symm.op) h'
  have hbound := bound_equivalence_iff E F G e
  constructor
  · intro h
    exact ⟨(hc.trans hm).mp h.continuity, hbound.mp h.bounded⟩
  · intro h
    exact ⟨(hc.trans hm).mpr h.1, hbound.mpr h.2⟩

open ModuleObjectRingedComparison CategoryTheory.RingedHomUniverses in
private theorem nativeContinuous_closure
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (NativeContinuous Λ X) ∧
      ObjectProperty.IsTriangulated (NativeContinuous Λ X) := by
  let P : ObjectProperty (DerivedCategory (ModuleObjectRingedComparison.Modules Λ.X X)) :=
    BoundedTargetHomContinuous.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ.X X)
  have h := boundedTargetHomContinuous_triangle_closure.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ.X X)
  let : P.IsClosedUnderIsomorphisms := h.1
  let : P.IsTriangulated := h.2.1
  have he : NativeContinuous Λ X = P.inverseImage (forward Λ.X X) := by
    funext K
    exact propext (nativeContinuous_iff Λ X K)
  rw [he]
  change ObjectProperty.IsClosedUnderIsomorphisms
      (P.inverseImage (equivalence Λ.X X).functor.mapDerivedCategory) ∧
    (P.inverseImage (equivalence Λ.X X).functor.mapDerivedCategory).IsTriangulated
  exact ⟨inferInstance, inferInstance⟩

open CondensedRing in
private theorem closedModelContinuous
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (FiniteConstantModel.integralCoefficients l E) ∨
      Λ = Mon.mk (FiniteConstantModel.rationalCoefficients l E))
    {T S : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    (i : S ⟶ T) [IsClosedImmersion i]
    (L : supportModules Λ.X S) (hL : HasFiniteConstantLocalModel Λ.X S L) :
    NativeContinuous Λ T ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar Λ.X i).obj L)) := by
  let U : T.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU : Set.range U.ι = (Set.range i)ᶜ := U.range_ι
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [hU, compl_compl]
  let := closedSupport_lowerStarExact Λ.X i U.ι hij
  have : PreservesColimitsOfSize.{u + 1, u + 1} (CondensedRing.lowerStar Λ.X i) :=
    (closedSupportAdjunction Λ.X i U.ι hij).leftAdjoint_preservesColimits
  let A := (DerivedCategory.singleFunctor _ 0).obj L
  let F := (closedSupport Λ.X i U.ι).rightDerivedFunctor
  let FC := CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (supportModules Λ.X T) ⋙
      (closedSupport Λ.X i U.ι).mapHomologicalComplex (.up ℤ)
  have eFC : DerivedCategory.Q ⋙ F ≅ FC ⋙ DerivedCategory.Q :=
    resolutionDerivedIso (closedSupport Λ.X i U.ι)
  let G := (derivedHom Λ.X S).obj (Opposite.op A)
  have hF : HomContinuous F := by
    apply (continuous_model_iff F FC eFC).mpr
    intro I _ _ M c hM
    exact (closedSupport_bounded_continuity Λ.X i U.ι hU c).1 I M hM
  have hG : HomContinuous G := by
    intro I _ _ M c hM q
    exact (finite_local_model_rhom_continuity l E S Λ hΛ L hL c).1 I M hM q
  have hb (N : DerivedCategory (supportModules Λ.X T)) (c : ℤ) (hN : N.IsGE c) :
      (F.obj N).IsGE (c + 0) := by
    simpa only [add_zero] using
      (closedSupport_bounded_continuity Λ.X i U.ι hU c).2.2.1 N hN
  have hFG := continuous_comp_model F G FC eFC hF hG 0 hb
  have hpost := continuous_postcomp (CondensedRing.lowerStar Λ.X i) hFG
  obtain ⟨p, o, z, _, _, _, _, hz⟩ := openClosedInternalHomFormulas Λ.X i U.ι hij
  let e : (derivedHom Λ.X T).obj
      (Opposite.op ((CondensedRing.lowerStar Λ.X i).mapDerivedCategory.obj A)) ≅
      F ⋙ G ⋙ (CondensedRing.lowerStar Λ.X i).mapDerivedCategory :=
    closedFormulaIso _ _ _ _ z hz A
  have hcont := continuous_iso e.symm hpost
  have hbound : ∃ d : ℤ, ∀ (c : ℤ) (N : DerivedCategory (supportModules Λ.X T)),
      N.IsGE c →
      (((derivedHom Λ.X T).obj
        (Opposite.op ((CondensedRing.lowerStar Λ.X i).mapDerivedCategory.obj A))).obj N).IsGE
          (c + d) := by
    refine ⟨0, fun c N hN ↦ ?_⟩
    have hFN := (closedSupport_bounded_continuity Λ.X i U.ι hU c).2.2.1 N hN
    have := (finite_local_model_rhom_continuity l E S Λ hΛ L hL c).2 (F.obj N) hFN
    have := (CondensedRing.lowerStar Λ.X i).isGE_mapDerivedCategory_obj (G.obj (F.obj N)) c
    have := DerivedCategory.TStructure.t.isGE_of_iso (z A N).symm c
    simpa only [add_zero] using this
  let P : ObjectProperty (DerivedCategory (supportModules Λ.X T)) := NativeContinuous Λ T
  let := (nativeContinuous_closure Λ T).1
  have hA : P ((CondensedRing.lowerStar Λ.X i).mapDerivedCategory.obj A) := ⟨hcont, hbound⟩
  exact P.prop_of_iso
    ((CondensedRing.lowerStar Λ.X i).mapDerivedCategorySingleFunctor 0 |>.app L) hA

private theorem openContinuous
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X V : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] (v : V ⟶ X) [IsOpenImmersion v]
    (A : DerivedCategory (CondensedRing.supportModules Λ.X V))
    (hA : NativeContinuous Λ V A) :
    NativeContinuous Λ X
      ((CondensedRing.openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A) := by
  obtain ⟨d, hd⟩ := hA.bounded
  have ho := CondensedRing.openImmersionLowerShriek_rhom_continuity Λ v A d
    ((continuous_post_iff _).mp hA.continuity) (fun N c hN ↦ hd c N hN)
  exact ⟨(continuous_post_iff _).mpr ho.1, d, fun c N hN ↦ ho.2 N c hN⟩

/-- Constructible-source internal Hom commutes with uniformly bounded-below filtered
colimits in the ordinary, uncompleted module-object derived category. On cohomology,
the image of the original colimit cocone is a colimit cocone in every degree.

Source: Bhatt--Scholze, Lemmas 6.8.12, 6.3.14 and 6.7.13, with the internal
filtered-colimit devissage in the node
(blueprint: lem-sfb-constructible-internal-hom-continuity).

Proof, following the six DAG steps:
1. Compare native module-object Hom with ringed-site Hom using
`moduleObject_ringedSite_derived_comparison`. Exact filtered colimits commute with
cohomology, so the canonical complex-model comparison is invertible exactly when
its mapped cohomology cocones are colimits. Transport both continuity and the
uniform output bound through the exact module-sheaf equivalence.
2. Apply `finite_local_model_rhom_continuity` to finite constant local models,
including integral torsion models; their output-bound offset is zero.
3. Apply `closedSupport_bounded_continuity` to the closed-support resolution model.
Its common cohomological bound permits composition with the finite-model Hom
functor. Closed direct image is exact and preserves colimits because it is left
adjoint to closed support. The natural closed formula of
`openClosedInternalHomFormulas` identifies this composition with Hom out of the
closed direct image of the local model. Naturality transports the actual cocone.
4. Apply `openImmersionLowerShriek_rhom_continuity` to these closed-support sources
on the open subschemes of X. Open subspaces of a Noetherian space are Noetherian.
Exact-functor compatibility with the degree-zero embedding identifies the resulting
sources with the stratum generators used by `bounded_finiteModel_generation`.
5. The ringed property `BoundedTargetHomContinuous` is isomorphism-closed and
triangulated by `boundedTargetHomContinuous_triangle_closure`. Pull it back through
the derived equivalence and use step 1. Then `bounded_finiteModel_generation`
applies to the generators of step 4 and gives the property for K.
6. A common termwise lower bound implies the required common cohomological bound.
Apply the continuity component for K to the given diagram and every degree n.
All transports use natural isomorphisms and the original complex-colimit cocone,
so they preserve its canonical legs. -/
theorem constructible_internalHom_continuity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : Λ = Mon.mk (FiniteConstantModel.integralCoefficients l E) ∨
      Λ = Mon.mk (FiniteConstantModel.rationalCoefficients l E))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (_hK : constantModelBoundedConstructible Λ.X X K)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) ℤ)
    (c : ℤ) (_hM : ∀ (i : I) (r : ℤ), r < c → IsZero ((M.obj i).X r)) :
    ∀ n : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ (CondensedRing.derivedHom Λ.X X).obj (Opposite.op K) ⋙
        DerivedCategory.homologyFunctor _ n).mapCocone (colimit.cocone M))) := by
  classical
  let P : ObjectProperty (DerivedCategory (CondensedRing.supportModules Λ.X X)) :=
    NativeContinuous Λ X
  let := (nativeContinuous_closure Λ X).1
  let := (nativeContinuous_closure Λ X).2
  have hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : CondensedRing.supportModules Λ.X S), HasFiniteConstantLocalModel Λ.X S L →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ.X v).obj
          ((CondensedRing.lowerStar Λ.X t).obj L))) := by
    intro V S v _ t _ _ L hL
    have : TopologicalSpace.NoetherianSpace V :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let A := (DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ.X t).obj L)
    have hA := closedModelContinuous l E Λ _hΛ t L hL
    have hopen := openContinuous Λ X V v A hA
    exact P.prop_of_iso
      ((CondensedRing.openImmersionLowerShriek Λ.X v).mapDerivedCategorySingleFunctor 0 |>.app
        ((CondensedRing.lowerStar Λ.X t).obj L)) hopen
  have hK := (CondensedRing.bounded_finiteModel_generation Λ.X X P hgen K _hK).1
  apply hK.continuity I M c
  intro i
  have : (M.obj i).IsStrictlyGE c := (CochainComplex.isStrictlyGE_iff _ _).mpr (_hM i)
  infer_instance


end AlgebraicGeometry.ProEtale
