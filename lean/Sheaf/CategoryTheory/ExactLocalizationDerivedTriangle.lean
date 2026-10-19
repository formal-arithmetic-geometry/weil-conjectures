/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Deriving an exact localization sequence

Source: Stacks, Tags 0152, 070I and 070K; the construction used in blueprint
`det-sf-open-closed-extension-zero-limits`, proof (1)
(blueprint: lem-sf-exact-localization-derived-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

private theorem transport_ses
    {E : Type*} [Category* E]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L M N : E ⥤ DerivedCategory D)
    (T : E → ShortComplex (CochainComplex D ℤ)) (ht : ∀ X, (T X).ShortExact)
    (p : ∀ X, L.obj X ≅ DerivedCategory.Q.obj (T X).X₁)
    (q : ∀ X, M.obj X ≅ DerivedCategory.Q.obj (T X).X₂)
    (r : ∀ X, N.obj X ≅ DerivedCategory.Q.obj (T X).X₃)
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      M.map f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) :
    ∃ (α : L ⟶ M) (β : M ⟶ N)
      (δ : N ⟶ L ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ)),
      ∀ X, Triangle.mk (α.app X) (β.app X) (δ.app X) ∈
        distTriang (DerivedCategory D) := by
  let α : L ⟶ M :=
    { app := fun X ↦ (p X).hom ≫ DerivedCategory.Q.map (T X).f ≫ (q X).inv
      naturality := by
        intro X Y f
        obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
        apply (cancel_mono (q Y).hom).1
        simp only [Category.assoc]
        rw [← Category.assoc, hg₂]
        simp only [Category.assoc]
        rw [← Category.assoc, hg₁]
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id, ← Functor.map_comp] using
          congrArg (fun k ↦ (p X).hom ≫ DerivedCategory.Q.map k) g.comm₁₂
      }
  let β : M ⟶ N :=
    { app := fun X ↦ (q X).hom ≫ DerivedCategory.Q.map (T X).g ≫ (r X).inv
      naturality := by
        intro X Y f
        obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
        apply (cancel_mono (r Y).hom).1
        simp only [Category.assoc]
        rw [← Category.assoc, hg₃]
        simp only [Category.assoc]
        rw [← Category.assoc, hg₂]
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id, ← Functor.map_comp] using
          congrArg (fun k ↦ (q X).hom ≫ DerivedCategory.Q.map k) g.comm₂₃
      }
  let δ : N ⟶ L ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ) :=
    { app := fun X ↦ (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
        (shiftFunctor _ (1 : ℤ)).map (p X).inv
      naturality := by
        intro X Y f
        obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
        apply (cancel_mono ((shiftFunctor _ (1 : ℤ)).map (p Y).hom)).1
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
          Functor.map_id, Category.comp_id]
        rw [← Category.assoc, hg₃]
        rw [Category.assoc, ← DerivedCategory.triangleOfSESδ_naturality (ht X) (ht Y) g]
        change _ = (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
          (shiftFunctor _ (1 : ℤ)).map (p X).inv ≫
          (shiftFunctor _ (1 : ℤ)).map (L.map f) ≫
          (shiftFunctor _ (1 : ℤ)).map (p Y).hom
        simp only [← Functor.map_comp, hg₁,
          Iso.inv_hom_id_assoc]
      }
  refine ⟨α, β, δ, fun X ↦ ?_⟩
  apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (ht X)) _
  refine Triangle.isoMk _ _ (p X) (q X) (r X) ?_ ?_ ?_
  · change ((p X).hom ≫ DerivedCategory.Q.map (T X).f ≫ (q X).inv) ≫
        (q X).hom = (p X).hom ≫ DerivedCategory.Q.map (T X).f
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change ((q X).hom ≫ DerivedCategory.Q.map (T X).g ≫ (r X).inv) ≫
        (r X).hom = (q X).hom ≫ DerivedCategory.Q.map (T X).g
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change ((r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
        (shiftFunctor _ (1 : ℤ)).map (p X).inv) ≫
        (shiftFunctor _ (1 : ℤ)).map (p X).hom =
        (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem computation_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (G : C ⥤ D) [G.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    {J J' : CochainComplex C ℤ} [J.IsKInjective] [J'.IsKInjective] (f : J ⟶ J') :
    (G.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map f) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J')).hom =
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J)).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) := by
  let η := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  let := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J
  let := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J'
  have hn : (G.rightDerivedFunctorOfQuasiIsoResolutions h).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)) ≫
        inv (η.app ((HomotopyCategory.quotient _ _).obj J')) =
      inv (η.app ((HomotopyCategory.quotient _ _).obj J)) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ _).map f)) := by
    apply (cancel_mono (η.app ((HomotopyCategory.quotient _ _).obj J'))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hn := η.naturality ((HomotopyCategory.quotient _ _).map f)
    dsimp only [Functor.comp_map] at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  dsimp [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso]
  simp only [Functor.map_id, Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp, DerivedCategory.quotientCompQhIso_inv_naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := reassoc_of% hn
  dsimp only [η] at hn'
  rw [hn', Functor.mapHomotopyCategory_map]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]


set_option backward.isDefEq.respectTransparency false in
/-- Derive an exact localization sequence using any supply of K-injective resolutions.
Source: Stacks, Tags 0152, 070I and 070K; blueprint proof (1)
(blueprint: lem-sf-exact-localization-derived-triangle).

Proof: Choose a K-injective representative J functorially in the homotopy category,
using the inverse to its fully faithful equivalence with the derived category. Apply
`a` and `b` in each degree to G(J). The supplied short exact sequences form a short
exact sequence of complexes. Its distinguished triangle and its natural connecting
map are those of Tag 0152. The counit identifies S(G(J)) with J, including its
coefficient actions. Exactness of F and H identifies their derived functors with
termwise application. The computation isomorphism of the universal right-derived
pair identifies the middle complex G(J) with RG. All identifications are natural:
compute morphisms on K-injectives, where localization is fully faithful (070I),
and use naturality of the short-exact-sequence boundary. Transport the three arrows
through these natural isomorphisms. This yields the asserted natural transformations
and distinguished triangles. Zero categories and zero functors cause no exception;
no product, boundedness or degreewise injectivity hypothesis is used. -/
theorem exactLocalization_derived_triangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : D ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (G : C ⥤ D) [G.Additive] (adj : S ⊣ G) [IsIso adj.counit]
    (H : D ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0)
    (hseq : ∀ M, (ShortComplex.mk (a.app M) (b.app M) (hab M)).ShortExact)
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s) :
    ∃ (α : F.mapDerivedCategory ⟶ G.rightDerivedFunctorOfQuasiIsoResolutions h)
      (β : G.rightDerivedFunctorOfQuasiIsoResolutions h ⟶
        G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory)
      (δ : G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory ⟶
        F.mapDerivedCategory ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ)),
      ∀ K, Triangle.mk (α.app K) (β.app K) (δ.app K) ∈
        distTriang (DerivedCategory D) := by
  classical
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions h
  have rep (K : DerivedCategory C) : ∃ J : CochainComplex C ℤ,
      J.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj J ≅ K) := by
    obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
    obtain ⟨J, s, hJ, hs⟩ := h L
    let := hs
    exact ⟨J, hJ, ⟨(asIso (DerivedCategory.Q.map s)).symm ≪≫ e⟩⟩
  choose J hJ he using rep
  let e (K : DerivedCategory C) := Classical.choice (he K)
  let counit := NatIso.mapHomologicalComplex (asIso adj.counit) (.up ℤ)
  let T (K : DerivedCategory C) : ShortComplex (CochainComplex D ℤ) :=
    ShortComplex.mk
      ((a.mapHomologicalComplex (.up ℤ)).app (Gc.obj (J K)))
      ((b.mapHomologicalComplex (.up ℤ)).app (Gc.obj (J K)))
      (by ext n; exact hab _)
  have ht (K : DerivedCategory C) : (T K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact hseq _
  let p (K : DerivedCategory C) : F.mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj (T K).X₁ :=
    F.mapDerivedCategory.mapIso (e K).symm ≪≫ F.mapDerivedCategoryFactors.app (J K) ≪≫
      (DerivedCategory.Q.mapIso (Fc.mapIso (counit.app (J K)))).symm
  let q (K : DerivedCategory C) : RG.obj K ≅ DerivedCategory.Q.obj (T K).X₂ :=
    RG.mapIso (e K).symm ≪≫
      G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 (J K))
  let r (K : DerivedCategory C) : (RG ⋙ H.mapDerivedCategory).obj K ≅
      DerivedCategory.Q.obj (T K).X₃ :=
    H.mapDerivedCategory.mapIso (q K) ≪≫ H.mapDerivedCategoryFactors.app (Gc.obj (J K))
  apply transport_ses F.mapDerivedCategory RG (RG ⋙ H.mapDerivedCategory) T ht p q r
  intro K L f
  let qc := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (qc.obj (J K)) (J L)).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app (J K) ≫
        (e K).hom ≫ f ≫ (e L).inv ≫
          (DerivedCategory.quotientCompQhIso C).inv.app (J L))
  obtain ⟨c, rfl⟩ := qc.map_surjective g
  have hc : DerivedCategory.Q.map c = (e K).hom ≫ f ≫ (e L).inv := by
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app (J K))).1
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  let gc := Gc.map c
  let m : T K ⟶ T L :=
    { τ₁ := ((S ⋙ F).mapHomologicalComplex (.up ℤ)).map gc
      τ₂ := gc
      τ₃ := Hc.map gc
      comm₁₂ := (a.mapHomologicalComplex (.up ℤ)).naturality gc
      comm₂₃ := (b.mapHomologicalComplex (.up ℤ)).naturality gc }
  have heq : f ≫ (e L).inv = (e K).inv ≫ DerivedCategory.Q.map c := by
    rw [hc]
    simp only [Iso.inv_hom_id_assoc]
  have hq : RG.map f ≫ (q L).hom = (q K).hom ≫ DerivedCategory.Q.map gc := by
    dsimp only [q, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hq := computation_naturality G h c
    dsimp only [RG] at *
    rw [← Category.assoc, ← Functor.map_comp, heq,
      Functor.map_comp, Category.assoc, hq]
    dsimp only [gc, Gc]
    simp only [Category.assoc]
  refine ⟨m, ?_, hq, ?_⟩
  · have hn := counit.inv.naturality c
    change c ≫ counit.inv.app (J L) = counit.inv.app (J K) ≫ Sc.map (Gc.map c) at hn
    have hn' := congrArg (fun k ↦ DerivedCategory.Q.map (Fc.map k)) hn
    simp only [Functor.map_comp] at hn'
    dsimp only [p, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, heq, Functor.map_comp]
    simp only [Category.assoc]
    change F.mapDerivedCategory.map (e K).inv ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map c) ≫
        F.mapDerivedCategoryFactors.hom.app (J L) ≫
          DerivedCategory.Q.map (Fc.map (counit.inv.app (J L))) =
      F.mapDerivedCategory.map (e K).inv ≫
        F.mapDerivedCategoryFactors.hom.app (J K) ≫
          DerivedCategory.Q.map (Fc.map (counit.inv.app (J K))) ≫
            DerivedCategory.Q.map (Fc.map (Sc.map (Gc.map c)))
    rw [reassoc_of% (F.mapDerivedCategoryFactors_hom_naturality c)]
    exact congrArg (fun k ↦ F.mapDerivedCategory.map (e K).inv ≫
      F.mapDerivedCategoryFactors.hom.app (J K) ≫ k) hn'
  · dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, hq, Functor.map_comp]
    change (H.mapDerivedCategory.map (q K).hom ≫
      H.mapDerivedCategory.map (DerivedCategory.Q.map gc)) ≫
        H.mapDerivedCategoryFactors.hom.app (Gc.obj (J L)) =
      (H.mapDerivedCategory.map (q K).hom ≫
        H.mapDerivedCategoryFactors.hom.app (Gc.obj (J K))) ≫
          DerivedCategory.Q.map (Hc.map gc)
    rw [Category.assoc, H.mapDerivedCategoryFactors_hom_naturality gc, Category.assoc]

end CategoryTheory
