/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# K-injective descent after exact postcomposition

Source: Stacks Project, Derived Categories, Tags 070I, 070Y, 070K and 08BJ;
the normalized descent calculation in the node's proof
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

The unit and normalization predicates below only package the canonical comparisons.
No K-injective preservation hypothesis is imposed on the exact postcomposition functors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u0 u1 u2 uB v0 v1 v2 vB w0 w1 w2 wB
universe u0' u1' u2' uB' v0' v1' v2' vB' w0' w1' w2' wB'

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Representatives

variable {A : Type u0} [Category.{v0} A] [Abelian A] [HasDerivedCategory.{w0} A]
  {T : Type uB} [Category.{vB} T]

private theorem representative (h : ∀ N : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (X : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ Nonempty (X ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨I, a, hI, ha⟩ := h (DerivedCategory.Q.objPreimage X)
  exact ⟨I, hI, ⟨(DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
    asIso (DerivedCategory.Q.map a)⟩⟩

private theorem representative_ext
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T} (α β : F ⟶ G)
    (he : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  ext X
  obtain ⟨I, hI, ⟨e⟩⟩ := representative h X
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, he I]

private theorem representative_map_surjective (I J : CochainComplex A ℤ)
    [J.IsKInjective] (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ g : I ⟶ J, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj I) J).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app I ≫ f ≫
        (DerivedCategory.quotientCompQhIso A).inv.app J)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso A).hom.naturality g
  dsimp at hn
  rw [hg] at hn
  simpa using congrArg
    (fun t ↦ (DerivedCategory.quotientCompQhIso A).inv.app I ≫ t) hn.symm

private theorem extend_representatives
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T}
    (t : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      F.obj (DerivedCategory.Q.obj I) ≅ G.obj (DerivedCategory.Q.obj I))
    (ht : ∀ (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] (g : I ⟶ J),
      F.map (DerivedCategory.Q.map g) ≫ (t J).hom =
        (t I).hom ≫ G.map (DerivedCategory.Q.map g)) :
    ∃ r : F ≅ G, ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      r.hom.app (DerivedCategory.Q.obj I) = (t I).hom := by
  classical
  choose I hI e using representative h
  let e' (X : DerivedCategory A) := (e X).some
  have hn (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective]
      (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
      F.map f ≫ (t J).hom = (t I).hom ≫ G.map f := by
    obtain ⟨g, rfl⟩ := representative_map_surjective I J f
    exact ht I J g
  let r : F ≅ G := NatIso.ofComponents
    (fun X ↦ F.mapIso (e' X) ≪≫ t (I X) ≪≫ (G.mapIso (e' X)).symm)
    (by
      intro X Y f
      have hh := hn (I X) (I Y) ((e' X).inv ≫ f ≫ (e' Y).hom)
      dsimp
      simp only [Functor.map_comp, Category.assoc] at hh ⊢
      have hh' := congrArg (fun z ↦ F.map (e' X).hom ≫ z ≫ G.map (e' Y).inv) hh
      simpa [← Functor.map_comp, Category.assoc] using hh')
  refine ⟨r, ?_⟩
  intro J hJ
  have hh := hn J (I (DerivedCategory.Q.obj J)) (e' (DerivedCategory.Q.obj J)).hom
  dsimp [r]
  rw [← Category.assoc, hh]
  simp [← G.map_comp]

private theorem extend_units
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T} {S : CochainComplex A ℤ ⥤ T}
    (u : S ⟶ DerivedCategory.Q ⋙ F) (v : S ⟶ DerivedCategory.Q ⋙ G)
    (hu : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso (u.app I))
    (hv : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso (v.app I)) :
    ∃ r : F ≅ G, ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      u.app I ≫ r.hom.app (DerivedCategory.Q.obj I) = v.app I := by
  let t (I : CochainComplex A ℤ) [I.IsKInjective] :
      F.obj (DerivedCategory.Q.obj I) ≅ G.obj (DerivedCategory.Q.obj I) :=
    letI := hu I
    letI := hv I
    (asIso (u.app I)).symm ≪≫ asIso (v.app I)
  have ht (I : CochainComplex A ℤ) [I.IsKInjective] :
      u.app I ≫ (t I).hom = v.app I := by
    let := hu I
    simp [t]
  obtain ⟨r, hr⟩ := extend_representatives h t (by
    intro I J hI hJ a
    let := hu I
    apply (cancel_epi (u.app I)).mp
    have hn := u.naturality a
    have hn' := v.naturality a
    dsimp only [Functor.comp_map] at hn hn'
    rw [← Category.assoc, ← hn, Category.assoc, ht J,
      ← Category.assoc, ht I, hn'])
  refine ⟨r, ?_⟩
  intro I hI
  rw [hr I]
  exact ht I

private theorem representative_app_eq
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T} (α β : F ⟶ G)
    (he : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I))
    (X : DerivedCategory A) : α.app X = β.app X :=
  NatTrans.congr_app (representative_ext h α β he) X

private theorem resolution_unit_ext
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {S : CochainComplex A ℤ ⥤ T} {F : DerivedCategory A ⥤ T}
    (α β : S ⟶ DerivedCategory.Q ⋙ F)
    (he : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], α.app I = β.app I) : α = β := by
  ext N
  obtain ⟨I, a, hI, ha⟩ := h N
  apply (cancel_mono (F.map (DerivedCategory.Q.map a))).mp
  have hα := α.naturality a
  have hβ := β.naturality a
  dsimp only [Functor.comp_map] at hα hβ
  rw [← hα, ← hβ, he I]

end Representatives

section Unit

variable {A : Type u1} {C : Type u0} [Category.{v1} A] [Category.{v0} C]
  [Abelian A] [Abelian C] [HasDerivedCategory.{w1} A] [HasDerivedCategory.{w0} C]

/-- The recorded right-derived unit, expressed on complexes using the canonical
quotient-to-localization comparisons. Source: Stacks Tags 070K and 070Y
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent). -/
noncomputable def kInjectiveDescentUnit (H : A ⥤ C) [H.Additive]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (H.rightDerivedFunctorOfQuasiIsoResolutions h).obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
    (H.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
    (H.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso A).hom.app I)

private theorem descentUnit_isIso (H : A ⥤ C) [H.Additive]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (kInjectiveDescentUnit H h I) := by
  let := H.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  dsimp [kInjectiveDescentUnit]
  infer_instance

private theorem descentUnit_naturality (H : A ⥤ C) [H.Additive]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {I J : CochainComplex A ℤ} (a : I ⟶ J) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map a) ≫
        kInjectiveDescentUnit H h J =
      kInjectiveDescentUnit H h I ≫
        (H.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map a) := by
  have hq := (DerivedCategory.quotientCompQhIso C).inv.naturality
    ((H.mapHomologicalComplex (.up ℤ)).map a)
  have hu := (H.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).naturality
    ((HomotopyCategory.quotient A (.up ℤ)).map a)
  have ha := (DerivedCategory.quotientCompQhIso A).hom.naturality a
  dsimp only [Functor.comp_map] at hq hu ha
  dsimp only [kInjectiveDescentUnit]
  simp only [Category.assoc]
  erw [reassoc_of% hq, reassoc_of% hu]
  simp only [← Functor.map_comp]
  rw [ha]

private noncomputable def descentUnitNat (H : A ⥤ C) [H.Additive]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ H.rightDerivedFunctorOfQuasiIsoResolutions h where
  app := kInjectiveDescentUnit H h
  naturality := by
    intro I J a
    exact descentUnit_naturality H h a

private theorem descentObjIso_unit (H : A ⥤ C) [H.Additive]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {N I : CochainComplex A ℤ} [I.IsKInjective] (a : N ⟶ I) [QuasiIso a] :
    (H.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h a).hom ≫
        kInjectiveDescentUnit H h I =
      (H.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map a) := by
  dsimp [rightDerivedFunctorOfQuasiIsoResolutionsObjIso, kInjectiveDescentUnit]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, IsIso.inv_hom_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

end Unit

section ExactSquare

variable {C : Type u0} {D : Type u1} {D' : Type u2} {T : Type uB}
  [Category.{v0} C] [Category.{v1} D] [Category.{v2} D'] [Category.{vB} T]
  [Abelian C] [Abelian D] [Abelian D'] [Abelian T]
  [HasDerivedCategory.{w0} C] [HasDerivedCategory.{w1} D]
  [HasDerivedCategory.{w2} D'] [HasDerivedCategory.{wB} T]
  {F : C ⥤ D} {G : D ⥤ T} {F' : C ⥤ D'} {G' : D' ⥤ T}
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

private theorem square_factors (e : F ⋙ G ≅ F' ⋙ G') (I : CochainComplex C ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj I) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app I) ≫
        G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  dsimp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors,
    mapDerivedCategoryNatIso_fac]
  rw [← mapDerivedCategoryCompIso_hom_app_factors F G I]
  simp

end ExactSquare

section Descent

variable {A0 : Type u0} {A1 : Type u1} {B : Type uB}
  [Category.{v0} A0] [Category.{v1} A1] [Category.{vB} B]
  [Abelian A0] [Abelian A1] [Abelian B]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{wB} B]
  (h1 : ∀ N : CochainComplex A1 ℤ,
    ∃ (I : CochainComplex A1 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (H : A1 ⥤ A0) [H.Additive]
  (E0 : A0 ⥤ B) (E1 : A1 ⥤ B) [E0.Additive] [E1.Additive]
  [PreservesFiniteLimits E0] [PreservesFiniteColimits E0]
  [PreservesFiniteLimits E1] [PreservesFiniteColimits E1]
  (c : H ⋙ E0 ≅ E1)

/-- Normalization on every K-injective, with the exact-functor localization comparisons
inserted. Source: Stacks Tags 070I and 070Y, node proof step 1
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent). -/
def IsNormalizedKInjectiveDescent
    (r : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
      E1.mapDerivedCategory) : Prop :=
  ∀ (I : CochainComplex A1 ℤ), I.IsKInjective →
    E0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I) ≫
        r.hom.app (DerivedCategory.Q.obj I) ≫ E1.mapDerivedCategoryFactors.hom.app I =
      E0.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I)

private theorem descent_exists :
    ∃ r : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
        E1.mapDerivedCategory, IsNormalizedKInjectiveDescent h1 H E0 E1 c r := by
  let t (I : CochainComplex A1 ℤ) [I.IsKInjective] :
      E0.mapDerivedCategory.obj
          ((H.rightDerivedFunctorOfQuasiIsoResolutions h1).obj (DerivedCategory.Q.obj I)) ≅
        E1.mapDerivedCategory.obj (DerivedCategory.Q.obj I) :=
    have := descentUnit_isIso H h1 I
    (E0.mapDerivedCategory.mapIso (asIso (kInjectiveDescentUnit H h1 I))).symm ≪≫
      E0.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex c (.up ℤ)).app I) ≪≫
      (E1.mapDerivedCategoryFactors.app I).symm
  have ht (I : CochainComplex A1 ℤ) [I.IsKInjective] :
      E0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I) ≫
          (t I).hom ≫ E1.mapDerivedCategoryFactors.hom.app I =
        E0.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) := by
    have := descentUnit_isIso H h1 I
    simp [t]
    rfl
  obtain ⟨r, hr⟩ := extend_representatives h1
    (F := H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory)
    (G := E1.mapDerivedCategory) t (by
    intro I J hI hJ a
    have := descentUnit_isIso H h1 I
    apply (cancel_epi (E0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I))).mp
    apply (cancel_mono (E1.mapDerivedCategoryFactors.hom.app J)).mp
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    rw [← E0.mapDerivedCategory.map_comp_assoc, ← descentUnit_naturality,
      E0.mapDerivedCategory.map_comp_assoc, ht J]
    have hn1 := E1.mapDerivedCategoryFactors.hom.naturality a
    dsimp only [Functor.comp_map] at hn1
    erw [hn1]
    erw [reassoc_of% ht I]
    have hn0 := E0.mapDerivedCategoryFactors.hom.naturality
      ((H.mapHomologicalComplex (.up ℤ)).map a)
    dsimp only [Functor.comp_map] at hn0
    erw [reassoc_of% hn0]
    simp only [← Functor.map_comp]
    have hn := (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).naturality a
    erw [hn])
  refine ⟨r, ?_⟩
  intro I hI
  rw [hr I]
  exact ht I

/-- Normalization alone determines the comparison, hence its construction is independent
of every choice of resolutions. Source: Stacks 070I, node proof steps 2--4
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: cancel the invertible unit on K-injectives in the two normalization equations.
Every derived object is isomorphic to a K-injective representative; naturality transports
the resulting equality to that object. Equality of components gives equality of isomorphisms.
-/
theorem normalizedKInjectiveDescent_ext
    (r s : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
      E1.mapDerivedCategory)
    (hr : IsNormalizedKInjectiveDescent h1 H E0 E1 c r)
    (hs : IsNormalizedKInjectiveDescent h1 H E0 E1 c s) : r = s := by
  apply Iso.ext
  apply representative_ext h1
  intro I hI
  have := descentUnit_isIso H h1 I
  apply (cancel_epi (E0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I))).mp
  apply (cancel_mono (E1.mapDerivedCategoryFactors.hom.app I)).mp
  simpa only [Category.assoc] using (hr I hI).trans (hs I hI).symm


set_option linter.unusedVariables false in
/-- Existence and uniqueness of normalized descent, including its formula for every
resolution and naturality for all derived arrows. Source: Stacks Tags 070I, 070Y, 070K,
08BJ; node proof steps 1--4
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: form the isomorphism on each K-injective by inverting the derived unit and
using the exact-factorization comparisons. Naturality holds on homotopy classes because
additive functors respect homotopies. The Hom bijection into K-injectives represents every
derived arrow. Choose K-injective representatives and conjugate these components by their
resolution isomorphisms. The same naturality square proves uniqueness and independence.
Taking the representative from any specified resolution gives the displayed formula.
The exact left adjoint preserves acyclic complexes, so H preserves K-injectives by 08BJ.
-/
theorem exists_unique_normalizedKInjectiveDescent
    (h0 : ∀ N : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (L : A0 ⥤ A1) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ H) :
    ∃! r : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
        E1.mapDerivedCategory,
      IsNormalizedKInjectiveDescent h1 H E0 E1 c r ∧
      (∀ (N I : CochainComplex A1 ℤ) [I.IsKInjective] (a : N ⟶ I) [QuasiIso a],
        r.hom.app (DerivedCategory.Q.obj N) ≫
            E1.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
            E1.mapDerivedCategoryFactors.hom.app I =
          E0.mapDerivedCategory.map
              (H.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h1 a).hom ≫
            E0.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I)) ∧
      (∀ (X Y : DerivedCategory A1) (f : X ⟶ Y),
        E0.mapDerivedCategory.map ((H.rightDerivedFunctorOfQuasiIsoResolutions h1).map f) ≫
            r.hom.app Y = r.hom.app X ≫ E1.mapDerivedCategory.map f) := by
  clear h0 adj
  obtain ⟨r, hr⟩ := descent_exists h1 H E0 E1 c
  refine ⟨r, ⟨hr, ?_, fun X Y f ↦ r.hom.naturality f⟩, ?_⟩
  · intro N I hI a ha
    rw [← r.hom.naturality_assoc]
    change E0.mapDerivedCategory.map
        ((H.rightDerivedFunctorOfQuasiIsoResolutions h1).map (DerivedCategory.Q.map a)) ≫
          r.hom.app (DerivedCategory.Q.obj I) ≫ E1.mapDerivedCategoryFactors.hom.app I = _
    rw [← descentObjIso_unit H h1 a, E0.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    rw [hr I hI]
  · intro s hs
    apply Iso.ext
    apply representative_ext h1
    intro I hI
    have := descentUnit_isIso H h1 I
    apply (cancel_epi (E0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I))).mp
    apply (cancel_mono (E1.mapDerivedCategoryFactors.hom.app I)).mp
    simpa only [Category.assoc] using (hs.1 I hI).trans (hr I hI).symm


end Descent

section Composition

variable {A0 : Type u0} {A1 : Type u1} {A2 : Type u2} {B : Type uB}
  [Category.{v0} A0] [Category.{v1} A1] [Category.{v2} A2] [Category.{vB} B]
  [Abelian A0] [Abelian A1] [Abelian A2] [Abelian B]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{wB} B]
  (h1 : ∀ N : CochainComplex A1 ℤ,
    ∃ (I : CochainComplex A1 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h2 : ∀ N : CochainComplex A2 ℤ,
    ∃ (I : CochainComplex A2 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (H : A1 ⥤ A0) (J : A2 ⥤ A1) (P : A2 ⥤ A0)
  [H.Additive] [J.Additive] [P.Additive] (d : P ≅ J ⋙ H)

/-- The compositor is normalized by Q(d), using JI as the intermediate representative.
The units are defined even before asserting preservation of K-injectives.
Source: Stacks 08BJ and 070I, node proof steps 5--6
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent). -/
def IsNormalizedKInjectiveCompositor
    (κ : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ≅
      J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙
        H.rightDerivedFunctorOfQuasiIsoResolutions h1) : Prop :=
  ∀ (I : CochainComplex A2 ℤ), I.IsKInjective →
    kInjectiveDescentUnit P h2 I ≫ κ.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I) ≫
        kInjectiveDescentUnit H h1 ((J.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (H.rightDerivedFunctorOfQuasiIsoResolutions h1).map (kInjectiveDescentUnit J h2 I)

/-- Uniqueness of the compositor from its K-injective normalization.
Source: Stacks 070I, node proof step 6
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: invert the unit at each K-injective in both normalization equations.
Conjugate along a K-injective resolution of every derived object and use naturality.
-/
theorem normalizedKInjectiveCompositor_ext
    (κ κ' : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ≅
      J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙
        H.rightDerivedFunctorOfQuasiIsoResolutions h1)
    (hκ : IsNormalizedKInjectiveCompositor h1 h2 H J P d κ)
    (hκ' : IsNormalizedKInjectiveCompositor h1 h2 H J P d κ') : κ = κ' := by
  apply Iso.ext
  apply representative_ext h2
  intro I hI
  have := descentUnit_isIso P h2 I
  apply (cancel_epi (kInjectiveDescentUnit P h2 I)).mp
  exact (hκ I hI).trans (hκ' I hI).symm


set_option linter.unusedVariables false in
/-- Preservation of K-injectives, the uniquely normalized compositor, and compatibility
with exact postcomposition. Source: Stacks Tags 08BJ, 070I and 070K, node proof steps 5--7
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: the exact left adjoints of H, J and P give preservation by 08BJ. On a
K-injective I, use JI as the intermediate K-injective and define the compositor by Q(d_I).
Naturality on homotopy classes and the Hom bijection extend it uniquely to the derived
category, as in steps 2--4. On QI the three comparisons in the claimed identity are
Q(E0 d_I), Q(c_JI), and Q(c'_I); their composite is Q(b_I). The normalization determines
r_b, so equality on these representatives extends to every derived object.
-/
theorem normalizedKInjectiveDescent_comp
    (h0 : ∀ N : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (LH : A0 ⥤ A1) (LJ : A1 ⥤ A2) (LP : A0 ⥤ A2)
    [LH.Additive] [LJ.Additive] [LP.Additive]
    [PreservesFiniteLimits LH] [PreservesFiniteColimits LH]
    [PreservesFiniteLimits LJ] [PreservesFiniteColimits LJ]
    [PreservesFiniteLimits LP] [PreservesFiniteColimits LP]
    (adjH : LH ⊣ H) (adjJ : LJ ⊣ J) (adjP : LP ⊣ P)
    (E0 : A0 ⥤ B) (E1 : A1 ⥤ B) (E2 : A2 ⥤ B)
    [E0.Additive] [E1.Additive] [E2.Additive]
    [PreservesFiniteLimits E0] [PreservesFiniteColimits E0]
    [PreservesFiniteLimits E1] [PreservesFiniteColimits E1]
    [PreservesFiniteLimits E2] [PreservesFiniteColimits E2]
    (c : H ⋙ E0 ≅ E1) (c' : J ⋙ E1 ≅ E2) (b : P ⋙ E0 ≅ E2)
    (hb : b.hom = whiskerRight d.hom E0 ≫ (associator J H E0).hom ≫
      whiskerLeft J c.hom ≫ c'.hom) :
    H.PreservesKInjectiveComplexes ∧ J.PreservesKInjectiveComplexes ∧
      P.PreservesKInjectiveComplexes ∧
    ∃! κ : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ≅
        J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙
          H.rightDerivedFunctorOfQuasiIsoResolutions h1,
      IsNormalizedKInjectiveCompositor h1 h2 H J P d κ ∧
      ∀ (rc : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
          E1.mapDerivedCategory)
        (rc' : J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙ E1.mapDerivedCategory ≅
          E2.mapDerivedCategory)
        (rb : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙ E0.mapDerivedCategory ≅
          E2.mapDerivedCategory),
        IsNormalizedKInjectiveDescent h1 H E0 E1 c rc →
        IsNormalizedKInjectiveDescent h2 J E1 E2 c' rc' →
        IsNormalizedKInjectiveDescent h2 P E0 E2 b rb →
        rb.hom = whiskerRight κ.hom E0.mapDerivedCategory ≫
          (associator _ _ _).hom ≫
          whiskerLeft (J.rightDerivedFunctorOfQuasiIsoResolutions h2) rc.hom ≫ rc'.hom := by
  let := adjH.preservesKInjectiveComplexes
  let := adjJ.preservesKInjectiveComplexes
  let := adjP.preservesKInjectiveComplexes
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  let v : P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙
        H.rightDerivedFunctorOfQuasiIsoResolutions h1) :=
    whiskerRight (NatTrans.mapHomologicalComplex d.hom (.up ℤ)) DerivedCategory.Q ≫
      whiskerLeft (J.mapHomologicalComplex (.up ℤ)) (descentUnitNat H h1) ≫
      whiskerRight (descentUnitNat J h2) (H.rightDerivedFunctorOfQuasiIsoResolutions h1)
  obtain ⟨κ, hκ⟩ := extend_units h2 (descentUnitNat P h2) v
    (fun I _ ↦ by simpa [descentUnitNat] using descentUnit_isIso P h2 I) (by
      intro I hI
      have := descentUnit_isIso H h1 ((J.mapHomologicalComplex (.up ℤ)).obj I)
      have := descentUnit_isIso J h2 I
      have : IsIso ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I) :=
        ((NatIso.mapHomologicalComplex d (.up ℤ)).app I).isIso_hom
      dsimp [v, descentUnitNat]
      infer_instance)
  have hκn : IsNormalizedKInjectiveCompositor h1 h2 H J P d κ := by
    intro I hI
    simpa [descentUnitNat, v, Category.assoc] using hκ I
  refine ⟨κ, ⟨hκn, ?_⟩, ?_⟩
  · intro rc rc' rb hrc hrc' hrb
    let t : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙ E0.mapDerivedCategory ≅
        E2.mapDerivedCategory :=
      isoWhiskerRight κ E0.mapDerivedCategory ≪≫ associator _ _ _ ≪≫
        isoWhiskerLeft (J.rightDerivedFunctorOfQuasiIsoResolutions h2) rc ≪≫ rc'
    have htn : IsNormalizedKInjectiveDescent h2 P E0 E2 b t := by
      intro I hI
      dsimp [t]
      simp only [Category.id_comp, Category.assoc]
      rw [← E0.mapDerivedCategory.map_comp_assoc, hκn I hI,
        E0.mapDerivedCategory.map_comp, E0.mapDerivedCategory.map_comp]
      simp only [Category.assoc]
      have hn := rc.hom.naturality (kInjectiveDescentUnit J h2 I)
      dsimp only [Functor.comp_map] at hn
      erw [reassoc_of% hn]
      erw [hrc' I hI]
      erw [reassoc_of% hrc ((J.mapHomologicalComplex (.up ℤ)).obj I) inferInstance]
      have hf := E0.mapDerivedCategoryFactors.hom.naturality
        ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I)
      dsimp only [Functor.comp_map] at hf
      erw [reassoc_of% hf]
      have hbI : (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app I =
          (E0.mapHomologicalComplex (.up ℤ)).map
              ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I) ≫
            (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app
              ((J.mapHomologicalComplex (.up ℤ)).obj I) ≫
            (NatTrans.mapHomologicalComplex c'.hom (.up ℤ)).app I := by
        ext n
        change b.hom.app (I.X n) = E0.map (d.hom.app (I.X n)) ≫
          c.hom.app (J.obj (I.X n)) ≫ c'.hom.app (I.X n)
        simpa using congrArg (fun z ↦ z.app (I.X n)) hb
      erw [hbI]
      simp only [Functor.map_comp]
    have he := normalizedKInjectiveDescent_ext h2 P E0 E2 b rb t hrb htn
    exact congrArg Iso.hom he
  · intro κ' hκ'
    exact normalizedKInjectiveCompositor_ext h1 h2 H J P d κ' κ hκ'.1 hκn


end Composition

section Identity

variable {A : Type u0} [Category.{v0} A] [Abelian A] [HasDerivedCategory.{w0} A]
  (h : ∀ N : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)

/-- Identity normalization, including the canonical comparison R1 ≅ 1.
Source: Stacks 070K and localization, node proof step 8
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: the identity on D(A) with its localization comparison is a right-derived pair
for the identity. Uniqueness of the universal right-derived pair gives the unique e
carrying its unit to the identity. After this identification the normalized component is
identity on every K-injective. Uniqueness of descent extends this to all derived objects.
-/
theorem normalizedKInjectiveDescent_id :
    ∃! e : (𝟭 A).rightDerivedFunctorOfQuasiIsoResolutions h ≅ 𝟭 (DerivedCategory A),
      (∀ I : CochainComplex A ℤ,
        kInjectiveDescentUnit (𝟭 A) h I ≫ e.hom.app (DerivedCategory.Q.obj I) =
          DerivedCategory.Q.map ((mapHomologicalComplexIdIso A (.up ℤ)).hom.app I)) ∧
      (∀ {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
        (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
        (r : (𝟭 A).rightDerivedFunctorOfQuasiIsoResolutions h ⋙ E.mapDerivedCategory ≅
          E.mapDerivedCategory),
        IsNormalizedKInjectiveDescent h (𝟭 A) E E (leftUnitor E) r →
          r.hom = whiskerRight e.hom E.mapDerivedCategory ≫
            (leftUnitor E.mapDerivedCategory).hom) := by
  let v : (𝟭 A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ 𝟭 (DerivedCategory A) :=
    whiskerRight (mapHomologicalComplexIdIso A (.up ℤ)).hom DerivedCategory.Q
  obtain ⟨e, he⟩ := extend_units h (descentUnitNat (𝟭 A) h) v
    (fun I _ ↦ by simpa [descentUnitNat] using descentUnit_isIso (𝟭 A) h I) (by
      intro I hI
      dsimp [v]
      infer_instance)
  have hen (N : CochainComplex A ℤ) :
      kInjectiveDescentUnit (𝟭 A) h N ≫ e.hom.app (DerivedCategory.Q.obj N) =
        DerivedCategory.Q.map ((mapHomologicalComplexIdIso A (.up ℤ)).hom.app N) := by
    obtain ⟨I, a, hI, ha⟩ := h N
    apply (cancel_mono (DerivedCategory.Q.map a)).mp
    have hn := e.hom.naturality (DerivedCategory.Q.map a)
    dsimp only [Functor.id_map] at hn
    rw [Category.assoc, ← hn]
    have heI := he I
    dsimp [descentUnitNat, v] at heI
    rw [← Category.assoc, ← descentUnit_naturality, Category.assoc, heI]
    exact v.naturality a
  refine ⟨e, ⟨hen, ?_⟩, ?_⟩
  · intro B _ _ _ E _ _ _ r hr
    let t : (𝟭 A).rightDerivedFunctorOfQuasiIsoResolutions h ⋙ E.mapDerivedCategory ≅
        E.mapDerivedCategory := isoWhiskerRight e E.mapDerivedCategory ≪≫ leftUnitor _
    have ht : IsNormalizedKInjectiveDescent h (𝟭 A) E E (leftUnitor E) t := by
      intro I hI
      dsimp [t]
      simp only [Category.comp_id, ← Functor.map_comp_assoc, hen]
      have hn := E.mapDerivedCategoryFactors.hom.naturality
        ((mapHomologicalComplexIdIso A (.up ℤ)).hom.app I)
      dsimp only [Functor.comp_map, Functor.id_obj] at hn
      erw [hn]
      congr 1
      congr 1
      ext n
      exact E.map_id _
    exact congrArg Iso.hom
      (normalizedKInjectiveDescent_ext h (𝟭 A) E E (leftUnitor E) r t hr ht)
  · intro e' he'
    apply Iso.ext
    apply representative_ext h
    intro I hI
    have := descentUnit_isIso (𝟭 A) h I
    apply (cancel_epi (kInjectiveDescentUnit (𝟭 A) h I)).mp
    exact (he'.1 I).trans (hen I).symm

end Identity

section Equivalence

variable {A : Type u0} {A' : Type u0'} [Category.{v0} A] [Category.{v0'} A']
  [Abelian A] [Abelian A']

/-- An additive exact equivalence preserves and reflects K-injectivity and carries
resolution quasi-isomorphisms to resolution quasi-isomorphisms.
Source: Stacks 08BJ and 070I, node proof step 9
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: the inverse equivalence is additive and exact, as follows by transporting
Hom bijections and limit and colimit universal properties. The adjunction on homotopy
categories identifies maps from acyclic complexes into UI with maps into I. Exactness
of the inverse makes these zero, proving preservation. Interchange the equivalences and
use invariance under complex isomorphisms to obtain reflection. Exactness preserves
quasi-isomorphisms, giving the resolution clause. Resolve the inverse image of any complex
and use the counit isomorphism to obtain enough resolutions in the equivalent category.
-/
theorem kInjectiveDescent_equivalence_resolutions
    (U : A ⥤ A') [U.Additive] [U.IsEquivalence]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    (∀ I : CochainComplex A ℤ,
      I.IsKInjective ↔ CochainComplex.IsKInjective ((U.mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (N I : CochainComplex A ℤ) [I.IsKInjective] (a : N ⟶ I) [QuasiIso a],
      CochainComplex.IsKInjective ((U.mapHomologicalComplex (.up ℤ)).obj I) ∧
        QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map a)) ∧
    (∀ N : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a) := by
  let V := U.asEquivalence.inverse
  have : U.asEquivalence.functor.Additive := ‹U.Additive›
  have : V.Additive := U.asEquivalence.inverse_additive
  have hi (I : CochainComplex A ℤ) :
      I.IsKInjective ↔ CochainComplex.IsKInjective
        ((U.mapHomologicalComplex (.up ℤ)).obj I) := by
    constructor
    · intro hI
      infer_instance
    · intro hI
      have hVI : CochainComplex.IsKInjective
          ((V.mapHomologicalComplex (.up ℤ)).obj
            ((U.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
      have e : (V.mapHomologicalComplex (.up ℤ)).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj I) ≅ I :=
        ((U.asEquivalence.mapHomologicalComplex (.up ℤ)).unitIso.app I).symm
      exact CochainComplex.isKInjective_of_iso e
  refine ⟨hi, ?_, ?_⟩
  · intro N I hI a ha
    exact ⟨(hi I).mp hI, inferInstance⟩
  · intro N
    obtain ⟨I, a, hI, ha⟩ := h ((V.mapHomologicalComplex (.up ℤ)).obj N)
    let e := (U.asEquivalence.mapHomologicalComplex (.up ℤ)).counitIso.app N
    refine ⟨(U.mapHomologicalComplex (.up ℤ)).obj I,
      e.inv ≫ (U.mapHomologicalComplex (.up ℤ)).map a, (hi I).mp hI, ?_⟩
    infer_instance

end Equivalence

section Square

variable {A0 : Type u0} {A1 : Type u1} {A0' : Type u0'} {A1' : Type u1'}
  [Category.{v0} A0] [Category.{v1} A1] [Category.{v0'} A0'] [Category.{v1'} A1']
  [Abelian A0] [Abelian A1] [Abelian A0'] [Abelian A1']
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w0'} A0'] [HasDerivedCategory.{w1'} A1']
  (h1 : ∀ N : CochainComplex A1 ℤ,
    ∃ (I : CochainComplex A1 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h1' : ∀ N : CochainComplex A1' ℤ,
    ∃ (I : CochainComplex A1' ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (H : A1 ⥤ A0) (H' : A1' ⥤ A0') [H.Additive] [H'.Additive]
  (U0 : A0 ⥤ A0') (U1 : A1 ⥤ A1') [U0.Additive] [U1.Additive]
  [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
  [PreservesFiniteLimits U1] [PreservesFiniteColimits U1]
  (α : U1 ⋙ H' ≅ H ⋙ U0)

/-- Unit normalization of the comparison transporting a right-derived functor through
exact equivalences. Source: Stacks 070I and 08BJ, node proof step 10
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent). -/
def IsNormalizedKInjectiveSquare
    (a : U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ≅
      H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory) : Prop :=
  ∀ (I : CochainComplex A1 ℤ), I.IsKInjective →
    kInjectiveDescentUnit H' h1' ((U1.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map
          (U1.mapDerivedCategoryFactors.inv.app I) ≫ a.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) ≫
        U0.mapDerivedCategoryFactors.inv.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
        U0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I)

private theorem square_normalization_all
    (a : U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ≅
      H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory)
    (_ha : IsNormalizedKInjectiveSquare h1 h1' H H' U0 U1 α a)
    (I : CochainComplex A1 ℤ) :
    kInjectiveDescentUnit H' h1' ((U1.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map
          (U1.mapDerivedCategoryFactors.inv.app I) ≫ a.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) ≫
        U0.mapDerivedCategoryFactors.inv.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
        U0.mapDerivedCategory.map (kInjectiveDescentUnit H h1 I) := by
  let l := whiskerLeft (U1.mapHomologicalComplex (.up ℤ)) (descentUnitNat H' h1') ≫
    whiskerRight U1.mapDerivedCategoryFactors.inv
      (H'.rightDerivedFunctorOfQuasiIsoResolutions h1') ≫ whiskerLeft DerivedCategory.Q a.hom
  let r := whiskerRight (NatTrans.mapHomologicalComplex α.hom (.up ℤ)) DerivedCategory.Q ≫
    whiskerLeft (H.mapHomologicalComplex (.up ℤ)) U0.mapDerivedCategoryFactors.inv ≫
    whiskerRight (descentUnitNat H h1) U0.mapDerivedCategory
  have he : l = r := resolution_unit_ext h1 l r (by
    intro J hJ
    simpa [l, r, descentUnitNat] using _ha J hJ)
  simpa [l, r, descentUnitNat] using NatTrans.congr_app he I

/-- The normalized transport square exists uniquely under additive exact equivalences.
Source: Stacks 070I, 070K, 08BJ, node proof step 10
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: U1 carries K-injectives to K-injectives by step 9. Thus both units in the
normalization are invertible there. Use Q(alpha_I) between these representatives and
extend by the Hom bijection, as in proof steps 2--4. Cancellation gives uniqueness.
-/
theorem exists_unique_normalizedKInjectiveSquare [U0.IsEquivalence] [U1.IsEquivalence] :
    ∃! a : U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ≅
      H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory,
      IsNormalizedKInjectiveSquare h1 h1' H H' U0 U1 α a := by
  let u : (U1 ⋙ H').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1') :=
    whiskerLeft (U1.mapHomologicalComplex (.up ℤ)) (descentUnitNat H' h1') ≫
      whiskerRight U1.mapDerivedCategoryFactors.inv
        (H'.rightDerivedFunctorOfQuasiIsoResolutions h1')
  let v : (U1 ⋙ H').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory) :=
    whiskerRight (NatTrans.mapHomologicalComplex α.hom (.up ℤ)) DerivedCategory.Q ≫
      whiskerLeft (H.mapHomologicalComplex (.up ℤ)) U0.mapDerivedCategoryFactors.inv ≫
      whiskerRight (descentUnitNat H h1) U0.mapDerivedCategory
  obtain ⟨a, ha⟩ := extend_units h1 u v (by
      intro I hI
      have := descentUnit_isIso H' h1' ((U1.mapHomologicalComplex (.up ℤ)).obj I)
      dsimp [u, descentUnitNat]
      infer_instance) (by
      intro I hI
      have := descentUnit_isIso H h1 I
      have : IsIso ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) :=
        ((NatIso.mapHomologicalComplex α (.up ℤ)).app I).isIso_hom
      dsimp [v, descentUnitNat]
      infer_instance)
  refine ⟨a, ?_, ?_⟩
  · intro I hI
    simpa [u, v, descentUnitNat, Category.assoc] using ha I
  intro a' ha'
  apply Iso.ext
  apply representative_ext h1
  intro I hI
  have := descentUnit_isIso H' h1' ((U1.mapHomologicalComplex (.up ℤ)).obj I)
  have : IsIso (u.app I) := by
    dsimp [u, descentUnitNat]
    infer_instance
  apply (cancel_epi (u.app I)).mp
  have he := ha I
  dsimp [u, v, descentUnitNat] at he ⊢
  simpa only [Category.assoc] using (ha' I hI).trans he.symm

end Square

section Transport

variable {A0 : Type u0} {A1 : Type u1} {B : Type uB}
  {A0' : Type u0'} {A1' : Type u1'} {B' : Type uB'}
  [Category.{v0} A0] [Category.{v1} A1] [Category.{vB} B]
  [Category.{v0'} A0'] [Category.{v1'} A1'] [Category.{vB'} B']
  [Abelian A0] [Abelian A1] [Abelian B] [Abelian A0'] [Abelian A1'] [Abelian B']
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{w0'} A0']
  [HasDerivedCategory.{w1'} A1'] [HasDerivedCategory.{wB'} B']
  (h1 : ∀ N : CochainComplex A1 ℤ,
    ∃ (I : CochainComplex A1 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h1' : ∀ N : CochainComplex A1' ℤ,
    ∃ (I : CochainComplex A1' ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (H : A1 ⥤ A0) (H' : A1' ⥤ A0') [H.Additive] [H'.Additive]
  (E0 : A0 ⥤ B) (E1 : A1 ⥤ B) (E0' : A0' ⥤ B') (E1' : A1' ⥤ B')
  [E0.Additive] [E1.Additive] [E0'.Additive] [E1'.Additive]
  [PreservesFiniteLimits E0] [PreservesFiniteColimits E0]
  [PreservesFiniteLimits E1] [PreservesFiniteColimits E1]
  [PreservesFiniteLimits E0'] [PreservesFiniteColimits E0']
  [PreservesFiniteLimits E1'] [PreservesFiniteColimits E1']
  (U0 : A0 ⥤ A0') (U1 : A1 ⥤ A1') (W : B ⥤ B')
  [U0.Additive] [U1.Additive] [W.Additive]
  [U0.IsEquivalence] [U1.IsEquivalence] [W.IsEquivalence]
  [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
  [PreservesFiniteLimits U1] [PreservesFiniteColimits U1]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]

set_option linter.unusedSectionVars false in
/-- Exact equivalences carry the normalized descent comparison to the normalized
comparison for the transported data, with its full compatibility square.
Source: Stacks 070I and 08BJ, node proof step 10
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: the exact epsilon comparisons descend by localization. At a K-injective I,
U1I remains K-injective. Substituting the normalizations of r, r' and a into the two
composites reduces their equality to Q of the given underived compatibility equation.
Every object is isomorphic to QI, so naturality and cancellation extend the equality to
all objects. This is the comparison agreement asserted in proof step 10.
-/
theorem normalizedKInjectiveDescent_equivalence
    (c : H ⋙ E0 ≅ E1) (c' : H' ⋙ E0' ≅ E1')
    (α : U1 ⋙ H' ≅ H ⋙ U0)
    (ε0 : U0 ⋙ E0' ≅ E0 ⋙ W) (ε1 : U1 ⋙ E1' ≅ E1 ⋙ W)
    (hc : ∀ X : A1,
      c'.hom.app (U1.obj X) ≫ ε1.hom.app X =
        E0'.map (α.hom.app X) ≫ ε0.hom.app (H.obj X) ≫ W.map (c.hom.app X))
    (r : H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ E0.mapDerivedCategory ≅
      E1.mapDerivedCategory)
    (r' : H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ⋙ E0'.mapDerivedCategory ≅
      E1'.mapDerivedCategory)
    (a : U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ≅
      H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory)
    (hr : IsNormalizedKInjectiveDescent h1 H E0 E1 c r)
    (hr' : IsNormalizedKInjectiveDescent h1' H' E0' E1' c' r')
    (ha : IsNormalizedKInjectiveSquare h1 h1' H H' U0 U1 α a) :
    ∀ X : DerivedCategory A1,
      r'.hom.app (U1.mapDerivedCategory.obj X) ≫
          (mapDerivedCategorySquareIso ε1).hom.app X =
        E0'.mapDerivedCategory.map (a.hom.app X) ≫
          (mapDerivedCategorySquareIso ε0).hom.app
            ((H.rightDerivedFunctorOfQuasiIsoResolutions h1).obj X) ≫
          W.mapDerivedCategory.map (r.hom.app X) := by
  let l := whiskerLeft U1.mapDerivedCategory r'.hom ≫
    (mapDerivedCategorySquareIso ε1).hom
  let q := whiskerRight a.hom E0'.mapDerivedCategory ≫
    whiskerLeft (H.rightDerivedFunctorOfQuasiIsoResolutions h1)
      (mapDerivedCategorySquareIso ε0).hom ≫ whiskerRight r.hom W.mapDerivedCategory
  apply representative_app_eq h1 l q
  intro I hI
  let UI := (U1.mapHomologicalComplex (.up ℤ)).obj I
  have := descentUnit_isIso H' h1' UI
  apply (cancel_epi (E0'.mapDerivedCategory.map
    (kInjectiveDescentUnit H' h1' UI ≫
      (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map
        (U1.mapDerivedCategoryFactors.inv.app I)))).mp
  apply (cancel_mono (W.mapDerivedCategory.map (E1.mapDerivedCategoryFactors.hom.app I) ≫
    W.mapDerivedCategoryFactors.hom.app ((E1.mapHomologicalComplex (.up ℤ)).obj I))).mp
  dsimp only [l, q, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn0 := r'.hom.naturality (U1.mapDerivedCategoryFactors.inv.app I)
  dsimp only [Functor.comp_map] at hn0
  rw [reassoc_of% hn0]
  have he1 := square_factors ε1 I
  have he0 := square_factors ε0 ((H.mapHomologicalComplex (.up ℤ)).obj I)
  have hn' := hr' UI inferInstance
  have hn := hr I hI
  have hs := ha I hI
  have he1' := congrArg
    (fun z ↦ E1'.mapDerivedCategory.map (U1.mapDerivedCategoryFactors.inv.app I) ≫ z) he1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp] at he1'
  have he0' := congrArg
    (fun z ↦ E0'.mapDerivedCategory.map
      (U0.mapDerivedCategoryFactors.inv.app ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≫ z)
    he0
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp] at he0'
  erw [he1']
  erw [reassoc_of% hn']
  symm
  erw [← E0'.mapDerivedCategory.map_comp_assoc,
    ← E0'.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hs]
  simp only [Functor.map_comp, Category.assoc]
  have hn3 := (mapDerivedCategorySquareIso ε0).hom.naturality
    (kInjectiveDescentUnit H h1 I)
  dsimp only [Functor.comp_map] at hn3
  erw [reassoc_of% hn3]
  erw [← W.mapDerivedCategory.map_comp_assoc, ← W.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hn]
  simp only [Functor.map_comp, Category.assoc]
  have hn4 := W.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I)
  dsimp only [Functor.comp_map] at hn4
  erw [hn4]
  erw [reassoc_of% he0']
  erw [E0'.mapDerivedCategoryFactors.hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I)]
  dsimp only [Functor.comp_map]
  simp only [← Functor.map_comp]
  have hcomp :
      (E0'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) ≫
        (NatTrans.mapHomologicalComplex ε0.hom (.up ℤ)).app
          ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (W.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) =
      (NatTrans.mapHomologicalComplex c'.hom (.up ℤ)).app UI ≫
        (NatTrans.mapHomologicalComplex ε1.hom (.up ℤ)).app I := by
    ext n
    exact (hc (I.X n)).symm
  erw [hcomp]
  rfl

end Transport

section CompositorTransport

variable {A0 : Type u0} {A1 : Type u1} {A2 : Type u2}
  {A0' : Type u0'} {A1' : Type u1'} {A2' : Type u2'}
  [Category.{v0} A0] [Category.{v1} A1] [Category.{v2} A2]
  [Category.{v0'} A0'] [Category.{v1'} A1'] [Category.{v2'} A2']
  [Abelian A0] [Abelian A1] [Abelian A2] [Abelian A0'] [Abelian A1'] [Abelian A2']
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w0'} A0']
  [HasDerivedCategory.{w1'} A1'] [HasDerivedCategory.{w2'} A2']
  (h1 : ∀ N : CochainComplex A1 ℤ,
    ∃ (I : CochainComplex A1 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h2 : ∀ N : CochainComplex A2 ℤ,
    ∃ (I : CochainComplex A2 ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h1' : ∀ N : CochainComplex A1' ℤ,
    ∃ (I : CochainComplex A1' ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (h2' : ∀ N : CochainComplex A2' ℤ,
    ∃ (I : CochainComplex A2' ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
  (H : A1 ⥤ A0) (J : A2 ⥤ A1) (P : A2 ⥤ A0)
  (H' : A1' ⥤ A0') (J' : A2' ⥤ A1') (P' : A2' ⥤ A0')
  [H.Additive] [J.Additive] [P.Additive] [H'.Additive] [J'.Additive] [P'.Additive]
  (U0 : A0 ⥤ A0') (U1 : A1 ⥤ A1') (U2 : A2 ⥤ A2')
  [U0.Additive] [U1.Additive] [U2.Additive]
  [U0.IsEquivalence] [U1.IsEquivalence] [U2.IsEquivalence]
  [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
  [PreservesFiniteLimits U1] [PreservesFiniteColimits U1]
  [PreservesFiniteLimits U2] [PreservesFiniteColimits U2]

set_option linter.unusedSectionVars false in
/-- The normalized compositor also agrees under exact equivalences.
Source: Stacks 070I and 08BJ, node proof step 10, final sentence
(blueprint: lem-sfb-exact-postcomposition-kinjective-descent).

Proof plan: U2 sends each K-injective I to a K-injective. Insert the unit normalizations
of the two compositors and the three transport squares. On I the two composites become
Q of the stated compatibility between d, d' and the alpha comparisons. The Hom bijection,
naturality, and cancellation along resolutions extend this equality to every derived
object, exactly as for descent transport in proof step 10.
-/
theorem normalizedKInjectiveCompositor_equivalence
    (d : P ≅ J ⋙ H) (d' : P' ≅ J' ⋙ H')
    (αH : U1 ⋙ H' ≅ H ⋙ U0) (αJ : U2 ⋙ J' ≅ J ⋙ U1)
    (αP : U2 ⋙ P' ≅ P ⋙ U0)
    (hd : ∀ X : A2,
      d'.hom.app (U2.obj X) ≫ H'.map (αJ.hom.app X) ≫ αH.hom.app (J.obj X) =
        αP.hom.app X ≫ U0.map (d.hom.app X))
    (aH : U1.mapDerivedCategory ⋙ H'.rightDerivedFunctorOfQuasiIsoResolutions h1' ≅
      H.rightDerivedFunctorOfQuasiIsoResolutions h1 ⋙ U0.mapDerivedCategory)
    (aJ : U2.mapDerivedCategory ⋙ J'.rightDerivedFunctorOfQuasiIsoResolutions h2' ≅
      J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙ U1.mapDerivedCategory)
    (aP : U2.mapDerivedCategory ⋙ P'.rightDerivedFunctorOfQuasiIsoResolutions h2' ≅
      P.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙ U0.mapDerivedCategory)
    (haH : IsNormalizedKInjectiveSquare h1 h1' H H' U0 U1 αH aH)
    (haJ : IsNormalizedKInjectiveSquare h2 h2' J J' U1 U2 αJ aJ)
    (haP : IsNormalizedKInjectiveSquare h2 h2' P P' U0 U2 αP aP)
    (κ : P.rightDerivedFunctorOfQuasiIsoResolutions h2 ≅
      J.rightDerivedFunctorOfQuasiIsoResolutions h2 ⋙
        H.rightDerivedFunctorOfQuasiIsoResolutions h1)
    (κ' : P'.rightDerivedFunctorOfQuasiIsoResolutions h2' ≅
      J'.rightDerivedFunctorOfQuasiIsoResolutions h2' ⋙
        H'.rightDerivedFunctorOfQuasiIsoResolutions h1')
    (hκ : IsNormalizedKInjectiveCompositor h1 h2 H J P d κ)
    (hκ' : IsNormalizedKInjectiveCompositor h1' h2' H' J' P' d' κ') :
    ∀ X : DerivedCategory A2,
      κ'.hom.app (U2.mapDerivedCategory.obj X) ≫
          (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map (aJ.hom.app X) ≫
          aH.hom.app ((J.rightDerivedFunctorOfQuasiIsoResolutions h2).obj X) =
        aP.hom.app X ≫ U0.mapDerivedCategory.map (κ.hom.app X) := by
  let l := whiskerLeft U2.mapDerivedCategory κ'.hom ≫
    whiskerRight aJ.hom (H'.rightDerivedFunctorOfQuasiIsoResolutions h1') ≫
    whiskerLeft (J.rightDerivedFunctorOfQuasiIsoResolutions h2) aH.hom
  let q := aP.hom ≫ whiskerRight κ.hom U0.mapDerivedCategory
  apply representative_app_eq h2 l q
  intro I hI
  let UI := (U2.mapHomologicalComplex (.up ℤ)).obj I
  have := descentUnit_isIso P' h2' UI
  apply (cancel_epi (kInjectiveDescentUnit P' h2' UI ≫
    (P'.rightDerivedFunctorOfQuasiIsoResolutions h2').map
      (U2.mapDerivedCategoryFactors.inv.app I))).mp
  dsimp only [l, q, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  simp only [Category.assoc]
  have hn0 := κ'.hom.naturality (U2.mapDerivedCategoryFactors.inv.app I)
  dsimp only [Functor.comp_map] at hn0
  rw [reassoc_of% hn0]
  have hk := hκ I hI
  have hk' := hκ' UI inferInstance
  have hP := haP I hI
  have hJ := haJ I hI
  have hH := square_normalization_all h1 h1' H H' U0 U1 αH aH haH
    ((J.mapHomologicalComplex (.up ℤ)).obj I)
  rw [reassoc_of% hk']
  rw [← (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map_comp_assoc,
    ← (H'.rightDerivedFunctorOfQuasiIsoResolutions h1').map_comp_assoc]
  simp only [Category.assoc]
  rw [hJ]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% descentUnit_naturality H' h1'
    ((NatTrans.mapHomologicalComplex αJ.hom (.up ℤ)).app I)]
  have hn1 := aH.hom.naturality (kInjectiveDescentUnit J h2 I)
  dsimp only [Functor.comp_map] at hn1
  erw [hn1]
  erw [reassoc_of% hH]
  rw [reassoc_of% hP]
  conv_rhs => rw [← U0.mapDerivedCategory.map_comp, hk]
  simp only [Functor.map_comp]
  have hn2 := U0.mapDerivedCategoryFactors.inv.naturality
    ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I)
  dsimp only [Functor.comp_map] at hn2
  erw [← reassoc_of% hn2]
  simp only [← Functor.map_comp_assoc]
  have hcomp :
      (NatTrans.mapHomologicalComplex d'.hom (.up ℤ)).app UI ≫
        (H'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex αJ.hom (.up ℤ)).app I) ≫
        (NatTrans.mapHomologicalComplex αH.hom (.up ℤ)).app
          ((J.mapHomologicalComplex (.up ℤ)).obj I) =
      (NatTrans.mapHomologicalComplex αP.hom (.up ℤ)).app I ≫
        (U0.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app I) := by
    ext n
    exact hd (I.X n)
  erw [hcomp]
  rfl

end CompositorTransport

end CategoryTheory.Functor
