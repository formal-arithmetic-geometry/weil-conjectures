/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs
public import Sheaf.CategoryTheory.ExactAdjointTowerModels
import Sheaf.CategoryTheory.FlatRestrictionExactLeftAdjoint
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Flat scalars and the normalized direct-image/strict-limit square

Source: blueprint main-20261015, proper base change, completed exchange coherence,
second paragraph; scalar supplement using Stacks Tags 0A07, 08BJ, 070I, 070Y and 070K
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

The auxiliary structures merely bundle the universal units and their normalization
identities. Ordinary scalar-limit maps are fixed by `limit.post`, which sends a
compatible family to the same family. Positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w uA uB uA' uB' vA vB vA' vB'

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ExactAdjointTowerModels

namespace CategoryTheory.FlatScalarTowerLimit

-- Infer the category from the equation before elaborating its common final factor.
private theorem post_eq
    {E : Type uA} [Category.{vA} E] {X Y Z : E} {f g : X ⟶ Y}
    (h : f = g) (k : Y ⟶ Z) : f ≫ k = g ≫ k :=
  congrArg (fun t : X ⟶ Y ↦ t ≫ k) h

private theorem pre_eq
    {E : Type uA} [Category.{vA} E] {X Y Z : E} {f g : Y ⟶ Z}
    (h : f = g) (k : X ⟶ Y) : k ≫ f = k ≫ g :=
  congrArg (fun t : Y ⟶ Z ↦ k ≫ t) h

private theorem map_three
    {E : Type uA} [Category.{vA} E] {T : Type uB} [Category.{vB} T]
    (F : E ⥤ T) {X Y Z W : E} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

-- Comparisons can be descended directly from the two units on K-injectives.
private theorem normalized_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {T : Type uB} [Category.{vB} T]
    (F : CochainComplex A ℤ ⥤ T) (P R : DerivedCategory A ⥤ T)
    (a : F ⟶ DerivedCategory.Q ⋙ P) (b : F ⟶ DerivedCategory.Q ⋙ R)
    (ha : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (a.app I))
    (hb : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (b.app I)) :
    ∃ e : P ≅ R, ∀ I, a.app I ≫ e.hom.app (DerivedCategory.Q.obj I) = b.app I := by
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives F := by
    intro I J f hf
    have := I.property
    have := J.property
    have : QuasiIso f.hom := hf
    have := ha I.obj I.property
    have := ha J.obj J.property
    have he : F.map f.hom = a.app I.obj ≫ P.map (DerivedCategory.Q.map f.hom) ≫
        inv (a.app J.obj) := by
      have hn := a.naturality f.hom
      dsimp only [Functor.comp_map] at hn
      apply (cancel_mono (a.app J.obj)).mp
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hn
    change IsIso (F.map f.hom)
    rw [he]
    infer_instance
  have := h.isRightDerivedFunctor_of_isIso a (fun I ↦ ha I.obj I.property)
  have := h.isRightDerivedFunctor_of_isIso b (fun I ↦ hb I.obj I.property)
  refine ⟨Functor.rightDerivedUnique P R a b (HomologicalComplex.quasiIso A (.up ℤ)), ?_⟩
  intro I
  simpa only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app P R a b
    (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 F) I

private theorem derived_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {T : Type uB} [Category.{vB} T]
    {P R : DerivedCategory A ⥤ T} (a b : P ⟶ R)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext Z
  let K := DerivedCategory.Q.objPreimage Z
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hf
  let e : Z ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫ asIso (DerivedCategory.Q.map f)
  apply (cancel_mono (R.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, h I hI]

private theorem tower_preserves_kInjectives
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] (L : A ⥤ B) (R : B ⥤ A)
    [L.Additive] [R.Additive] [PreservesFiniteLimits L]
    (adj : L ⊣ R) :
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj R).PreservesKInjectiveComplexes := by
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj L) :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesLimitsOfShape _⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj L) :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesColimitsOfShape _⟩
  exact (Adjunction.whiskerRight ℕᵒᵖ adj).preservesKInjectiveComplexes

section Normalizations

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

/-- The ordinary and derived scalar comparison, retaining both exact-localization
factors and the equation with universal right-derived units on K-injectives.
Source: Stacks Tags 070I, 070Y and 070K, scalar supplement to completed exchange coherence
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
structure ScalarComparison
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    [F'.Additive] [F.Additive] [r.Additive] [s.Additive]
    (rD : DerivedCategory A' ⥤ DerivedCategory A)
    (sD : DerivedCategory B' ⥤ DerivedCategory B)
    (qr : DerivedCategory.Q ⋙ rD ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qs : DerivedCategory.Q ⋙ sD ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M' : DerivedModel (F'.mapHomologicalComplex (.up ℤ)))
    (M : DerivedModel (F.mapHomologicalComplex (.up ℤ))) where
  ordinary : F' ⋙ s ≅ r ⋙ F
  derived : M'.functor ⋙ sD ≅ rD ⋙ M.functor
  normalized : ∀ I : CochainComplex A' ℤ, I.IsKInjective →
    sD.map (M'.unit.app I) ≫ derived.hom.app (DerivedCategory.Q.obj I) ≫
        M.functor.map (qr.hom.app I) =
      qs.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        M.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I)

/-- The additive structure of ordinary limit, supplied by Mathlib's limit-preservation
criterion, so additivity is not an extra hypothesis of the scalar square.
Source: Stacks Tag 02MZ (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev limitAdditive {E : Type uA} [Category.{vA} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] :
    (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [instance] limitAdditive

variable [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- The canonical direct-image/limit comparison, with its ordinary projection
characterization and common-composite universal-unit normalization.
Source: Stacks Tag 0A07, as specified by ringedTowerPushforwardLimitComparison
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
structure PushforwardComparison
    (F : A ⥤ B) [F.Additive]
    (MF : DerivedModel (F.mapHomologicalComplex (.up ℤ)))
    (MT : DerivedModel (tower F))
    (LA : DerivedModel ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)))
    (LB : DerivedModel ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ))) where
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim
  projections : ∀ T : ℕᵒᵖ ⥤ A, ordinary.hom.app T = limit.post T F
  derived : LA.functor ⋙ MF.functor ≅ MT.functor ⋙ LB.functor
  normalized : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    MF.unit.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        MF.functor.map (LA.unit.app I) ≫ derived.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        LB.unit.app ((tower F).obj I) ≫ LB.functor.map (MT.unit.app I)

omit [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] in
private theorem scalarComparison_exists
    [Abelian.HasKInjectiveResolutions A']
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    [F'.Additive] [F.Additive] [r.Additive] [s.Additive]
    [r.PreservesKInjectiveComplexes]
    (rD : DerivedCategory A' ⥤ DerivedCategory A)
    (sD : DerivedCategory B' ⥤ DerivedCategory B)
    (qr : DerivedCategory.Q ⋙ rD ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qs : DerivedCategory.Q ⋙ sD ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M' : DerivedModel (F'.mapHomologicalComplex (.up ℤ)))
    (M : DerivedModel (F.mapHomologicalComplex (.up ℤ)))
    (c : F' ⋙ s ≅ r ⋙ F) :
    ∃ e : ScalarComparison F' F r s rD sD qr qs M' M, e.ordinary = c ∧
      ∀ I : CochainComplex A' ℤ,
        sD.map (M'.unit.app I) ≫ e.derived.hom.app (DerivedCategory.Q.obj I) ≫
            M.functor.map (qr.hom.app I) =
          qs.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I) ≫
            M.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I) := by
  let a : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (M'.functor ⋙ sD) :=
    Functor.whiskerLeft (F'.mapHomologicalComplex (.up ℤ)) qs.inv ≫
      Functor.whiskerRight M'.unit sD
  let b : (F' ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (rD ⋙ M.functor) :=
    Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q ≫
      Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) M.unit ≫
      Functor.whiskerRight qr.inv M.functor
  obtain ⟨e, he⟩ := normalized_iso _ _ _ a b (by
    intro I hI
    have := M'.on_injectives I hI
    dsimp [a]
    infer_instance) (by
    intro I hI
    have := hI
    have := M.on_injectives ((r.mapHomologicalComplex (.up ℤ)).obj I) inferInstance
    dsimp [b]
    infer_instance)
  have hn (I : CochainComplex A' ℤ) :
      sD.map (M'.unit.app I) ≫ e.hom.app (DerivedCategory.Q.obj I) ≫
          M.functor.map (qr.hom.app I) =
        qs.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I) ≫
          M.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I) := by
    have h := he I
    dsimp [a, b] at h
    apply (cancel_epi (qs.inv.app ((F'.mapHomologicalComplex (.up ℤ)).obj I))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have h' := post_eq h (M.functor.map (qr.hom.app I))
    simpa [Category.assoc, ← M.functor.map_comp] using h'
  exact ⟨⟨c, e, fun I _ ↦ hn I⟩, rfl, hn⟩

end Normalizations

private theorem ordinary_square
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ A'] [HasLimitsOfShape ℕᵒᵖ B']
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    (c : F' ⋙ s ≅ r ⋙ F)
    (d : (Functor.whiskeringRight ℕᵒᵖ A' B').obj F' ⋙
        (Functor.whiskeringRight ℕᵒᵖ B' B).obj s ≅
      (Functor.whiskeringRight ℕᵒᵖ A' A).obj r ⋙
        (Functor.whiskeringRight ℕᵒᵖ A B).obj F)
    (hd : ∀ T n, (d.hom.app T).app n = c.hom.app (T.obj n))
    (T : ℕᵒᵖ ⥤ A') :
    s.map (limit.post T F') ≫ limit.post (T ⋙ F') s ≫ lim.map (d.hom.app T) =
      c.hom.app (limit T) ≫ F.map (limit.post T r) ≫ limit.post (T ⋙ r) F := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, lim_map, limMap_π, limit.post_π_assoc,
    ← s.map_comp_assoc, limit.post_π, hd]
  change s.map (F'.map (limit.π T n)) ≫ c.hom.app (T.obj n) =
    c.hom.app (limit T) ≫ F.map (limit.post T r) ≫
      limit.post (T ⋙ r) F ≫ limit.π ((T ⋙ r) ⋙ F) n
  rw [limit.post_π, ← F.map_comp, limit.post_π]
  exact c.hom.naturality (limit.π T n)


-- The normalization fields have an abstract categorical API. Keeping the diagram
-- chase at this level avoids repeatedly unfolding the sheaf and chosen-limit data.
set_option maxHeartbeats 700000 in
-- The normalization chase retains arbitrary localization universes and all unit factors.
private theorem square_of_normalized
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ A'] [HasLimitsOfShape ℕᵒᵖ B']
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B')]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')]
    (F : A ⥤ B) (F' : A' ⥤ B') (r : A' ⥤ A) (s : B' ⥤ B)
    [F.Additive] [F'.Additive] [r.Additive] [s.Additive]
    [((Functor.whiskeringRight ℕᵒᵖ A' A).obj r).PreservesKInjectiveComplexes]
    (FR : DerivedModel (F.mapHomologicalComplex (.up ℤ)))
    (TR : DerivedModel (tower F))
    (FS : DerivedModel (F'.mapHomologicalComplex (.up ℤ)))
    (TS : DerivedModel (tower F'))
    (LRU : DerivedModel ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)))
    (LSU : DerivedModel ((lim : (ℕᵒᵖ ⥤ A') ⥤ A').mapHomologicalComplex (.up ℤ)))
    (LRV : DerivedModel ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)))
    (LSV : DerivedModel ((lim : (ℕᵒᵖ ⥤ B') ⥤ B').mapHomologicalComplex (.up ℤ)))
    (rU : DerivedCategory A' ⥤ DerivedCategory A)
    (rtU : DerivedCategory (ℕᵒᵖ ⥤ A') ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
    (qU : DerivedCategory.Q ⋙ rU ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtU : DerivedCategory.Q ⋙ rtU ≅ tower r ⋙ DerivedCategory.Q)
    (rV : DerivedCategory B' ⥤ DerivedCategory B)
    (rtV : DerivedCategory (ℕᵒᵖ ⥤ B') ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (qV : DerivedCategory.Q ⋙ rV ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtV : DerivedCategory.Q ⋙ rtV ≅ tower s ⋙ DerivedCategory.Q)
    (χ : ScalarComparison F' F r s rU rV qU qV FS FR)
    (d : ScalarComparison
      ((Functor.whiskeringRight ℕᵒᵖ A' B').obj F')
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ A' A).obj r)
      ((Functor.whiskeringRight ℕᵒᵖ B' B).obj s) rtU rtV qtU qtV TS TR)
    (ordinaryd : ∀ (T : ℕᵒᵖ ⥤ A') (n : ℕᵒᵖ),
      (d.ordinary.hom.app T).app n = χ.ordinary.hom.app (T.obj n))
    (κR : PushforwardComparison F FR TR LRU LRV)
    (κS : PushforwardComparison F' FS TS LSU LSV)
    (lambdaU : ScalarComparison (lim : (ℕᵒᵖ ⥤ A') ⥤ A') (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
      ((Functor.whiskeringRight ℕᵒᵖ A' A).obj r) r rtU rU qtU qU LSU LRU)
    (lambdaV : ScalarComparison (lim : (ℕᵒᵖ ⥤ B') ⥤ B') (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
      ((Functor.whiskeringRight ℕᵒᵖ B' B).obj s) s rtV rV qtV qV LSV LRV)
    (hpU : ∀ T, lambdaU.ordinary.hom.app T = limit.post T r)
    (hpV : ∀ T, lambdaV.ordinary.hom.app T = limit.post T s)
    (hnU : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A') ℤ,
      rU.map (LSU.unit.app I) ≫ lambdaU.derived.hom.app (DerivedCategory.Q.obj I) ≫
          LRU.functor.map (qtU.hom.app I) =
        qU.hom.app (((lim : (ℕᵒᵖ ⥤ A') ⥤ A').mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex lambdaU.ordinary (.up ℤ)).hom.app I) ≫
          LRU.unit.app ((tower r).obj I))
    (hnV : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B') ℤ,
      rV.map (LSV.unit.app I) ≫ lambdaV.derived.hom.app (DerivedCategory.Q.obj I) ≫
          LRV.functor.map (qtV.hom.app I) =
        qV.hom.app (((lim : (ℕᵒᵖ ⥤ B') ⥤ B').mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex lambdaV.ordinary (.up ℤ)).hom.app I) ≫
          LRV.unit.app ((tower s).obj I)) :
    ∀ Z : DerivedCategory (ℕᵒᵖ ⥤ A'),
      rV.map (κS.derived.hom.app Z) ≫ lambdaV.derived.hom.app (TS.functor.obj Z) ≫
          LRV.functor.map (d.derived.hom.app Z) =
        χ.derived.hom.app (LSU.functor.obj Z) ≫ FR.functor.map (lambdaU.derived.hom.app Z) ≫
          κR.derived.hom.app (rtU.obj Z) := by
  let a : LSU.functor ⋙ FS.functor ⋙ rV ⟶ rtU ⋙ TR.functor ⋙ LRV.functor :=
    Functor.whiskerRight κS.derived.hom rV ≫
      Functor.whiskerLeft TS.functor lambdaV.derived.hom ≫
      Functor.whiskerRight d.derived.hom LRV.functor
  let b : LSU.functor ⋙ FS.functor ⋙ rV ⟶ rtU ⋙ TR.functor ⋙ LRV.functor :=
    Functor.whiskerLeft LSU.functor χ.derived.hom ≫
      Functor.whiskerRight lambdaU.derived.hom FR.functor ≫
      Functor.whiskerLeft rtU κR.derived.hom
  have hab : a = b := by
    apply derived_ext
    intro I hI
    have := hI
    let LC := (lim : (ℕᵒᵖ ⥤ A') ⥤ A').mapHomologicalComplex (.up ℤ)
    let RC := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
    let LV := (lim : (ℕᵒᵖ ⥤ B') ⥤ B').mapHomologicalComplex (.up ℤ)
    let sU := (r).mapHomologicalComplex (.up ℤ)
    let RV := (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)
    let FU := F.mapHomologicalComplex (.up ℤ)
    let FS' := F'.mapHomologicalComplex (.up ℤ)
    let sV := (s).mapHomologicalComplex (.up ℤ)
    let it := (tower (r)).obj I
    let jt := (tower F').obj I
    let cs : FS'.obj (LC.obj I) ⟶ LV.obj jt :=
      { f := fun p ↦ κS.ordinary.hom.app (I.X p)
        comm' := fun p q _ ↦ (κS.ordinary.hom.naturality (I.d p q)).symm }
    let cr : FU.obj (RC.obj it) ⟶ RV.obj ((tower F).obj it) :=
      { f := fun p ↦ κR.ordinary.hom.app (it.X p)
        comm' := fun p q _ ↦ (κR.ordinary.hom.naturality (it.d p q)).symm }
    let lu : sU.obj (LC.obj I) ⟶ RC.obj it :=
      { f := fun p ↦ lambdaU.ordinary.hom.app (I.X p)
        comm' := fun p q _ ↦ (lambdaU.ordinary.hom.naturality (I.d p q)).symm }
    let lv : sV.obj (LV.obj jt) ⟶ RV.obj ((tower (s)).obj jt) :=
      { f := fun p ↦ lambdaV.ordinary.hom.app (jt.X p)
        comm' := fun p q _ ↦ (lambdaV.ordinary.hom.naturality (jt.d p q)).symm }
    let cc : sV.obj (FS'.obj (LC.obj I)) ⟶ FU.obj (sU.obj (LC.obj I)) :=
      { f := fun p ↦ χ.ordinary.hom.app ((LC.obj I).X p)
        comm' := fun p q _ ↦ (χ.ordinary.hom.naturality ((LC.obj I).d p q)).symm }
    let dd : (tower (s)).obj jt ⟶ (tower F).obj it :=
      { f := fun p ↦ d.ordinary.hom.app (I.X p)
        comm' := fun p q _ ↦ (d.ordinary.hom.naturality (I.d p q)).symm }
    -- Check the ordinary square degreewise by its limit projections.
    have ho : sV.map cs ≫ lv ≫ RV.map dd = cc ≫ FU.map lu ≫ cr := by
      apply HomologicalComplex.hom_ext (V := B) (c := .up ℤ)
      intro p
      change (s).map (κS.ordinary.hom.app (I.X p)) ≫
          lambdaV.ordinary.hom.app (I.X p ⋙ F') ≫
            lim.map (d.ordinary.hom.app (I.X p)) =
        χ.ordinary.hom.app (limit (I.X p)) ≫
          F.map (lambdaU.ordinary.hom.app (I.X p)) ≫
            κR.ordinary.hom.app (I.X p ⋙ r)
      rw [κS.projections (I.X p), κR.projections (I.X p ⋙ r), hpU, hpV]
      exact ordinary_square _ _ _ _ χ.ordinary d.ordinary ordinaryd (I.X p)
    have : (Functor.const ℕᵒᵖ : A' ⥤ (ℕᵒᵖ ⥤ A')).Additive :=
      ⟨by intros; ext n; rfl⟩
    have : (lim : (ℕᵒᵖ ⥤ A') ⥤ A').PreservesKInjectiveComplexes :=
      Adjunction.preservesKInjectiveComplexes
        (G := Functor.const ℕᵒᵖ) (F := lim) constLimAdj
    have hLC : CochainComplex.IsKInjective (LC.obj I) := inferInstance
    have hIt : it.IsKInjective := inferInstance
    have := LSU.on_injectives I hI
    have := FS.on_injectives (LC.obj I) hLC
    -- Both changes of source and target are invertible.
    let pre := rV.map (FS.unit.app (LC.obj I)) ≫
      rV.map (FS.functor.map (LSU.unit.app I))
    let post := LRV.functor.map (TR.functor.map (qtU.hom.app I))
    have : IsIso pre := by dsimp [pre]; infer_instance
    have : IsIso post := by dsimp [post]; infer_instance
    dsimp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    apply (cancel_epi pre).mp
    apply (cancel_mono post).mp
    dsimp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, pre, post]
    have hS := (map_three rV (FS.unit.app (LC.obj I))
      (FS.functor.map (LSU.unit.app I)) (κS.derived.hom.app (DerivedCategory.Q.obj I))).symm.trans
      ((congrArg (fun f ↦ rV.map f) (κS.normalized I hI)).trans
        (map_three rV (DerivedCategory.Q.map cs) (LSV.unit.app jt)
          (LSV.functor.map (TS.unit.app I))))
    have hR := κR.normalized it hIt
    have hχ := χ.normalized (LC.obj I) hLC
    have hd := d.normalized I hI
    have hlU := hnU I
    have hlV := hnV jt
    change rtV.map (TS.unit.app I) ≫ d.derived.hom.app (DerivedCategory.Q.obj I) ≫
      TR.functor.map (qtU.hom.app I) =
        qtV.hom.app jt ≫ DerivedCategory.Q.map dd ≫ TR.unit.app it at hd
    change rV.map (LSV.unit.app jt) ≫ lambdaV.derived.hom.app (DerivedCategory.Q.obj jt) ≫
      LRV.functor.map (qtV.hom.app jt) =
        qV.hom.app (LV.obj jt) ≫ DerivedCategory.Q.map lv ≫
          LRV.unit.app ((tower (s)).obj jt) at hlV
    change rU.map (LSU.unit.app I) ≫ lambdaU.derived.hom.app (DerivedCategory.Q.obj I) ≫
      LRU.functor.map (qtU.hom.app I) =
        qU.hom.app (LC.obj I) ≫ DerivedCategory.Q.map lu ≫ LRU.unit.app it at hlU
    change FR.unit.app (RC.obj it) ≫ FR.functor.map (LRU.unit.app it) ≫
      κR.derived.hom.app (DerivedCategory.Q.obj it) =
        DerivedCategory.Q.map cr ≫ LRV.unit.app ((tower F).obj it) ≫
          LRV.functor.map (TR.unit.app it) at hR
    change rV.map (FS.unit.app (LC.obj I)) ≫
      χ.derived.hom.app (DerivedCategory.Q.obj (LC.obj I)) ≫
        FR.functor.map (qU.hom.app (LC.obj I)) =
      qV.hom.app (FS'.obj (LC.obj I)) ≫ DerivedCategory.Q.map cc ≫
        FR.unit.app (sU.obj (LC.obj I)) at hχ
    have hd' := (map_three LRV.functor (rtV.map (TS.unit.app I))
      (d.derived.hom.app (DerivedCategory.Q.obj I)) (TR.functor.map (qtU.hom.app I))).symm.trans
      ((congrArg (fun f ↦ LRV.functor.map f) hd).trans
        (map_three LRV.functor (qtV.hom.app jt) (DerivedCategory.Q.map dd) (TR.unit.app it)))
    have hu' := (map_three FR.functor (rU.map (LSU.unit.app I))
      (lambdaU.derived.hom.app (DerivedCategory.Q.obj I))
        (LRU.functor.map (qtU.hom.app I))).symm.trans
      ((congrArg (fun f ↦ FR.functor.map f) hlU).trans
        (map_three FR.functor (qU.hom.app (LC.obj I)) (DerivedCategory.Q.map lu)
          (LRU.unit.app it)))
    have nV := lambdaV.derived.hom.naturality (TS.unit.app I)
    have nR := κR.derived.hom.naturality (qtU.hom.app I)
    have nχ := χ.derived.hom.naturality (LSU.unit.app I)
    have nQ := qV.hom.naturality cs
    have nLV := LRV.unit.naturality dd
    have nFU := FR.unit.naturality lu
    dsimp only [Functor.comp_obj, Functor.comp_map] at nV nR nχ nQ nLV nFU
    trans qV.hom.app (FS'.obj (LC.obj I)) ≫
      DerivedCategory.Q.map (sV.map cs ≫ lv ≫ RV.map dd) ≫
        LRV.unit.app ((tower F).obj it) ≫
          LRV.functor.map (TR.unit.app it)
    · -- Normalize the left path using κS, d, and lambdaV.
      simp only [Category.assoc]
      have hs := post_eq hS (lambdaV.derived.hom.app (TS.functor.obj (DerivedCategory.Q.obj I)) ≫
          LRV.functor.map (d.derived.hom.app (DerivedCategory.Q.obj I)) ≫
            LRV.functor.map (TR.functor.map (qtU.hom.app I)))
      simp only [Category.assoc] at hs
      have nv := post_eq nV (LRV.functor.map (d.derived.hom.app (DerivedCategory.Q.obj I)) ≫
          LRV.functor.map (TR.functor.map (qtU.hom.app I)))
      simp only [Category.assoc] at nv
      have nv' := pre_eq nv (rV.map (DerivedCategory.Q.map cs) ≫
        rV.map (LSV.unit.app jt))
      simp only [Category.assoc] at nv'
      have hd'' := pre_eq hd' (rV.map (DerivedCategory.Q.map cs) ≫
        rV.map (LSV.unit.app jt) ≫ lambdaV.derived.hom.app (DerivedCategory.Q.obj jt))
      simp only [Category.assoc] at hd''
      have hv := post_eq hlV (LRV.functor.map (DerivedCategory.Q.map dd) ≫
        LRV.functor.map (TR.unit.app it))
      simp only [Category.assoc] at hv
      have hv' := pre_eq hv (rV.map (DerivedCategory.Q.map cs))
      have nlv := post_eq nLV (LRV.functor.map (TR.unit.app it))
      simp only [Category.assoc] at nlv
      have nlv' := pre_eq nlv.symm
        (rV.map (DerivedCategory.Q.map cs) ≫ qV.hom.app (LV.obj jt) ≫
          DerivedCategory.Q.map lv)
      simp only [Category.assoc] at nlv'
      refine hs.trans (nv'.trans (hd''.trans (hv'.trans (nlv'.trans ?_))))
      simpa only [Category.assoc, Functor.map_comp] using post_eq nQ
        (DerivedCategory.Q.map lv ≫ DerivedCategory.Q.map (RV.map dd) ≫
          LRV.unit.app ((tower F).obj it) ≫
            LRV.functor.map (TR.unit.app it))
    · -- Normalize the right path using lambdaU, χ, and κR.
      simp only [Category.assoc]
      have hm := (congrArg (fun f : sV.obj (FS'.obj (LC.obj I)) ⟶
          RV.obj ((tower F).obj it) ↦
            (DerivedCategory.Q : CochainComplex (B) ℤ ⥤ _).map f) ho).trans
        (map_three DerivedCategory.Q cc (FU.map lu) cr)
      have hm' := post_eq (pre_eq hm (qV.hom.app (FS'.obj (LC.obj I))))
        (LRV.unit.app ((tower F).obj it) ≫
          LRV.functor.map (TR.unit.app it))
      simp only [Category.assoc] at hm'
      refine hm'.trans ?_
      symm
      have nr := pre_eq nR.symm
        (rV.map (FS.unit.app (LC.obj I)) ≫ rV.map (FS.functor.map (LSU.unit.app I)) ≫
          χ.derived.hom.app (LSU.functor.obj (DerivedCategory.Q.obj I)) ≫
            FR.functor.map (lambdaU.derived.hom.app (DerivedCategory.Q.obj I)))
      simp only [Category.assoc] at nr
      have nc := post_eq nχ (FR.functor.map (lambdaU.derived.hom.app (DerivedCategory.Q.obj I)) ≫
          FR.functor.map (LRU.functor.map (qtU.hom.app I)) ≫
            κR.derived.hom.app (DerivedCategory.Q.obj it))
      simp only [Category.assoc] at nc
      have nc' := pre_eq nc (rV.map (FS.unit.app (LC.obj I)))
      have hu := post_eq hu' (κR.derived.hom.app (DerivedCategory.Q.obj it))
      simp only [Category.assoc] at hu
      have hu'' := pre_eq hu (rV.map (FS.unit.app (LC.obj I)) ≫
        χ.derived.hom.app (DerivedCategory.Q.obj (LC.obj I)))
      simp only [Category.assoc] at hu''
      have hc := post_eq hχ (FR.functor.map (DerivedCategory.Q.map lu) ≫
        FR.functor.map (LRU.unit.app it) ≫
          κR.derived.hom.app (DerivedCategory.Q.obj it))
      simp only [Category.assoc] at hc
      have nfu := post_eq nFU (FR.functor.map (LRU.unit.app it) ≫
        κR.derived.hom.app (DerivedCategory.Q.obj it))
      simp only [Category.assoc] at nfu
      have nfu' := pre_eq nfu.symm (qV.hom.app (FS'.obj (LC.obj I)) ≫
        DerivedCategory.Q.map cc)
      simp only [Category.assoc] at nfu'
      have hr := pre_eq hR (qV.hom.app (FS'.obj (LC.obj I)) ≫
        DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map (FU.map lu))
      simp only [Category.assoc] at hr
      exact nr.trans (nc'.trans (hu''.trans (hc.trans (nfu'.trans hr))))
  intro Z
  exact NatTrans.congr_app hab Z


variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}

/-- The RU module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesRU (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.RU)

/-- The SU module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesSU (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)

/-- The RV module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesRV (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.RV)

/-- The SV module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesSV (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.SV)

/-- Actual restriction of scalars at U, using Mathlib's construction.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev scalarU (x : FlatRingedDiagramInput K H) : modulesSU x ⥤ modulesRU x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)

/-- Actual restriction of scalars at V, using Mathlib's construction.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev scalarV (x : FlatRingedDiagramInput K H) : modulesSV x ⥤ modulesRV x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)

set_option maxHeartbeats 700000 in
-- Elaborate the comparison interfaces and the two scalar-restriction adjunctions.
/-- Flat scalar restriction commutes with derived strict inverse limit, and the
normalized direct-image/limit square commutes as an equality on every derived tower.
`χ` and `d` are the specified flat comparisons, normalized by their ordinary identity
and universal units. `κR` and `κS` are the specified comparisons of Tag 0A07.
The output supplies the ordinary family-identity and the derived normalized comparison
at both U and V. No finite reduction, completeness, or exact-products condition occurs.

Source: blueprint main-20261015, completed exchange coherence proof, second paragraph;
scalar supplement using Stacks Tags 0A07 and 08BJ
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

Proof:
1. The exact scalar-extension left adjoints make scalar restriction preserve limits
   and, termwise, K-injectives. Use preservesLimitNatIso for the ordinary comparisons.
2. Source tower categories are Grothendieck abelian and have K-injective resolutions.
   The two unit-normalized composite functors are right derived functors of the same
   ordinary functor. Mathlib's uniqueness isomorphism constructs lambdaU and lambdaV.
   Its universal-unit equation holds on every complex.
3. Limit projections and naturality of the ordinary chi give the ordinary square,
   degreewise on any tower complex.
4. On a K-injective I, ordinary limit and scalar restriction preserve K-injectivity.
   Precompose with the composite LSU/FS unit and postcompose with LRV(TR(qtU)).
   Substitute the kappa, scalar and lambda unit equations and move units by naturality.
   The two sides have identical outer factors around Q of the ordinary square.
   Cancel the pre- and postcomposition isomorphisms.
5. Naturality along a K-injective representative extends the equality to every
   derived tower. No direct-image preservation of K-injectives is needed.
-/
theorem flatScalarTowerLimitSquare
    (x : FlatRingedDiagramInput K H)
    [HasDerivedCategory.{w} (modulesRU x)]
    [HasDerivedCategory.{w} (modulesSU x)]
    [HasDerivedCategory.{w} (modulesRV x)]
    [HasDerivedCategory.{w} (modulesSV x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesRU x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesSU x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesRV x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesSV x)]
    (FR : DerivedModel (x.R.morphism.modules.mapHomologicalComplex (.up ℤ)))
    (TR : DerivedModel (tower x.R.morphism.modules))
    (FS : DerivedModel (x.S.morphism.modules.mapHomologicalComplex (.up ℤ)))
    (TS : DerivedModel (tower x.S.morphism.modules))
    (LRU : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x).mapHomologicalComplex (.up ℤ)))
    (LSU : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x).mapHomologicalComplex (.up ℤ)))
    (LRV : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x).mapHomologicalComplex (.up ℤ)))
    (LSV : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x).mapHomologicalComplex (.up ℤ)))
    (rU : DerivedCategory (modulesSU x) ⥤ DerivedCategory (modulesRU x))
    (rtU : DerivedCategory (ℕᵒᵖ ⥤ modulesSU x) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ modulesRU x))
    (qU : DerivedCategory.Q ⋙ rU ≅
      (scalarU x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtU : DerivedCategory.Q ⋙ rtU ≅ tower (scalarU x) ⋙ DerivedCategory.Q)
    (rV : DerivedCategory (modulesSV x) ⥤ DerivedCategory (modulesRV x))
    (rtV : DerivedCategory (ℕᵒᵖ ⥤ modulesSV x) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ modulesRV x))
    (qV : DerivedCategory.Q ⋙ rV ≅
      (scalarV x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtV : DerivedCategory.Q ⋙ rtV ≅ tower (scalarV x) ⋙ DerivedCategory.Q)
    (χ : ScalarComparison x.S.morphism.modules x.R.morphism.modules
      (scalarU x) (scalarV x) rU rV qU qV FS FR)
    (ordinaryχ : ∀ N : modulesSU x,
      (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
          (χ.ordinary.hom.app N) ≫
        x.R.morphism.underlying.hom.app ((scalarU x).obj N) =
      x.S.morphism.underlying.hom.app N ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).obj N))
            x.sameDirect.symm))
    (d : ScalarComparison
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj x.S.morphism.modules)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj x.R.morphism.modules)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x))
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)) rtU rtV qtU qtV TS TR)
    (ordinaryd : ∀ (T : ℕᵒᵖ ⥤ modulesSU x) (n : ℕᵒᵖ),
      (d.ordinary.hom.app T).app n = χ.ordinary.hom.app (T.obj n))
    (κR : PushforwardComparison x.R.morphism.modules FR TR LRU LRV)
    (κS : PushforwardComparison x.S.morphism.modules FS TS LSU LSV) :
    ∃ (lambdaU : ScalarComparison
        (lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x)
        (lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x)) (scalarU x) rtU rU qtU qU LSU LRU)
      (lambdaV : ScalarComparison
        (lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x)
        (lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)) (scalarV x) rtV rV qtV qV LSV LRV),
      (∀ T : ℕᵒᵖ ⥤ modulesSU x, lambdaU.ordinary.hom.app T = limit.post T (scalarU x)) ∧
      (∀ T : ℕᵒᵖ ⥤ modulesSV x, lambdaV.ordinary.hom.app T = limit.post T (scalarV x)) ∧
      ∀ Z : DerivedCategory (ℕᵒᵖ ⥤ modulesSU x),
        rV.map (κS.derived.hom.app Z) ≫ lambdaV.derived.hom.app (TS.functor.obj Z) ≫
            LRV.functor.map (d.derived.hom.app Z) =
          χ.derived.hom.app (LSU.functor.obj Z) ≫
            FR.functor.map (lambdaU.derived.hom.app Z) ≫ κR.derived.hom.app (rtU.obj Z) := by
  have _ordinaryNormalization := ordinaryχ
  have : H.HasSheafCompose (forget₂ CommRingCat RingCat) := inferInstance
  have : K.HasSheafCompose (forget₂ CommRingCat RingCat) := inferInstance
  let : Abelian (modulesRU x) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ modulesRU x) := inferInstance
  let : Abelian (modulesSU x) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ modulesSU x) := inferInstance
  let : Abelian (modulesRV x) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ modulesRV x) := inferInstance
  let : Abelian (modulesSV x) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ modulesSV x) := inferInstance
  obtain ⟨EU, hEU, hEUlim, ⟨adjU⟩⟩ :=
    SheafOfModules.flatRestriction_exact_leftAdjoint x.aU x.flatU
  obtain ⟨EV, hEV, hEVlim, ⟨adjV⟩⟩ :=
    SheafOfModules.flatRestriction_exact_leftAdjoint x.aV x.flatV
  have := hEU
  have := hEV
  have := hEUlim
  have := hEVlim
  have : x.R.morphism.modules.Additive := x.R.morphism.additive
  have : x.S.morphism.modules.Additive := x.S.morphism.additive
  have : (scalarU x).Additive := inferInstance
  have : (scalarV x).Additive := inferInstance
  have : (lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x).Additive := limitAdditive
  have : (lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x).Additive := limitAdditive
  have : (lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x).Additive := limitAdditive
  have : (lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x).Additive := limitAdditive
  have : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (x.R.morphism.modules)).Additive := inferInstance
  have : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (x.S.morphism.modules)).Additive := inferInstance
  have : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x)).Additive := inferInstance
  have : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)).Additive := inferInstance
  have : (x.R.morphism.modules).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (x.S.morphism.modules).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (scalarU x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (scalarV x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : PreservesLimitsOfShape ℕᵒᵖ (scalarU x) :=
    adjU.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : PreservesLimitsOfShape ℕᵒᵖ (scalarV x) :=
    adjV.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have := tower_preserves_kInjectives EU (scalarU x) adjU
  have := tower_preserves_kInjectives EV (scalarV x) adjV
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ modulesSU x) := by
    have := smallModuleDiagrams_isGrothendieckAbelian H
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ modulesSV x) := by
    have := smallModuleDiagrams_isGrothendieckAbelian K
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.SV)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  obtain ⟨lambdaU, hU, hnU⟩ := scalarComparison_exists
    (lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x)
    (lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x)) (scalarU x)
    rtU rU qtU qU LSU LRU (preservesLimitNatIso (scalarU x))
  obtain ⟨lambdaV, hV, hnV⟩ := scalarComparison_exists
    (lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x)
    (lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)) (scalarV x)
    rtV rV qtV qV LSV LRV (preservesLimitNatIso (scalarV x))
  have hpU (T : ℕᵒᵖ ⥤ modulesSU x) :
      lambdaU.ordinary.hom.app T = limit.post T (scalarU x) := by
    exact NatTrans.congr_app (congrArg Iso.hom hU) T
  have hpV (T : ℕᵒᵖ ⥤ modulesSV x) :
      lambdaV.ordinary.hom.app T = limit.post T (scalarV x) := by
    exact NatTrans.congr_app (congrArg Iso.hom hV) T
  refine ⟨lambdaU, lambdaV, hpU, hpV, ?_⟩
  apply square_of_normalized _ _ _ _ FR TR FS TS LRU LSU LRV LSV
    rU rtU qU qtU rV rtV qV qtV χ d ordinaryd κR κS lambdaU lambdaV hpU hpV
  · intro I
    have h := hnU I
    erw [← hU] at h
    exact h
  · intro I
    have h := hnV I
    erw [← hV] at h
    exact h

end CategoryTheory.FlatScalarTowerLimit
