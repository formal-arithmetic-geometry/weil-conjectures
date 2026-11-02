/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Localization preserves the ordinary component-square coherence equations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

section Identity

universe v w d
variable {A B : Type w} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ B) (H : A ⥤ A)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_identity (e : F ⋙ G ≅ H ⋙ F) (i : H ≅ 𝟭 A) (j : G ≅ 𝟭 B)
    (h : ∀ M, e.hom.app M ≫ F.map (i.hom.app M) = j.hom.app (F.obj M))
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategorySquareIso e).hom.app K ≫
        F.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso i ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app K) =
      (Functor.mapDerivedCategoryNatIso j ≪≫
        Functor.mapDerivedCategoryIdIso B).hom.app (F.mapDerivedCategory.obj K) := by
  have he : e ≪≫ Functor.isoWhiskerRight i F = Functor.isoWhiskerLeft F j := by
    ext M
    exact h M
  have hi := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight i F) K
  have hj := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F j) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hv := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  have ht := congr_app (Functor.mapDerivedCategoryNatIso_trans e
    (Functor.isoWhiskerRight i F)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.id_app] at hi hj hu hv ht
  rw [he] at ht
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hi, hu]
  erw [Category.comp_id]
  rw [← reassoc_of% hj, hv]
  erw [Category.comp_id]
  exact ht.symm

private theorem derived_composition
    (ef : a ⋙ f ≅ h ⋙ b) (eg : b ⋙ g ≅ k ⋙ c) (efg : a ⋙ fg ≅ hk ⋙ c)
    (i : fg ≅ f ⋙ g) (j : hk ≅ h ⋙ k)
    (hh : ∀ M, i.hom.app (a.obj M) ≫ g.map (ef.hom.app M) ≫
      eg.hom.app (h.obj M) = efg.hom.app M ≫ c.map (j.hom.app M))
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryTriangleIso i).hom.app (a.mapDerivedCategory.obj K) ≫
        g.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso ef).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso eg).hom.app (h.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso efg).hom.app K ≫
        c.mapDerivedCategory.map ((Functor.mapDerivedCategoryTriangleIso j).hom.app K) := by
  have he : Functor.isoWhiskerLeft a i ≪≫ Functor.isoWhiskerRight ef g ≪≫
      Functor.isoWhiskerLeft h eg = efg ≪≫ Functor.isoWhiskerRight j c := by
    ext M
    exact hh M
  have hi := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft a i) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc a f g) K
  have hf := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight ef g) K
  have hb := congr_app (Functor.mapDerivedCategoryCompIso_assoc h b g) K
  have hg := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft h eg) K
  have hc := congr_app (Functor.mapDerivedCategoryCompIso_assoc h k c) K
  have hj := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight j c) K
  have ht := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) he
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at ht
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hi ha hf hb hg hc hj
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso a fg).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hi, reassoc_of% ha]
  rw [← g.mapDerivedCategory.map_comp_assoc]
  simp only [Iso.hom_inv_id_app]
  erw [g.mapDerivedCategory.map_id, Category.id_comp]
  rw [← reassoc_of% hf, ← reassoc_of% hb]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hg, hc, ← reassoc_of% hj]
  rw [reassoc_of% ht]

/-- The normalized ordinary identity and composition laws pass to the unbounded
exact derived functors. Source: HRS construction (4.1), naturality used in Corollary 4.4(2);
exact-functor localization (blueprint: lem-zl-component-derived-square-coherence).

Proof: extensionality turns each ordinary component equation into an equality of
pasted natural isomorphisms. Apply `mapDerivedCategoryNatIso` to these equalities.
Its composition and whiskering laws move each comparison through the canonical
composition maps. The unit laws cancel the identity comparisons, giving the first
equation. For the second equation the associativity law moves the two intermediate
composition comparisons together; their inverse pairs cancel. The remaining equality
is exactly the derived image of the ordinary pasted-isomorphism equation. This uses
only exact-functor localization and needs no tensor structure. -/
theorem component_derived_square_coherence
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinarySystem Λ) :
    (∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((s.square (𝟙 X)).theta Λ).hom.app K ≫
        ((s.corner X).derived Λ X).map (((s.sliceIdentity X).derived Λ X).hom.app K) =
      (schemeIdentity Λ X).hom.app (((s.corner X).derived Λ X).obj K)) ∧
    (∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (schemeComposition Λ f g).hom.app (((s.corner X).derived Λ X).obj K) ≫
        (CondensedRing.upperStar Λ.X g).mapDerivedCategory.map
          (((s.square f).theta Λ).hom.app K) ≫
        ((s.square g).theta Λ).hom.app (((s.slice f).derived Λ).obj K) =
      ((s.square (g ≫ f)).theta Λ).hom.app K ≫
        ((s.corner Z).derived Λ Z).map (((s.sliceComposition f g).derived Λ).hom.app K)) := by
  constructor
  · intro X _ K
    unfold Square.theta SliceIdentity.derived schemeIdentity leftPath rightPath
      Corner.derived Slice.derived
    exact derived_identity ((s.corner X).modules Λ X)
      (CondensedRing.upperStar Λ.X (𝟙 X)) ((s.slice (𝟙 X)).modules Λ)
      (s.square (𝟙 X)).ordinary (s.sliceIdentity X).ordinary
      (CondensedRing.upperStarId Λ.X X) (s.identity X) K
  · intro X Y Z _ _ _ f g K
    unfold Square.theta SliceComposition.derived schemeComposition leftPath rightPath
      Corner.derived Slice.derived
    exact derived_composition
      ((s.corner X).modules Λ X) ((s.corner Y).modules Λ Y) ((s.corner Z).modules Λ Z)
      (CondensedRing.upperStar Λ.X f) (CondensedRing.upperStar Λ.X g)
      (CondensedRing.upperStar Λ.X (g ≫ f))
      ((s.slice f).modules Λ) ((s.slice g).modules Λ) ((s.slice (g ≫ f)).modules Λ)
      (s.square f).ordinary (s.square g).ordinary (s.square (g ≫ f)).ordinary
      (CondensedRing.upperStarComp Λ.X g f) (s.sliceComposition f g).ordinary
      (s.composition X Y Z f g) K

end Identity

section Composition

universe v w d
variable {A B C D E H : Type w}
  [Category.{v} A] [Category.{v} B] [Category.{v} C]
  [Category.{v} D] [Category.{v} E] [Category.{v} H]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian H]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] [HasDerivedCategory.{d} C]
  [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} H]
  (a : A ⥤ B) (b : C ⥤ D) (c : E ⥤ H)
  (f : B ⥤ D) (g : D ⥤ H) (fg : B ⥤ H)
  (h : A ⥤ C) (k : C ⥤ E) (hk : A ⥤ E)
  [a.Additive] [b.Additive] [c.Additive] [f.Additive] [g.Additive] [fg.Additive]
  [h.Additive] [k.Additive] [hk.Additive]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits fg] [PreservesFiniteColimits fg]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]
  [PreservesFiniteLimits k] [PreservesFiniteColimits k]
  [PreservesFiniteLimits hk] [PreservesFiniteColimits hk]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Composition

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
