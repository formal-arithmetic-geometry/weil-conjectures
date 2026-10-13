/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit
import Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit

/-!
# Pre-derived adjunction from essentially constant derived systems

Source: Stacks Project, Derived Categories, Lemma 0DVC, specialized from Lemma 0FND
(blueprint: lem-pc-pre-derived-adjoint-functors-general).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory

namespace CategoryTheory

/-- The pointwise derived Hom comparison, characterized on all fraction representatives,
and natural in both localized variables and their induced maps on representing values.
Source: Stacks Project, Derived Categories, Lemmas 0DVC and 0FND
(blueprint: lem-pc-pre-derived-adjoint-functors-general).

Proof: Use the product diagram of numerators Hom(P,Fh(I)), indexed by outgoing and
incoming quasi-isomorphisms. The source and target double-colimit comparisons identify
its ColimitType bijectively with Hom(QB(M),RF) and Hom(LG,QA(K)), respectively. Compose
the inverse of the first bijection with the second to obtain e. Their representative
formulas give canonicality, and joint surjectivity of colimit representatives gives
uniqueness. To prove naturality, represent an arbitrary source morphism by (s,t,f).
Represent inv(QA(s)) followed by k as a left fraction (a,s'), and m followed by
inv(QB(t)) as a right fraction (t',b). These choices give exactly the hypotheses of
the compatibility equations for r and l. The transformed source is represented by
(s',t', b followed by f followed by Fh(a)). Apply the canonical formulas for e and e',
then naturality of the homotopy adjunction to transpose that composite. Cancellation
of the inverted denominators proves the desired equality. No colimit-interchange
lemma or unproved Hom-colimit theorem is used.

Additivity is explicit: an adjunction between abelian categories makes the left
adjoint preserve finite coproducts and the right adjoint finite products, hence both
are additive. The denominator categories of quasi-isomorphisms under `K` and over `M`
are filtered resp. cofiltered by the calculus of fractions; this is part of the two
essential-constancy hypotheses (the landed predicates of
def-pc-essentially-constant-ind-diagram and def-pc-essentially-constant-pro-diagram).
`splitR`/`splitL` state, for the chosen natural maps `p`/`u`, the remaining clauses of
those predicates, as the node's "chosen representing cocone and cone". -/
theorem preDerivedAdjunctionGeneral
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ A) [G.Additive] (adj : G ⊣ F)
    (K : HomotopyCategory A (ComplexShape.up ℤ))
    (M : HomotopyCategory B (ComplexShape.up ℤ))
    (RF : DerivedCategory B) (LG : DerivedCategory A) :
    let HA := HomotopyCategory A (ComplexShape.up ℤ)
    let HB := HomotopyCategory B (ComplexShape.up ℤ)
    let WA := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
    let WB := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
    let QA := DerivedCategory.Qh (C := A)
    let QB := DerivedCategory.Qh (C := B)
    let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ)
    let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
    let ah := adj.mapHomotopyCategory (ComplexShape.up ℤ)
    let R (X : HA) :=
      MorphismProperty.Under.forget WA ⊤ X ⋙ Under.forget X ⋙ Fh ⋙ QB
    let L (Y : HB) :=
      MorphismProperty.Over.forget WB ⊤ Y ⋙ Over.forget Y ⋙ Gh ⋙ QA
    let left {X Y : HA} (s : WA.Under ⊤ X) (f : Y ⟶ s.right) :=
      (MorphismProperty.LeftFraction.mk f s.hom s.prop).map QA
        (Localization.inverts QA WA)
    let right {X Y : HB} (t : WB.Over ⊤ X) (f : t.left ⟶ Y) :=
      (MorphismProperty.RightFraction.mk t.hom t.prop f).map QB
        (Localization.inverts QB WB)
    let splitR (X : HA) (V : DerivedCategory B)
        (p : R X ⟶ (Functor.const _).obj V) :=
      ∃ (s₀ : WA.Under ⊤ X) (a : V ⟶ (R X).obj s₀),
        a ≫ p.app s₀ = 𝟙 V ∧
          ∀ s, ∃ (s₁ : WA.Under ⊤ X) (b : s₀ ⟶ s₁) (c : s ⟶ s₁),
            (R X).map c = p.app s ≫ a ≫ (R X).map b
    let splitL (Y : HB) (V : DerivedCategory A)
        (u : (Functor.const _).obj V ⟶ L Y) :=
      ∃ (t₀ : WB.Over ⊤ Y) (a : (L Y).obj t₀ ⟶ V),
        u.app t₀ ≫ a = 𝟙 V ∧
          ∀ t, ∃ (t₁ : WB.Over ⊤ Y) (b : t₁ ⟶ t₀) (c : t₁ ⟶ t),
            (L Y).map c = (L Y).map b ≫ a ≫ u.app t
    let canonical (X : HA) (Y : HB) (V : DerivedCategory B) (U : DerivedCategory A)
        (p : R X ⟶ (Functor.const _).obj V)
        (u : (Functor.const _).obj U ⟶ L Y)
        (e : (QB.obj Y ⟶ V) ≃ (U ⟶ QA.obj X)) :=
      ∀ (s : WA.Under ⊤ X) (t : WB.Over ⊤ Y) (f : t.left ⟶ Fh.obj s.right),
        e (right t f ≫ p.app s) =
          u.app t ≫ left s ((ah.homEquiv t.left s.right).symm f)
    IsEssentiallyConstantIndDiagram (R K) RF →
    IsEssentiallyConstantProDiagram (L M) LG →
    ∀ (p : R K ⟶ (Functor.const _).obj RF)
      (u : (Functor.const _).obj LG ⟶ L M),
      splitR K RF p → splitL M LG u →
      ∃! e : (QB.obj M ⟶ RF) ≃ (LG ⟶ QA.obj K),
        canonical K M RF LG p u e ∧
        ∀ (K' : HA) (M' : HB) (RF' : DerivedCategory B) (LG' : DerivedCategory A)
          (p' : R K' ⟶ (Functor.const _).obj RF')
          (u' : (Functor.const _).obj LG' ⟶ L M')
          (e' : (QB.obj M' ⟶ RF') ≃ (LG' ⟶ QA.obj K')),
          canonical K' M' RF' LG' p' u' e' →
          ∀ (k : QA.obj K ⟶ QA.obj K') (m : QB.obj M' ⟶ QB.obj M)
            (r : RF ⟶ RF') (l : LG' ⟶ LG),
            (∀ (s : WA.Under ⊤ K) (s' : WA.Under ⊤ K') (a : s.right ⟶ s'.right),
              QA.map s.hom ≫ left s' a = k →
                p.app s ≫ r = QB.map (Fh.map a) ≫ p'.app s') →
            (∀ (t : WB.Over ⊤ M) (t' : WB.Over ⊤ M') (a : t'.left ⟶ t.left),
              right t' a ≫ QB.map t.hom = m →
                l ≫ u.app t = u'.app t' ≫ QA.map (Gh.map a)) →
            ∀ h : QB.obj M ⟶ RF, e' (m ≫ h ≫ r) = l ≫ e h ≫ k := by
  classical
  intro HA HB WA WB QA QB Fh Gh ah R L left right splitR splitL canonical
    hR hL p u hp hu
  obtain ⟨φS, hS, hSrep⟩ :=
    derivedAdjunction_source_colimit WA WB QB Fh K M RF hR p hp
  obtain ⟨φT, hT, hTrep⟩ :=
    derivedAdjunction_target_colimit WA WB QA Fh Gh ah K M LG hL u hu
  let H := derivedAdjunctionHomDiagram WA WB Fh K M
  let eS := Equiv.ofBijective φS hS
  let eT := Equiv.ofBijective φT hT
  let e := eS.symm.trans eT
  have he (x : H.ColimitType) : e (φS x) = φT x := by
    exact congrArg φT (eS.symm_apply_apply x)
  have hcan : canonical K M RF LG p u e := by
    intro s t f
    change e (_ ≫ p.app s) = _
    rw [← hSrep s t f, he, hTrep]
  have hrep (h : QB.obj M ⟶ RF) :
      ∃ (s : WA.Under ⊤ K) (t : WB.Over ⊤ M) (f : t.left ⟶ Fh.obj s.right),
        h = right t f ≫ p.app s := by
    obtain ⟨x, rfl⟩ := hS.2 h
    obtain ⟨⟨s, t⟩, f, rfl⟩ := H.ιColimitType_jointly_surjective x
    exact ⟨s, t.unop, f, hSrep s t.unop f⟩
  refine ⟨e, ⟨hcan, ?_⟩, ?_⟩
  · intro K' M' RF' LG' p' u' e' hcan' k m r l hr hl h
    obtain ⟨s, t, f, rfl⟩ := hrep h
    have hsiso := Localization.inverts QA WA s.hom s.prop
    have htiso := Localization.inverts QB WB t.hom t.prop
    obtain ⟨α, hα⟩ := Localization.exists_leftFraction QA WA (inv (QA.map s.hom) ≫ k)
    obtain ⟨β, hβ⟩ := Localization.exists_rightFraction QB WB (m ≫ inv (QB.map t.hom))
    let s' : WA.Under ⊤ K' := MorphismProperty.Under.mk ⊤ α.s α.hs
    let t' : WB.Over ⊤ M' := MorphismProperty.Over.mk ⊤ β.s β.hs
    have hk : QA.map s.hom ≫ left s' α.f = k := by
      change QA.map s.hom ≫ α.map QA (Localization.inverts QA WA) = k
      rw [← hα, IsIso.hom_inv_id_assoc]
    have hm : right t' β.f ≫ QB.map t.hom = m := by
      change β.map QB (Localization.inverts QB WB) ≫ QB.map t.hom = m
      rw [← hβ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hr' := hr s s' α.f hk
    have hl' := hl t t' β.f hm
    have hsource : m ≫ (right t f ≫ p.app s) ≫ r =
        right t' (β.f ≫ f ≫ Fh.map α.f) ≫ p'.app s' := by
      rw [← hm]
      dsimp [right]
      simp only [MorphismProperty.RightFraction.map, Functor.map_comp, Category.assoc,
        IsIso.hom_inv_id_assoc]
      rw [← hr']
    rw [hsource]
    rw [hcan' s' t' (β.f ≫ f ≫ Fh.map α.f), hcan s t f]
    rw [← hk]
    simp only [Category.assoc]
    rw [← Category.assoc l (u.app t), hl']
    have htranspose : (ah.homEquiv t'.left s'.right).symm
        (β.f ≫ f ≫ Fh.map α.f) =
        Gh.map β.f ≫ (ah.homEquiv t.left s.right).symm f ≫ α.f := by
      dsimp [s', t', Fh, Gh]
      rw [← Category.assoc, ah.homEquiv_naturality_right_symm,
        ah.homEquiv_naturality_left_symm, Category.assoc]
    dsimp [left]
    rw [htranspose]
    simp only [MorphismProperty.LeftFraction.map, Functor.map_comp, Category.assoc]
    simp
  · intro e' he'
    apply Equiv.ext
    intro h
    obtain ⟨s, t, f, rfl⟩ := hrep h
    exact (he'.1 s t f).trans (hcan s t f).symm

end CategoryTheory
