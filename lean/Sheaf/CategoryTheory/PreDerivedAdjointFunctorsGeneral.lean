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
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import Sheaf.CategoryTheory.LocalizationHomColimit
import Sheaf.CategoryTheory.RightLocalizationHomColimit

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

Proof: (1) use lem-pc-essentially-constant-ind-hom-colimit to express Hom(M,RF(K))
as the colimit over quasi-isomorphisms s:K->I. (2) Use
lem-pc-right-localization-hom-colimit to express each Hom(M,F(I)) as the colimit
of Hom(P,F(I)) over t:P->M. The fraction calculus applies by
lem-pc-quasi-isomorphisms-multiplicative-system. (3) Interchange the independent
colimits using lem-pc-colimit-fubini. (4) Apply the underived adjunction, induced
on homotopy categories, to replace Hom(P,F(I)) by Hom(G(P),I). (5) Use
lem-pc-left-localization-hom-colimit to identify the inner colimit with
Hom(G(P),K). (6) Use lem-pc-essentially-constant-pro-hom-colimit to identify the
outer colimit with Hom(LG(M),K). The resulting bijection has the displayed formula
on representatives; these representatives exhaust Hom(M,RF(K)), proving uniqueness.
For naturality, refine representatives using the left and right fraction calculi,
apply naturality of the underived adjunction, and use the two compatibility equations
for the induced maps on representing values. This works for all localized morphisms,
so in particular on the triangulated subcategories where the partial functors exist.

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
  sorry

end CategoryTheory
