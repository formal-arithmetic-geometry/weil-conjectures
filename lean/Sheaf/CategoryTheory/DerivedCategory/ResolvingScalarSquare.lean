/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Sheaf.Paper.ReductionPullbackDerivedTower

/-! # Normalized squares of derived functors on resolving representatives

Source: Stacks Project, Tags 06XN, 06YY and 0D6D.
(blueprint: lem-trf-resolving-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b c d va vb vc vd wa wb wc wd
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wa} A]
  {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{wb} B]
  {C : Type c} [Category.{vc} C] [Abelian C] [HasDerivedCategory.{wc} C]
  {D : Type d} [Category.{vd} D] [Abelian D] [HasDerivedCategory.{wd} D]
  (F : A ⥤ B) (G : C ⥤ D) (S : A ⥤ C) (T : B ⥤ D)
  [F.Additive] [G.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (LS : DerivedCategory A ⥤ DerivedCategory C)
  (LT : DerivedCategory B ⥤ DerivedCategory D)
  (εS : DerivedCategory.Q ⋙ LS ⟶ S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εT : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (e : F ⋙ T ≅ S ⋙ G)

/-- A derived square is fixed by its two universal comparisons on any resolving class.
The computation formula holds on every cochain representative.
Source: Stacks 06XN, 06YY and 0D6D (blueprint: lem-trf-resolving-scalar-square).

Proof: restrict both sides of the square to good complexes. The two counits, exact
functor localization factors, and the ordinary square give two natural isomorphisms
with common target. Their quotient descends uniquely because restriction to resolving
representatives is fully faithful. For an additional representative, resolve it by a
good complex and use naturality of the counits and the ordinary square. Cancel the
image of the resolution quasi-isomorphism to obtain its formula. Uniqueness follows
already on the good resolving class. -/
theorem resolvingScalarSquare
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ P, ∃ (Q : CochainComplex A ℤ) (s : Q ⟶ P), good Q ∧ QuasiIso s)
    (hS : ∀ P, good P → IsIso (εS.app P))
    (hT : ∀ P, good P → IsIso (εT.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    ∃! τ : F.mapDerivedCategory ⋙ LT ≅ LS ⋙ G.mapDerivedCategory,
      ∀ P,
        LT.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          εT.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
        τ.hom.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (εS.app P) ≫
          G.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) := by
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let l := P.ι ⋙ DerivedCategory.Q
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let Tc := T.mapHomologicalComplex (.up ℤ)
  let ord := NatIso.mapHomologicalComplex e (.up ℤ)
  let α : l ⋙ (F.mapDerivedCategory ⋙ LT) ⟶ P.ι ⋙ Sc ⋙
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft P.ι
      (Functor.whiskerRight F.mapDerivedCategoryFactors.hom LT ≫
        Functor.whiskerLeft Fc εT ≫ Functor.whiskerRight ord.hom DerivedCategory.Q)
  let β : l ⋙ (LS ⋙ G.mapDerivedCategory) ⟶ P.ι ⋙ Sc ⋙
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (Functor.whiskerLeft P.ι εS) G.mapDerivedCategory ≫
      Functor.whiskerLeft (P.ι ⋙ Sc) G.mapDerivedCategoryFactors.hom
  have ha (X : P.FullSubcategory) : IsIso (α.app X) := by
    have := hT X.obj X.property
    dsimp [α]
    infer_instance
  have hb (X : P.FullSubcategory) : IsIso (β.app X) := by
    have := hS X.obj X.property
    dsimp [β]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let ff := cochainRepresentativeWhiskering good res (DerivedCategory D)
  let τ := ff.preimageIso (asIso α ≪≫ (asIso β).symm)
  have he : Functor.whiskerLeft l τ.hom ≫ β = α := by
    rw [show Functor.whiskerLeft l τ.hom =
      (asIso α ≪≫ (asIso β).symm).hom from ff.map_preimage _]
    simp
  refine ⟨τ, ?_, ?_⟩
  · let lhs : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT) ⟶
        Sc ⋙ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerRight F.mapDerivedCategoryFactors.hom LT ≫
        Functor.whiskerLeft Fc εT ≫ Functor.whiskerRight ord.hom DerivedCategory.Q
    let rhs : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT) ⟶
        Sc ⋙ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerLeft DerivedCategory.Q τ.hom ≫
        Functor.whiskerRight εS G.mapDerivedCategory ≫
          Functor.whiskerLeft Sc G.mapDerivedCategoryFactors.hom
    intro X
    obtain ⟨W, s, hW, hs⟩ := res X
    have : QuasiIso s := hs
    have hg : lhs.app W = rhs.app W :=
      (NatTrans.congr_app he ⟨W, hW⟩).symm
    have : IsIso ((DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT)).map s) := by
      dsimp
      infer_instance
    apply (cancel_epi ((DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT)).map s)).1
    change _ ≫ lhs.app X = _ ≫ rhs.app X
    rw [lhs.naturality, rhs.naturality, hg]
  · intro σ hσ
    apply Iso.ext
    apply ff.map_injective
    apply (cancel_mono β).1
    ext X
    exact (hσ X.obj).symm.trans (NatTrans.congr_app he X).symm

end CategoryTheory
