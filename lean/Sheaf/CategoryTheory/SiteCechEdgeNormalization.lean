/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-!
# Augmentation normalization for a chosen site Čech complex

Source: Stacks Project, Cohomology on Sites, Tag 03AX, the maps alpha and beta
(blueprint: def-weil-pbc-site-cech-edge-normalization).

The coefficient category may be abelian sheaves or sheaves of modules. The
presheaf-valued functor forgets to underlying abelian sections. All data below
are constructed from this functor and the already chosen tuple products.
-/

@[expose] public section

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [SmallCategory C] {T : Type u} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
  {E : Type a} [Category.{b} E] [Abelian E] [EnoughInjectives E]
  (P : E ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive]

/-- The Čech-first double complex obtained by applying the existing Čech functor
termwise. Source: Stacks 03AX
(blueprint: def-weil-pbc-site-cech-edge-normalization). -/
noncomputable def resolutionDoubleComplex {A : E} (I : InjectiveResolution A) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip
    (((P ⋙ S.complexFunctor).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)

/-- The two augmentations specified by their actual degreewise formulas. Their
source and target use the existing complex and total-complex constructions.
Source: Stacks 03AX (blueprint: def-weil-pbc-site-cech-edge-normalization). -/
structure Augmentations {A : E} (I : InjectiveResolution A) where
  alpha : ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex ⟶
      (S.resolutionDoubleComplex P I).total (ComplexShape.up ℕ)
  beta : S.complex (P.obj A) ⟶
    (S.resolutionDoubleComplex P I).total (ComplexShape.up ℕ)
  alpha_f : ∀ n : ℕ, alpha.f n =
    AddCommGrpCat.ofHom (AddMonoidHom.pi fun t : Fin (0 + 1) → T ↦
      ((P.obj (I.cocomplex.X n)).map (S.pr 0 t 0 ≫ hom (t 0)).op).hom) ≫
      (S.resolutionDoubleComplex P I).ιTotal (ComplexShape.up ℕ) 0 n n (Nat.zero_add n)
  beta_f : ∀ n : ℕ, beta.f n =
    S.cochainsMap (P.map (I.ι.f 0)) n ≫
      (S.resolutionDoubleComplex P I).ιTotal (ComplexShape.up ℕ) n 0 n (Nat.add_zero n)

/-- An edge is normalized when every injective resolution computes it by beta
followed by the inverse of alpha. The equation avoids choosing an inverse, and
also asserts that the specified alpha is a quasi-isomorphism. Existence of the
augmentations is part of the predicate; it is not an assumption on the user.
Source: Stacks 03AX (blueprint: def-weil-pbc-site-cech-edge-normalization). -/
def IsNormalizedEdge {A : E} (q : ℕ)
    (e : (S.cohomologyFunctor q).obj (P.obj A) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A) : Prop :=
  ∀ I : InjectiveResolution A, ∃ d : S.Augmentations P I,
    QuasiIso d.alpha ∧
      e ≫ (I.isoRightDerivedObj
        (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
          HomologicalComplex.homologyMap d.alpha q =
            HomologicalComplex.homologyMap d.beta q

end CategoryTheory.SiteCechComplex
