/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernNativeEncoding
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier

/-! # An explicit ordinary normalization for the native projective Chern arrow

The class used here is the native strict-system Cartier class, transported by the exact
coefficient equivalence before forgetting its Weil structure.
All data are parameters or actual constructions; no class is selected from mere existence.
Source: current blueprint, diagonal-tower-trace (1) and rank-one Thom Step 1.
(blueprint: def-pur-v5-projective-chern-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- Infinity is a relative effective Cartier divisor, including over the empty base.
Source: projective-line standard charts; alternatively the smooth relative-curve criterion.
(blueprint: def-pur-v5-projective-chern-normalization).
Proof: infinity is a closed section of the smooth relative curve P1/X. Its closed image
is isomorphic to X, hence flat and finite over X. The relative Cartier criterion applies. -/
theorem projectiveChernInfinityCartier :
    (ProjectiveLine.infinity X).ker.IsInvertible := by
  have hc : IsClosedImmersion
      (ProjectiveLine.infinity X ≫ ProjectiveLine X ↘ X) := by
    rw [ProjectiveLine.infinity_over]
    infer_instance
  have : IsClosedImmersion (ProjectiveLine.infinity X) :=
    .of_comp _ (ProjectiveLine X ↘ X)
  have h : (ProjectiveLine.infinity X).ker.subschemeι ≫ ProjectiveLine X ↘ X =
      inv (ProjectiveLine.infinity X).toImage := by
    apply (cancel_epi (ProjectiveLine.infinity X).toImage).mp
    simp [← Category.assoc, Scheme.Hom.image]
  have : IsIso ((ProjectiveLine.infinity X).ker.subschemeι ≫ ProjectiveLine X ↘ X) := by
    rw [h]
    infer_instance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat
    (ProjectiveLine X ↘ X) inferInstance inferInstance inferInstance

/-- The projective line as a base for the given Cartier construction.
Source: properness of the projective line
(blueprint: def-pur-v5-projective-chern-normalization). -/
def projectiveChernBase : ProEtale.NativeCartier.Base k₀ where
  scheme := ProjectiveLine X
  qc := by
    change QuasiCompact ((ProjectiveLine X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀)))
    infer_instance
  qs := by
    change QuasiSeparated ((ProjectiveLine X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀)))
    infer_instance
  lft := by
    change LocallyOfFiniteType ((ProjectiveLine X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀)))
    infer_instance

/-- Ordinary module coefficients on the geometric projective line.
Source: native coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev ProjectiveChernModules :=
  ProEtale.NativeCartier.Modules l
    (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)).geometricFiber

/-- The actual native coefficient unit transported by the specified inverse encoding.
Source: exact native coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernNativeUnit :=
  (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) (ProjectiveLine X)).inverse.obj
    (ProEtale.NativeCartier.unit k₀ l (ProjectiveLine X))

/-- The actual native positive Tate line transported by the specified inverse encoding.
Source: exact native coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernNativeTate :=
  (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) (ProjectiveLine X)).inverse.obj
    (ProEtale.NativeCartier.tate k₀ l (ProjectiveLine X))

/-- The ordinary continuous-coefficient encoding before derivation.
Source: native coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernSheafEncoding : ProEtaleWeilSheaf k₀ l (ProjectiveLine X) ⥤
    ProjectiveChernModules (k₀ := k₀) (l := l) X :=
  Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (ProjectiveLine X)) ⋙
    ProEtale.NativeEncoding.encoding l
      (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)).geometricFiber

/-- The encoded native coefficient unit in degree zero.
Source: native Cartier realization and exact coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernUnit : DerivedCategory (ProjectiveChernModules (k₀ := k₀) (l := l) X) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((projectiveChernSheafEncoding (k₀ := k₀) (l := l) X).obj
      (projectiveChernNativeUnit (k₀ := k₀) (l := l) X))

/-- The encoded native positive Tate line in degree zero.
Source: native Cartier realization and exact coefficient encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernTate : DerivedCategory (ProjectiveChernModules (k₀ := k₀) (l := l) X) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((projectiveChernSheafEncoding (k₀ := k₀) (l := l) X).obj
      (projectiveChernNativeTate (k₀ := k₀) (l := l) X))

/-- The positive infinity class as an actual arrow in the ambient native derived category.
No invariant ordinary arrow is lifted, and no arbitrary existence witness is selected.
Source: exact descent of the Cartier extension, then the specified inverse encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
def projectiveChernNativePositiveClass (C : ProEtale.NativeCartier.Construction k₀ l) :
    (DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)) 0).obj
        (projectiveChernNativeUnit (k₀ := k₀) (l := l) X) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (projectiveChernNativeTate (k₀ := k₀) (l := l) X))⟦(2 : ℤ)⟧ :=
  ProEtale.SpTowerClasses.mapSingleArrow
    (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) (ProjectiveLine X)).inverse 2
    (ProEtale.NativeCartier.nativeClass k₀ l (ProjectiveLine X)
      (C.route (projectiveChernBase (k₀ := k₀) X) (ProjectiveLine.infinity X).ker
        (projectiveChernInfinityCartier X)))

/-- Forget and encode the actual native positive infinity class.
Source: exact functorial realization of the native Cartier class
(blueprint: def-pur-v5-projective-chern-normalization). -/
def projectiveChernPositiveClass (C : ProEtale.NativeCartier.Construction k₀ l) :
    projectiveChernUnit (k₀ := k₀) (l := l) X ⟶
      (projectiveChernTate (k₀ := k₀) (l := l) X)⟦(2 : ℤ)⟧ :=
  ProEtale.SpTowerClasses.mapSingleArrow
    (projectiveChernSheafEncoding (k₀ := k₀) (l := l) X) 2
    (projectiveChernNativePositiveClass X C)

/-- Forget Frobenius and use the specified continuous-coefficient encoding.
Source: native adic encoding
(blueprint: def-pur-v5-projective-chern-normalization). -/
abbrev projectiveChernEncoding : WeilComplex k₀ l (ProjectiveLine X) ⥤
    DerivedCategory (ProjectiveChernModules (k₀ := k₀) (l := l) X) :=
  forget ⋙ ProEtale.NativeEncoding.derivedEncoding l
    (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)).geometricFiber

/-- A single native arrow is the tensor action of the actual positive Cartier class.
The two endpoint isomorphisms allow different unit and Tate presentations. They do not
postulate an inverse to the Chern arrow or any assertion about its cohomology.
Source: top-class argument, tensoring the Cartier extension
(blueprint: def-pur-v5-projective-chern-normalization). -/
def ProjectiveChernNormalized (C : ProEtale.NativeCartier.Construction k₀ l)
    (M : WeilSheaf k₀ l X)
    (a : (upperStar (ProjectiveLine X ↘ X)).obj
        ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          (WeilSheaf.toComplex.obj M)) ⟶
      (upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)) : Prop :=
  let E := projectiveChernEncoding (k₀ := k₀) (l := l) X
  let N := E.obj ((upperStar (ProjectiveLine X ↘ X)).obj
    ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj (WeilSheaf.toComplex.obj M)))
  ∃ s : N ≅ N ⊗ projectiveChernUnit (k₀ := k₀) (l := l) X,
    ∃ t : N ⊗ (projectiveChernTate (k₀ := k₀) (l := l) X)⟦(2 : ℤ)⟧ ≅
        E.obj ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)),
      E.map a = s.hom ≫ (𝟙 N ⊗ₘ projectiveChernPositiveClass X C) ≫ t.hom

end AlgebraicGeometry.WeilComplex
