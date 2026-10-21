/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
import Sheaf.Paper.ConstructibleExtContinuity
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Uniform vanishing on ind-constructible targets

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ind-heart-ii/
sk-cor-ind-heart-ii-vanishing.md and its proof
(blueprint: det-ind-heart-ii-vanishing).

Integer Ext is the ambient derived Hom from a degree-zero sheaf to a shifted
degree-zero sheaf. Ind-constructibility uses Mathlib's filtered-colimit property
in the module category, rather than an abstract ind-category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Every filtered constructible presentation gives the canonical Ext comparison
isomorphism in every integer degree. A fixed nonnegative uniform bound on
constructible targets also bounds all ind-constructible targets.

Source: blueprint main-20261015, sk-cor-ind-heart-ii-vanishing, with the explicit
Noetherian and uniform-bound hypotheses of the reviewed DAG statement
(blueprint: det-ind-heart-ii-vanishing).

Proof:
1. Regard the constructible diagram as degree-zero complexes. They all vanish
below zero; their termwise colimit is the degree-zero embedding of the module
colimit with exactly the given cocone. No derived-category colimit is asserted.
2. Apply sk-lem-constructible-ext-continuity, specifically its field-coefficient
constructible-sheaf clause, using Noetherianity and the common lower bound zero.
It identifies the displayed comparison with the one induced by the same cocone,
for every integer q and every chosen constructible presentation.
3. Above d, the assumed uniform bound makes every stage Ext group zero.
Its filtered colimit as an abelian group is zero, hence so is the target Ext
group by Step 2. Every object satisfying ObjectProperty.ind has a small filtered
constructible presentation, giving the second conjunct. The existence of d is
not asserted here; the supplied bound is the property intended in
sk-lem-uniform-constructible-ext. -/
theorem indHeartII_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (_hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : ConstantModelConstructible (coefficientHeartRingObj R) X)
    (d : ℤ) (_hd : 0 ≤ d)
    (_hbound : ∀ N : ConstantModelConstructible (coefficientHeartRingObj R) X,
      ∀ r : ℤ, d < r →
        Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦r⟧)) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X)),
      (∀ i : I, IsConstantModelConstructible (coefficientHeartRingObj R) X (D.obj i)) →
      ∀ (c : Cocone D), IsColimit c → ∀ q : ℤ,
        IsIso (colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone c))) ∧
    (∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X),
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (coefficientHeartRingObj R) X) B →
      ∀ q : ℤ, d < q →
        Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
          ((DerivedCategory.singleFunctor _ 0).obj B)⟦q⟧)) := by
  classical
  constructor
  · intro I _ _ D _ c hc q
    exact constructible_sheaf_ext_continuity ℓ E R _hR X C.obj C.property D c hc q
  · intro B hB q hq
    obtain ⟨I, _, _, pres, hpres⟩ := hB
    let F := DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
      preadditiveCoyoneda.obj
        (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))
    have hstage : ∀ i : I, IsZero ((pres.diag ⋙ F).obj i) := by
      intro i
      exact AddCommGrpCat.isZero_iff_subsingleton.mpr
        (_hbound ⟨pres.diag.obj i, hpres i⟩ q hq)
    have hzero : IsZero (colimit (pres.diag ⋙ F)) :=
      (colimit.isColimit _).isZero_pt (Functor.isZero _ hstage)
    have : IsIso (colimit.desc _ (F.mapCocone pres.cocone)) :=
      constructible_sheaf_ext_continuity ℓ E R _hR X C.obj C.property
        pres.diag pres.cocone pres.isColimit q
    exact AddCommGrpCat.subsingleton_of_isZero
      (hzero.of_iso (asIso (colimit.desc _ (F.mapCocone pres.cocone))).symm)

end AlgebraicGeometry.ProEtale
