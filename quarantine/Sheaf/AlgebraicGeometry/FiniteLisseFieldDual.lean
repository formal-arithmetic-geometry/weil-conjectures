/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom

import WeilConjectures.ConstructibleSheaf.Monoidal

import Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology
import Sheaf.AlgebraicGeometry.FiniteLisseFieldSitePerfect

/-!
# Duals of bounded finite locally constant complexes over a prime field

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lem-fin-lisse-field-dual).

The existing etale `derivedHom` is the K-injective derived internal Hom in the
`ModuleCat` encoding. Its construction derives the homotopy-category Hom functor
using K-injectives in `DerivedCategory.tensorHomAdjunctionQhObj`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

/-- The internal-Hom comparison followed by an isomorphism in the second variable.
It is the transpose of pulled-back evaluation, as recorded by the identity below.
Source: blueprint lem-fin-lisse-field-dual, proof step 5
(blueprint: lem-fin-lisse-field-dual). -/
noncomputable def derivedHomPullbackAlongIsoComparison
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T'.smallEtaleTopology A))
    (e : (L(upperStar A v)).obj M ≅ N) :
    (L(upperStar A v)).obj (((derivedHom A T).obj (op C)).obj M) ⟶
      ((derivedHom A T').obj (op ((L(upperStar A v)).obj C))).obj N :=
  derivedHomUpperStarComparison A v C M ≫
    ((derivedHom A T').obj (op ((L(upperStar A v)).obj C))).map e.hom

private theorem derivedHomPullbackAlongIsoComparison_eq_transpose
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T'.smallEtaleTopology A))
    (e : (L(upperStar A v)).obj M ≅ N) :
    (derivedTensorHomAdjunction A ((L(upperStar A v)).obj C)).homEquiv _ _
      ((leftDerivedUpperStarTensorIso A v C
        (((derivedHom A T).obj (op C)).obj M)).inv ≫
      (L(upperStar A v)).map ((derivedTensorHomAdjunction A C).counit.app M) ≫
      e.hom) = derivedHomPullbackAlongIsoComparison v C M N e := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  unfold derivedHomPullbackAlongIsoComparison
  congr 1
  let := leftDerivedUpperStarMonoidal A v
  rw [derivedHomUpperStarComparison,
    Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  congr 2
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  exact (leftDerivedUpperStarTensorIso A v C
    (((derivedHom A T).obj (op C)).obj M)).hom_inv_id

private theorem dualPullback_isIso_of_exactPairing
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T'.smallEtaleTopology A))
    (e : (L(upperStar A v)).obj M ≅ N)
    (hC : DerivedCategory.IsDualizableEtale C) :
    IsIso (derivedHomPullbackAlongIsoComparison v C M N e) := by
  obtain ⟨_⟩ := hC
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap C Cᘁ
  have := isIso_derivedHomUpperStarComparison_of_exactPairing A v Cᘁ C M
  unfold derivedHomPullbackAlongIsoComparison
  infer_instance

end General

/-- The canonical map from the pullback of the coefficient dual to the dual of the
pullback: transpose the pulled-back evaluation using the strong monoidal pullback
and its unit comparison. Source: blueprint lem-fin-lisse-field-dual, proof step 5;
Stacks, Sites Cohomology, Section 08J7 (blueprint: lem-fin-lisse-field-dual). -/
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj (constantComplex Λ T)) ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) T').obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C))).obj (constantComplex Λ T') :=
  derivedHomPullbackAlongIsoComparison v C (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v)


private theorem finiteLisseDualPullbackComparison_isIso
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) (hC : DerivedCategory.IsDualizableEtale C) :
    IsIso (finiteLisseDualPullbackComparison v C) := by
  exact dualPullback_isIso_of_exactPairing (A := ModuleCat.{u + 1} Λ) v C
    (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v) hC

/-- Duality for an ordinary bounded etale complex over the prime field: finite local
constancy of cohomology is preserved, cohomology is the degree-reversed sheaf dual,
and the canonical comparison commutes with every scheme pullback.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lem-fin-lisse-field-dual).

Proof: the finite-ring local-constancy theorem gives bounded complexes of finite
constant modules on an etale cover. Choosing bases over the coefficient field
makes them site-perfect. The site-perfect homology-dual calculation gives the
cohomology formula, and finite local constancy follows from the existing ordinary
sheaf-dual theorem. Site-perfectness also implies dualizability. A strong monoidal
functor preserves internal Hom out of a dualizable object; composing its comparison
with the unit comparison gives exactly the displayed pullback map, by naturality
of the tensor-Hom adjunction. -/
theorem finiteLisseFieldDual
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (_hℓ : IsUnit (ℓ : Γ(T, ⊤)))
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
    (_hlisse : ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) :
    (∀ q : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((derivedHom
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)))) ∧
    (∀ q : ℤ, Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((derivedHom
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
              (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj
          (𝟙_ (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))))) ∧
    (∀ (T' : Scheme.{u}) (v : T' ⟶ T),
      IsIso (finiteLisseDualPullbackComparison v C)) := by
  have hp := finiteLisseField_sitePerfect ℓ T C _hbounded _hlisse
  have h₂ := sitePerfect_fieldDual_homology ℓ T C hp
  refine ⟨?_, h₂, ?_⟩
  · intro q
    obtain ⟨e⟩ := h₂ q
    have hdual := (_hlisse (-q)).ihom_unit
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso e.symm
  · intro T' v
    exact finiteLisseDualPullbackComparison_isIso v C hp.isDualizable

end AlgebraicGeometry.Etale
