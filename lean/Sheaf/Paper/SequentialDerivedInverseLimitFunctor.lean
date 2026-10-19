/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Paper.SequentialDerivedInverseLimit
public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.CategoryTheory.Triangulated.DerivedLimitTower

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
/-! # Functorial sequential derived inverse limits

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
prop-weil-pbc-rlim-functoriality, order 1242; Stacks Tags 08TC, 079P and 0BK7
(blueprint: prop-weil-pbc-rlim-functoriality).

The natural factorization isomorphism specifies the assignment on complexes and chain
maps. Thus morphisms are induced by the chosen functorial resolution of strict towers;
no arbitrary maps between Roos cones are chosen. All complexes are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Fix any functorial K-injective resolution of strict towers. Termwise ordinary inverse
limit followed by localization descends to a triangulated functor. Every other functorial
resolution gives an isomorphic functor, naturally on the entire derived tower category.

Source: blueprint order 1242; Stacks Tags 08TC, 079P and 0BK7
(blueprint: prop-weil-pbc-rlim-functoriality).

Proof plan:
1. Ordinary inverse limit is additive: compatible families in a biproduct are pairs of
   compatible families, and addition of maps is componentwise. It therefore preserves
   homotopies of strict towers, which are compatible with every transition map.
2. For a derived morphism QM → QN, conjugate by the localized resolution augmentations.
   The Hom bijection into a K-injective target (lem-weil-pbc-kinjective-hom-derived)
   gives its unique lift between the resolutions in the homotopy category. Apply inverse
   limit and localization. Uniqueness proves identities, composition and the natural
   factorization on chain maps. In particular quasi-isomorphisms are inverted.
3. This is the unbounded right derived functor of ordinary inverse limit. Apply
   lem-pc-right-derived-functor-triangulated, transporting shift commutation along the
   comparison with its generic K-injective construction. Distinguished triangles are
   preserved because they are isomorphic, including their last arrow, to those images.
   Target resolutions exist by prop-pur-kinjective-resolutions-exist on the small skeleton.
4. For a second resolution J, lift Q(η_J) Q(η_I)⁻¹ uniquely into J in the homotopy
   category. The opposite lift is its inverse. The same Hom bijection proves naturality
   for all derived morphisms. Inverse limit preserves these homotopy equivalences,
   giving a natural isomorphism between the descended functors.
5. prop-weil-pbc-derived-inverse-limit-computation identifies each value with the
   sequential derived limit of def-weil-pbc-derived-inverse-limit. The Roos property
   def-weil-derived-limit is used for this identification, never to choose morphisms. -/
theorem sequentialDerivedInverseLimit_functorial
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [EnoughInjectives (Scheme.CompletedAdicTowers T d)]
    (I : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ ⥤
      CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
    (η : 𝟭 (CochainComplex (Scheme.CompletedAdicTowers T d) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    ∃ (RF : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d))
      (_ε : DerivedCategory.Q ⋙ RF ≅
        I ⋙ (lim : Scheme.CompletedAdicTowers T d ⥤
      Scheme.CompletedAdicModules T d).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q),
      (∃ (_ : RF.CommShift ℤ), RF.IsTriangulated) ∧
      (∀ M : DerivedCategory (Scheme.CompletedAdicTowers T d),
        IsAdicSequentialDerivedLimit T d M (RF.obj M)) ∧
      ∀ (J : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ ⥤
      CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
        (ν : 𝟭 (CochainComplex (Scheme.CompletedAdicTowers T d) ℤ) ⟶ J),
        (∀ M : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ,
          QuasiIso (ν.app M) ∧ (J.obj M).IsKInjective) →
        ∀ (RF' : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d)),
          Nonempty (DerivedCategory.Q ⋙ RF' ≅
            J ⋙ (lim : Scheme.CompletedAdicTowers T d ⥤
      Scheme.CompletedAdicModules T d).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) → Nonempty (RF ≅ RF') := by
  sorry

end AlgebraicGeometry.ProEtale
