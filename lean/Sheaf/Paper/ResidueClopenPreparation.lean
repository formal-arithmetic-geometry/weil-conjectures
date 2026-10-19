/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Cover.Open

import Sheaf.Paper.WeaklyContractibleClopenRefinement
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties

/-! # Finite clopen preparation of lisse residue cohomology

Source: Stacks Project, proetale.tex, Tag 09C3 (blueprint: lem-sf-residue-clopen-preparation).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Simultaneously trivialize the finite lisse residue cohomology on clopen pieces.
The completed pullbacks stay complete and retain finite residue Tor amplitude.

Source: Stacks Project, proetale.tex, Tag 09C3, finite disjoint covering step;
Tag 098F, splitting a pro-etale cover of a weakly contractible affine
(blueprint: lem-sf-residue-clopen-preparation).

Proof:
1. Bounded constructibility gives finitely many nonzero cohomology sheaves. Their
local constancy gives a common covering on which they are constant; finite stalks
make the constant modules finite-dimensional over the residue field.
2. Quasi-compactness of the affine scheme refines this covering by finitely many
covering affine opens. Their scheme coproduct is a weakly etale covering object.
Its representable maps epimorphically to the terminal representable. Weak
contractibility lifts the identity to a section of this map of representables.
3. Pull back the finitely many coproduct components along that section. Their
inverse images are pairwise disjoint clopen opens covering S. Each is affine,
since it is clopen in an affine. Pull back the constant residue trivializations.
A basis identifies each resulting cohomology sheaf with a finite power of the
residue coefficient sheaf, including rank zero in the vanishing degrees.
4. Sheaves on a disjoint clopen cover form the product of the sheaf categories
on its members. Extension by the terminal sheaf on the complement proves weak
contractibility on each member. Restriction is exact and preserves all limits,
quotient tensors and Roos triangles. It therefore preserves completeness and
finite Tor amplitude, and identifies the completed pullback of a complete object
with ordinary restriction, including its residue homology.
For the empty scheme take n=0. No integral projective model is asserted here. -/
theorem residue_clopen_preparation
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E S K)
    (hresidue : intrinsicFiniteTorsionConstructible l E 1 (by omega) S
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K))
    (hlisse : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheaf S
      (Padic.coefficientExtensionRing l E 1)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S
          (Padic.coefficientExtensionRing l E 1))) q).obj
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)))
    (hTor : HasFiniteProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)) :
    ∃ (n : ℕ) (U : Fin n → S.Opens),
      (⨆ i, U i) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        IsAffine (U i).toScheme ∧
        (Scheme.ProEt.topology (U i).toScheme).IsWeaklyContractible.{u + 1}
          (Scheme.ProEt.mk (𝟙 (U i).toScheme)) ∧
        IsDerivedCompleteUnrestricted.{u, u} l E (U i).toScheme
          ((integralDerivedPullback l E (U i).ι).obj K) ∧
        HasFiniteProEtaleTorAmplitude (U i).toScheme
          (Padic.coefficientExtensionRing l E 1)
          ((scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
            ((integralDerivedPullback l E (U i).ι).obj K)) ∧
        ∀ q : ℤ, ∃ N : ℕ, Nonempty
          (((DerivedCategory.homologyFunctor
            (proEtaleRingModules (U i).toScheme (proEtaleConstantRing (U i).toScheme
              (Padic.coefficientExtensionRing l E 1))) q).obj
            ((scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
              ((integralDerivedPullback l E (U i).ι).obj K))) ≅
            ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
              (integralCoefficientSheaf.{u, u} l E (U i).toScheme 0)) := by
  sorry

end WeilConjectures
