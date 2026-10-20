/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModels
public import Sheaf.Paper.KoszulReconstruction
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses

import Sheaf.Paper.CompatibleFiniteDerivedTrivializations
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.RingTheory.RlimPerfectComplete
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # Effectivity of uniformly perfect finite quotient systems

Source: Stacks Project, proetale.tex, Tag 09C6; More on Algebra, Tag 09AW
(blueprint: lem-weil-pbc-finite-perfect-adic-realization).

The input consists of finite-level models. The output identifies the derived limit of
the specified quotient tower, without assuming that its original object is complete.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A normalized quotient system with uniformly bounded etale local perfect constant
models has a pro-etale local perfect completed realization.

Source: Stacks Project, proetale.tex, lemma-connected-adic-lisse (Tag 09C6), specifically
its algebraic tower and compatible-isomorphism argument; More on Algebra, Tag 09AW;
Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-realization).

Proof:
Refine the input etale cover by connected components of Noetherian affine opens.
Finite-ring derived comparison descends each finite quotient to a bounded etale
complex. Their locally constant cohomology and uniform Tor bounds follow from their
given perfect local models. Full faithfulness lifts the datum's normalized reduction
maps uniquely, retaining all quotient cocycles. Fix a geometric point on each nonempty
connected neighborhood and take the exact stalk of this entire normalized system.
This gives a tower E_n over A/I^(n+1), whose first term is perfect and whose reduction
maps are isomorphisms. Its transitions are the adjoints of those same isomorphisms,
not independent choices of maps. Algebraic perfect inverse-limit reconstruction gives
a bounded finite-projective A-complex P and compatible isomorphisms of its reductions
with E_n. Finite-ring derived local constancy identifies each etale level locally with
its stalk model E_n. The finite locally constant sheaves Isom(constant E_n, L_n) have
nonempty stalks. Compatible finite derived trivialization therefore supplies one
pro-etale cover with compatible trivializations at all levels.
For a finite-projective term of P choose an idempotent on a finite free module. Its
finite quotient sheaves have sectionwise surjective transitions. Recursive lifting
makes 1-shift on their product sectionwise surjective. Its kernel is the same
idempotent summand of the completed coefficient ring. The Roos triangle therefore
identifies the derived limit of this bounded quotient complex with completed scalar
extension of the constant P. Exact slice restriction preserves products, hence the
Roos triangle; it thus carries the original strict quotient tower's derived limit to
this same local limit. Applying the compatible trivializations gives the displayed
isomorphism. Assemble the refinements of the original cover; empty members use empty
covers. No completeness hypothesis on the original M is used in this argument. -/
theorem finitePerfectModels_adic_realization
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A]
    [(koszulConstantFunctor X A).PreservesZeroMorphisms]
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((reconstructionRlim X d).obj ((completedAdicReduction X d).obj M)) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X A P)))) := by
  sorry

end AlgebraicGeometry.Scheme
