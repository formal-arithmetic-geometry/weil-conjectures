/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # Prime-to-ell acyclicity of trivial continuous condensed scalars

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar analytic input
(blueprint: lem-sfb-prime-to-ell-condensed-acyclicity).
The exact ordinary condensed reference, including noncomplete Omega, remains WANTED.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CondensedBar

namespace Profinite.CondensedAction

/-- Bundle the recorded all-continuous scalar sheaf with its recorded ring structure.
Source: blueprint paragraph (3), scalar analytic input
(blueprint: lem-sfb-prime-to-ell-condensed-acyclicity). -/
def scalarRing (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] :
    CategoryTheory.CondensedBar.Ring.{u} :=
  { X := Profinite.continuousMapRingObjOfUniverse.{u, u} F
    mon := Profinite.continuousMapRingObjOfUniverseMonObj F
    comm := Profinite.isCommMonObj_continuousMapRingObjOfUniverse F }

variable {A : CategoryTheory.CondensedBar.Ring.{u}} {K : Type u}
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [ActionAbelian A K] [IsGrothendieckAbelian.{u + 1} (CategoryTheory.CondensedBar.Equivariant A K)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant A K)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules A)]

/-- The canonical augmentation for a trivial module, computed on any injective resolution.
The adjunction unit is the identity into invariant sections, by the recorded transpose law.
Apply invariants to the resolution inclusion, extend by zero, localize, and use the inverse
of the recorded ordinary right-derived resolution comparison. Thus its target is the
ordinary total right derived invariants, rather than an independently chosen bar model.
Source: blueprint paragraph (3), scalar analytic input
(blueprint: lem-sfb-prime-to-ell-condensed-acyclicity). -/
def trivialDerivedAugmentation (V : CategoryTheory.CondensedBar.Invariants A K)
    (M : CategoryTheory.CondensedBar.Modules A)
    (I : InjectiveResolution ((trivial (R := A.toMon) (P := K)).obj M)) :
    DerivedCategory.Q.{u + 2}.obj (CategoryTheory.CondensedBar.extend
      ((CochainComplex.single₀ (CategoryTheory.CondensedBar.Modules A)).obj M)) ⟶
    V.functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.obj
      ((DerivedCategory.singleFunctor.{u + 2} (CategoryTheory.CondensedBar.Equivariant A K) 0).obj
        ((trivial (R := A.toMon) (P := K)).obj M)) :=
  DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
    ((CochainComplex.single₀ (CategoryTheory.CondensedBar.Modules A)).map
        (V.adjunction.unit.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex V.functor (.up ℕ) 0).inv.app
        ((trivial (R := A.toMon) (P := K)).obj M) ≫
      (V.functor.mapHomologicalComplex (.up ℕ)).map I.ι)
    ComplexShape.embeddingUpNat) ≫ (resolutionComparison V I).inv

/-- Scalar acyclicity includes existence of the ordinary action-category structures and
normalized invariants. Standard unbounded localizations are used in the next universe.
For every injective resolution the specified augmentation is an isomorphism in that
ordinary derived category. No completeness or locally constant condition is present.
Source: blueprint paragraph (3), scalar analytic input
(blueprint: lem-sfb-prime-to-ell-condensed-acyclicity). -/
def ScalarAcyclic (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] : Prop := by
  refine ∃ h : ActionAbelian (scalarRing F) K, ?_
  letI : ActionAbelian (scalarRing F) K := h
  refine ∃ g : IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (scalarRing F) K), ?_
  letI : IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (scalarRing F) K) := g
  letI : HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant (scalarRing F) K) :=
    HasDerivedCategory.standard (CategoryTheory.CondensedBar.Equivariant (scalarRing F) K)
  letI : HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (scalarRing F)) :=
    HasDerivedCategory.standard (CategoryTheory.CondensedBar.Modules (scalarRing F))
  exact ∃ V : CategoryTheory.CondensedBar.Invariants (scalarRing F) K,
    ∀ I : InjectiveResolution
      ((trivial (R := (scalarRing F).toMon) (P := K)).obj
        (Mod.regular (scalarRing F).X)),
      IsIso (trivialDerivedAugmentation V (Mod.regular (scalarRing F).X) I)

/-- Trivial scalar condensed coefficients are acyclic for pro-prime-to-ell groups,
for both the finite intermediate field and the noncomplete normed algebraic closure.
Source: blueprint direct-images proof, paragraph (3), agent-formulated scalar analytic input
(blueprint: lem-sfb-prime-to-ell-condensed-acyclicity).

Proof:
1. Apply lem-sfb-condensed-derived-invariant-bar to the trivial regular module. Ordinary
   derived invariants are its derived internal-Hom bar total; the augmentation is the
   invariant inclusion in degree zero.
2. Apply lem-sfb-normed-scalar-profinite-hom-acyclic to every profinite power K^n.
   Naturality identifies the bar faces with continuous precomposition, including the first
   face since the action is trivial. The resolution column augmentations are chain maps,
   are quasi-isomorphisms, and compose with the next resolution differential to zero.
   Apply lem-sc-first-quadrant-column-augmentation to obtain the all-continuous cochains.
3. Apply lem-sfb-prime-to-ell-cochain-finite-quotient-descent. Its specified inclusion from
   finite-quotient cochains is a quasi-isomorphism and is the identity in degree zero.
   This retains all continuous Omega-valued functions and uses no completion.
4. Locally a finite-quotient n-cocycle factors through Q=K/U. For n>=1 put
   b(s;g1,...,g(n-1))=(-1)^n/|Q| times the sum over h in Q of c(s;g1,...,g(n-1),h).
   Sum dc=0 over h and replace gn*h by h in the penultimate term: db=c. For n=1 the
   identity says c=0. These are finite continuous sums over either field, and |Q| is an
   ell-adic unit by the finite-quotient hypothesis. Refine the cover to make cocycle
   identities hold before sheafification and refine U to accommodate representatives.
5. These local primitives give zero positive cohomology. Negative terms vanish, while
   degree zero is precisely the scalar sheaf and has differential zero. Hence the map
   from the scalar module in degree zero to finite-quotient cochains is a quasi-isomorphism;
   localization as in sk-def-sfb-derived-categories makes it an isomorphism.
6. Compose the comparisons. Their degree-zero maps are the identity and the canonical
   resolution inclusions, so bar normalization identifies the composite with the stated
   trivialDerivedAugmentation. It is invertible for every injective resolution. For K=1
   the same maps are the identity under the canonical comparisons. Apply separately to
   E and Omega. The two analytic inputs in steps 2 and 3 remain WANTED statements.
-/
theorem prime_to_ell_condensed_acyclicity (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ∀ (Q : Type u) [Group Q] [Fintype Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (q : K →ₜ* Q), Function.Surjective q → Nat.Coprime (Nat.card Q) ell) :
    ScalarAcyclic E K ∧ ScalarAcyclic Ω K := by
  sorry

end Profinite.CondensedAction
