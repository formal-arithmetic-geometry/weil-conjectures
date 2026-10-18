/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CoefficientDuality
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Coefficient biduality at the finite, integral and field stages

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-weil-coefficient-frobenius; Stacks Tags 0AVF, 066Z and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Ordinary duals are algebraic module duals. Finite means finitely generated.
The integral ordinary assertion is deliberately different from the derived assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace WeilConjectures

/-- The three self-injective coefficient stages have exact ordinary duality,
finite-module evaluation isomorphisms, and a derived anti-equivalence on bounded
finite cohomology. Algebraic closure means the algebraic field, with ordinary duals.
Source: blueprint lem-weil-coefficient-frobenius, clause 1; Stacks 0AVF
(blueprint: lem-weil-coefficient-frobenius).

Proof:
1. The DVR description of O_E gives principal ideals, hence Noetherianity.
   Its positive quotients are finite; therefore Artinian and Noetherian. Fields
   are Artinian and Noetherian because their only ideals are zero and the unit ideal.
2. Every quotient ideal is (pi^i), 0 <= i <= n; cancellation in O_E gives
   Ann(pi^(n-i)) = (pi^i), including i = 0, n and n = 1.
3. A linear map (pi^i) -> A has value pi^i b at pi^i, and multiplication by b
   extends it. Apply lem-sf-baer-criterion. For a field use its two ideals.
   Restriction is onto for an inclusion, and its kernel is the maps factoring
   through the quotient: this proves exactness on all modules.
4. A finite A-module has finite underlying set, hence finite dual. Present it by
   two finite free modules using lem-sc-noetherian-finite-module-finite-presentation.
   Twice dualizing preserves the right-exact presentation. Finite free evaluation
   is invertible by lem-sf-finite-projective-dual, and naturality identifies the
   induced cokernel isomorphism with evaluation on M.
5. For either field stage a finite spanning list reduces to a finite basis.
   Apply lem-sf-finite-projective-dual; no finiteness of the underlying field is used.
6. The ring in degree zero is K-injective by self-injectivity and
   lem-weil-pbc-bounded-below-injectives-kinjective. Thus RHom(-,R) is computed by
   (DC)^j = Hom(C^(-j),R), with d(f) = (-1)^(j+1) f d_C.
   Exactness and lem-sp-exact-functor-preserves-homology give H^j(DC) = D H^(-j)(C).
   The signed evaluation x |-> (f |-> (-1)^j f(x)) is a chain map and a
   quasi-isomorphism by finite-module evaluation. Localization inverts it.
   It obeys D(delta_C) delta_DC = 1, so the restricted dual is its own
   contravariant quasi-inverse. Exactness on triangles follows from the cone
   formula, or lem-sf-exact-functor-derived-triangulated. -/
theorem coefficient_frobenius
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    coefficientFrobeniusProperties (Padic.coefficientExtensionRing l E n) ∧
      coefficientFrobeniusProperties E ∧
      coefficientFrobeniusProperties (AlgebraicClosure (Padic l)) := by
  sorry

/-- Integral coefficients are not quasi-Frobenius; finite projectives, but not
all finite modules, are ordinarily reflexive.
Source: blueprint lem-weil-coefficient-frobenius, clause 2; Stacks 0AVF and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 7): T = O_E/(pi) is nonzero. Every map T -> O_E is zero,
since pi annihilates its image and O_E is a domain. Thus T** = 0 and its
ordinary evaluation is not invertible. Dualizing multiplication by pi leaves
a nonsurjective multiplication-by-pi map, contradicting self-injectivity
(lem-sf-baer-criterion). Finite projectives remain reflexive by
lem-sf-finite-projective-dual. -/
theorem integral_coefficient_ordinary_duality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ¬ (IsArtinianRing (Padic.coefficientExtensionIntegers l E) ∧
      Module.Injective (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l E)) ∧
    (∀ M : ModuleCat.{u} (Padic.coefficientExtensionIntegers l E),
      Module.Finite (Padic.coefficientExtensionIntegers l E) M →
      Module.Projective (Padic.coefficientExtensionIntegers l E) M →
      Function.Bijective (Module.Dual.eval (Padic.coefficientExtensionIntegers l E) M)) ∧
    ∃ M : ModuleCat.{u} (Padic.coefficientExtensionIntegers l E),
      Module.Finite (Padic.coefficientExtensionIntegers l E) M ∧
      ¬ Function.Bijective (Module.Dual.eval (Padic.coefficientExtensionIntegers l E) M) := by
  sorry

/-- Every bounded integral complex with finite cohomology is perfect and its
canonical derived evaluation is invertible.
Source: blueprint lem-weil-coefficient-frobenius, clause 2; Stacks 066Z and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Steps 8--9): O_E is Noetherian by its principal-ideal DVR description.
For a finite module M choose a finite presentation O_E^u -> O_E^v -> M.
Its relation module is finite and torsion-free, hence finite free by
lem-sc-dvr-fg-torsionfree-free. This gives a length-one finite-free resolution.
Assemble the finitely many perfect cohomology objects using
lem-sf-perfect-cohomology-assembly. For the resulting bounded finite-projective
model apply the signed termwise evaluation calculation of Step 9, stated next. -/
theorem integral_coefficient_derived_duality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)))
    (hK : boundedFiniteCoefficientComplex (Padic.coefficientExtensionIntegers l E) K) :
    DerivedCategory.IsPerfectRingComplex K ∧ IsIso (coefficientDerivedEvaluation K) := by
  sorry

/-- Perfect complexes over any commutative ring have canonical derived biduality;
no self-injectivity is assumed.
Source: blueprint lem-weil-coefficient-frobenius, clause 3; Stacks 07VI and 0A66
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 9): Choose a bounded finite-projective model P. It is
K-projective by lem-sc-bounded-above-projective-kprojective. For a K-injective
resolution R[0] -> I the cone of Hom(P,R[0]) -> Hom(P,I) is the Hom complex
into the acyclic cone, hence acyclic. Thus termwise duality computes RHom.
The dual DP is again bounded finite projective by lem-sf-finite-projective-dual,
so the same calculation computes the double dual by DDP. In degree j,
x |-> (f |-> (-1)^j f(x)) commutes with differentials and is an isomorphism
by finite-projective evaluation. This chain isomorphism represents precisely
the transpose of the Koszul-interchanged evaluation used in the definition. -/
theorem perfect_coefficient_derived_evaluation
    (R : Type u) [CommRing R] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    IsIso (coefficientDerivedEvaluation K) := by
  sorry

/-- The finite-Tor point consequence at the finite coefficient stage.
At the two field stages all bounded finite-cohomology complexes have finite Tor
amplitude; at the integral stage the preceding integral theorem applies already.
Source: blueprint lem-weil-coefficient-frobenius, final clause; Stacks 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 10): lem-trf-finite-tor-amplitude-perfect supplies a bounded
finite-free model for the finite-stage complex of finite Tor amplitude.
Apply perfect_coefficient_derived_evaluation; it has no injectivity hypothesis.
Over fields finite cohomology is finite free, and
lem-sf-perfect-cohomology-assembly gives perfectness. Over O_E use Step 8. -/
theorem finiteTor_point_coefficient_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (K : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)))
    (hK : boundedFiniteCoefficientComplex (Padic.coefficientExtensionRing l E n) K)
    (hTor : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)) K) :
    IsIso (coefficientDerivedEvaluation K) := by
  sorry

end WeilConjectures
