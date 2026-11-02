/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData

public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen

/-! # Actual internal endomorphism reductions and scalar quotient cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Derived endomorphisms of the actual internal reductions are the locally constant
sections of the zeroth cohomology of the quotient algebraic Hom complex, naturally in
all quotient arrows.

Source: Stacks Project, Tags 09C5, 08JH and 06YQ; current blueprint,
`sk-prop-integral-local-structure`, Compatible isomorphisms.
(blueprint: lem-pe-internal-perfect-endomorphism-hom-comparison).

Proof: localize the small pro-etale site at W. The DVR quotients are finite, so the
normalized finite-discrete ordinary-coefficient equivalence applies to each level.
Choose bases of the finitely many nonzero terms of P. The scalar model has terms
finite sums of the internal regular module, hence is K-flat by bounded-flat
K-flatness. Derived reduction is therefore the ordinary constant complex P/pi^j.
The canonical derived-to-ordinary comparison agrees with scalar balancing, because
both are mates of the same restriction-of-scalars adjunction. Under the finite
coefficient equivalence, the terms of the reduced complex are constant finite free
modules. Weak contractibility makes sections exact, so these terms are projective;
the bounded-above complex is K-projective. The localization bijection computes its
derived endomorphisms as chain maps modulo chain homotopy. This is H^0 of the signed
Hom complex of its sections. Finite freeness and boundedness identify the latter
with sections of the constant quotient of moduleHomComplex P P: on each finite
matrix entry this is ordinary scalar reduction. Exact constant sheafification and
exact sections commute with kernels, images and cohomology. Sections of a constant
sheaf are locally constant functions on connected components. Finally reduction of
a chain map, and of a homotopy, reduces its matrix entries; scalar balancing has
this same formula. Thus the bijections commute with every successor arrow, and
induction gives the equation for all n<=m. Empty W and zero P yield singleton sets;
no connectedness, finite number of components or completeness is used. -/
theorem internalPerfectEndomorphism_homComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ∀ n : ℕ,
      (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op n) ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n m : ℕ) (h : n ≤ m) (x : (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op m)),
        e n ((internalReductionHomTower l E W.left
          (internalPerfectScalarModel l E W.left P)
          (internalPerfectScalarModel l E W.left P)).map (homOfLE h).op x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (m + 1) (n + 1)
              (Nat.succ_le_succ h)) 0) (e m x) := by sorry

end AlgebraicGeometry.ProEtale
