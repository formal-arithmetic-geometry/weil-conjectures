/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.AlgebraicGeometry.TotalQuotientRingMinimalProduct
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Normalization charts in the total ring of fractions

Source: Stacks Project, Morphisms, Tag 035P, parts (1) and (4), and Tag 0CDV
(blueprint: lem-sfb-normalization-affine-total-fractions).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An affine open of a reduced scheme with finitely many components on each quasi-compact
open has reduced section ring with finitely many minimal primes. Its inverse image in the
componentwise normalization is canonically the spectrum of the integral closure in the
localization at the nonzerodivisors. The displayed equation is over the affine open, using
exactly the structural algebra map into that integral closure: its composite with the
inclusion into the localization sends `a` to `a/1`. No Noetherian or module-finiteness
assumption is made. For the empty open all three rings are zero rings and both schemes
are empty.

Source: Stacks Project, Morphisms, Tag 035P (1), (4), and Tag 0CDV
(blueprint: lem-sfb-normalization-affine-total-fractions).

Proof:
1. Reducedness of X gives reducedness of its section ring A (def-pc-reduced-scheme).
   The finite generic-point set of lem-sfb-normalization-generic-residue-affine-charts
   and lem-weil-pbc-spec-irreducible-components-minimal-primes enumerate the minimal
   primes of A without repetition: V(p) has generic point p.
2. By lem-sfb-reduced-weakass-minimal all weakly associated primes are minimal.
   Apply lem-sc-affine-totalquotient-minimal-product to obtain the canonical A-algebra
   isomorphism from the total quotient ring to the product of minimal-prime localizations.
3. By lem-weil-pbc-minimal-prime-reduced-localization-field each factor is a field.
   Use lem-weil-pbc-affine-open-stalk-localization and def-weil-residue-field to identify
   it with the residue field at the corresponding generic point. These maps take a/1
   to the residue class of the germ of a, giving the generic-residue A-algebra structure.
4. This A-algebra isomorphism restricts to the integral closures: apply it and its
   inverse to monic equations (def-weil-pbc-integral-closure). Take spectra and compose
   with lem-sfb-normalization-generic-residue-affine-charts. Compatibility with A gives
   the displayed structural equation. The isomorphism is canonical since all the maps
   are the canonical localization, germ, residue and integral-closure maps.
5. On the empty open the sheaf axiom makes A a zero ring. Its localization and the
   integral-closure subring are zero rings too. A zero ring has empty spectrum, and the
   inverse image of the empty open is empty. This also covers the empty scheme. -/
theorem normalization_affine_total_fractions
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.affineOpens) :
    _root_.IsReduced Γ(X, U) ∧
    (minimalPrimes Γ(X, U)).Finite ∧
    (∃ e : (X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme ≅
        Spec (.of (integralClosure Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))))),
      e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U)
            (integralClosure Γ(X, U) (Localization (nonZeroDivisors Γ(X, U)))))) ≫
          U.2.isoSpec.inv = X.fromReducedNormalization ∣_ U.1) ∧
    (U.1 = ⊥ →
      Subsingleton Γ(X, U) ∧
      Subsingleton (Localization (nonZeroDivisors Γ(X, U))) ∧
      Subsingleton (integralClosure Γ(X, U) (Localization (nonZeroDivisors Γ(X, U)))) ∧
      IsEmpty (X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme ∧
      IsEmpty (Spec (.of
        (integralClosure Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))))))) := by
  sorry

end AlgebraicGeometry.Scheme
