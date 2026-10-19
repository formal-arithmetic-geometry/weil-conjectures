/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.RingTheory.WeaklyAssociatedTensorFlatFinitePresentation

/-!
# Fibre-generic detection of vertical principal ideals

Source: the agent-reconstructed finite-height valuation assertion in the trace-formula DAG;
Stacks Project, `algebra.tex`, Tag 05CB, `lemma-zero-at-weakly-ass-zero`, is background only.
The fibre-prime identification is an additional input, not a claim of Tag 05CB
(blueprint: lem-trf-vertical-principal-ideal-fibre-detection).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace Ideal

/-- Over a finite-height valuation domain, two generically invertible elements of a flat,
finitely presented algebra with geometrically reduced fibres generate the same ideal if
this holds after localizing at the inverse images of all fibre-component generic points.

Source: the agent-reconstructed finite-height valuation assertion of the trace-formula DAG;
Stacks Project, `algebra.tex`, Tag 05CB, `lemma-zero-at-weakly-ass-zero`, supplies only the
background detection principle (blueprint: lem-trf-vertical-principal-ideal-fibre-detection).

The fibre is Mathlib's `p.asIdeal.Fiber B = κ(p) ⊗[V] B`. Its geometric reducedness is
written explicitly after every residue-field extension, using tensor associativity and
commutativity to identify this with the base change in the node. The inverse-image prime
is obtained by `PrimeSpectrum.comap` along `Algebra.TensorProduct.includeRight`.
The condition on the closure of a singleton says exactly that the point is generic in
an irreducible component. No nonempty-fibre or Noetherian hypothesis is imposed.

Proof plan, following the six steps of the node:
1. Flat tensor injectivity (lem-weil-pbc-flat-tensor-exact) makes every nonzero element of
   V act injectively on B. Identify B tensor K with the localization at those elements
   via b tensor (a/s) maps to ab/s and b/s maps to b tensor (1/s), using the tensor and
   localization definitions (def-weil-pbc-module-tensor-product and
   def-weil-pbc-module-localization). Thus B maps injectively to its generic fibre.
2. For h equal to f or g, express its generic inverse as b/s and cancel a nonzero scalar
   to get hb = s. Multiplication by b is injective, since bx = 0 implies sx = 0.
   Consequently x modulo h maps injectively to bx modulo s. Identify B/sB with
   (V/sV) tensor B by the mutually inverse maps (a modulo s) tensor x maps to ax modulo s
   and x modulo s maps to (1 modulo s) tensor x.
3. That injection preserves element annihilators. Apply lem-trf-flat-tensor-weakass-fibre
   with M = V/sV: a weakly associated prime of B/hB gives an exact-annihilator associated
   prime in the fibre at its contraction. Finite presentation and flatness are precisely
   the hypotheses needed; no Noetherian assumption is used.
4. The fibre is reduced by the geometric hypothesis. If its proper prime equals Ann(z),
   then z is nonzero and is not in Ann(z), since otherwise z squared is zero. Every prime
   contained in Ann(z) contains each a in Ann(z), by applying primality to az = 0 and
   z outside that prime. Thus Ann(z) is minimal. Apply
   lem-weil-pbc-spec-irreducible-components-minimal-primes and
   lem-weil-pbc-fibre-ring-primes-bijection: its generic point has inverse image the
   original weakly associated prime.
5. If r modulo h is nonzero, for (r,h) = (f,g) or (g,f), its annihilator is proper.
   Choose a prime minimal over it (lem-weil-pbc-minimal-prime-over-proper-ideal).
   Steps 3--4 make it a fibre-generic inverse image. The local ideal equality gives
   r/1 = h(y/u). Clearing fractions gives v(ur - hy) = 0 with u and v outside the prime.
   Thus vu annihilates r modulo h, contradicting primality. Hence r belongs to hB.
6. The two choices of (r,h) give the two ideal inclusions, hence equality.
-/
theorem span_singleton_eq_of_fibre_generic_localizations
    (K : Type u) [Field K] (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (B : Type v) [CommRing B] [Algebra V B] [Module.Flat V B]
    [Algebra.FinitePresentation V B]
    (hgeom : ∀ (p : PrimeSpectrum V) (L : Type (max u v)) [Field L]
      [Algebra p.asIdeal.ResidueField L],
      IsReduced (L ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B))
    (f g : B)
    (hf : IsUnit ((Algebra.TensorProduct.includeLeft : B →ₐ[V] B ⊗[V] K) f))
    (hg : IsUnit ((Algebra.TensorProduct.includeLeft : B →ₐ[V] B ⊗[V] K) g))
    (hlocal : ∀ (p : PrimeSpectrum V) (ξ : PrimeSpectrum (p.asIdeal.Fiber B))
      (q : PrimeSpectrum B),
      q = ξ.comap (Algebra.TensorProduct.includeRight : B →ₐ[V] p.asIdeal.Fiber B) →
      closure ({ξ} : Set (PrimeSpectrum (p.asIdeal.Fiber B))) ∈
        irreducibleComponents (PrimeSpectrum (p.asIdeal.Fiber B)) →
      Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal)) (Ideal.span {f}) =
        Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal)) (Ideal.span {g})) :
    Ideal.span {f} = Ideal.span {g} := by
  sorry

end Ideal
