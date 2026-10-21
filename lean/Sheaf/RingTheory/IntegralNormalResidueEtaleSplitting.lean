/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField

/-!
# Étale splitting for integral algebras with normal residue extensions

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`, and Fundamental Groups, Tag 0BST,
`lemma-inertia-invariants-etale`, second reduction paragraph
(blueprint: lem-dl-a1-integral-normal-residue-etale-splitting).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- An integral algebra with finite fibre and normal algebraic residue extensions with
finite automorphism groups splits after an étale base change into integral factors with
singleton, purely inseparable fibres. The prescribed prime lifts to the first factor.
`Normal` includes algebraicity. Every residue algebra structure below is the canonical map
induced by contraction; `Ideal.ResidueField` is the fraction field of the prime quotient.

Source: Stacks Project, Tags 0BSR and 0BST, second reduction paragraph
(blueprint: lem-dl-a1-integral-normal-residue-etale-splitting).

Proof plan:
1. Enumerate the finite fibre. For each residue extension E/k,
   `lem-dl-a1-normal-finite-aut-separable-subfield` gives a finite-dimensional separable
   subfield F. By `lem-weil-pbc-separable-first-purely-inseparable`, E/F is purely inseparable.
   This does not assert that E/k is finite-dimensional.
2. Apply `lem-dl-a1-integral-finite-residue-model`: choose a module-finite intermediate
   algebra C in D, with D integral over C, bijective contraction on the fibre, finite residue
   fields L over k, and E/L purely inseparable.
3. Apply `lem-weil-pbc-integral-fibre-etale-splitting` to Spec C over Spec A. This gives an
   affine étale neighbourhood Spec B and a clopen partition into factors C_j with singleton
   purely inseparable fibres. Use `def-weil-finite-integral-morphism` and
   `lem-weil-pbc-fibre-product-affine-spectra` to identify this base change with B tensor C.
4. By `lem-weil-pbc-integral-base-change`, B tensor D is integral over B. The clopen pieces
   give orthogonal idempotents summing to one (`lem-weil-pbc-spec-clopen-idempotent`).
   Their images e_j give factors D_j = e_j (B tensor D), with identity e_j. The maps
   x to (e_j x)_j and (x_j)_j to sum x_j are inverse B-algebra maps. The factors are quotients,
   so monic integral equations descend to them.
5. For each C_j fibre point t_j, the finite-model fibre bijection selects a unique original
   prime with residue E over L. Use `lem-weil-pbc-fibre-product-affine-spectra` over C and
   `lem-weil-pbc-fibre-product-points` to identify its remaining fibre with Spec of
   E tensor_L kappa(t_j). It has a prime by
   `lem-weil-common-extension-fields-tensor-nontrivial` and
   `lem-weil-common-extension-fields-maximal-ideal`. The purely inseparable map Spec E to
   Spec L is universally injective (`def-weil-radicial-morphism`), so this prime is unique.
6. Universal injectivity persists under further base change; its radicial characterization
   and `lem-weil-pbc-fibre-product-point-residue-field` show that kappa(q_j)/kappa(t_j) is
   purely inseparable. Combine with kappa(t_j)/kappa(p'): in characteristic p, compose the
   p-power exponents; in characteristic zero both extensions are trivial.
7. Lift the specified q using a prime of kappa(q) tensor_k kappa(p'), again by nontriviality
   and maximal-ideal existence, and the affine pullback and point correspondences. Exactly
   one factor idempotent survives at this prime, since they are orthogonal and sum to one.
   Thus the number of factors is positive. Permute them to put this factor first. Its unique
   prime over p' is the indicated q_j, giving the asserted contraction formula. -/
theorem exists_integral_normal_residue_etale_splitting
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] (p : PrimeSpectrum A) (q : PrimeSpectrum D)
    (hq : PrimeSpectrum.comap (algebraMap A D) q = p)
    (hfibre : Set.Finite {r : PrimeSpectrum D |
      PrimeSpectrum.comap (algebraMap A D) r = p})
    (hnormal : ∀ (r : PrimeSpectrum D)
      (hr : PrimeSpectrum.comap (algebraMap A D) r = p),
      @Normal p.asIdeal.ResidueField r.asIdeal.ResidueField _ _
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra)
    (hauto : ∀ (r : PrimeSpectrum D)
      (hr : PrimeSpectrum.comap (algebraMap A D) r = p),
      Finite (@AlgEquiv p.asIdeal.ResidueField r.asIdeal.ResidueField r.asIdeal.ResidueField
        _ _ _
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      ∃ (p' : PrimeSpectrum B), PrimeSpectrum.comap (algebraMap A B) p' = p ∧
      ∃ (q' : PrimeSpectrum (B ⊗[A] D)),
        PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom) q' = q ∧
        PrimeSpectrum.comap (algebraMap B (B ⊗[A] D)) q' = p' ∧
      ∃ (n : ℕ) (hn : 0 < n) (Dj : Fin n → Type (max u v))
        (_ : ∀ j, CommRing (Dj j)) (_ : ∀ j, Algebra B (Dj j))
        (e : (B ⊗[A] D) ≃ₐ[B] (∀ j, Dj j))
        (qj : ∀ j, PrimeSpectrum (Dj j))
        (hlying : ∀ j, PrimeSpectrum.comap (algebraMap B (Dj j)) (qj j) = p'),
        (∀ j, Algebra.IsIntegral B (Dj j)) ∧
        (∀ (j : Fin n) (r : PrimeSpectrum (Dj j)),
          PrimeSpectrum.comap (algebraMap B (Dj j)) r = p' → r = qj j) ∧
        (∀ j, (Ideal.ResidueField.map p'.asIdeal (qj j).asIdeal
          (algebraMap B (Dj j)) (congrArg PrimeSpectrum.asIdeal (hlying j)).symm
          ).IsPurelyInseparable) ∧
        q'.asIdeal = ((qj ⟨0, hn⟩).asIdeal.comap
          ((Pi.evalRingHom Dj ⟨0, hn⟩).comp e.toRingHom)) := by
  sorry

end Algebra
