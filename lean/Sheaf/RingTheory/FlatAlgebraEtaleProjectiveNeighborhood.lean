/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.TraceFormula.CompleteDevissageProjectiveLocalization

/-!
# Pointed étale projective neighborhoods of a flat finitely presented algebra

Source: Stacks Project, More on Flatness, Tag 05ID,
`proposition-finite-presentation-flat-at-point`, applied to the structure sheaf;
Tag 05IG, `lemma-weak-bourbaki-pre`, first proof paragraph
(blueprint: lem-trf-flat-algebra-etale-projective-neighborhood).

The fibres use Mathlib's order of tensor factors, `κ(p) ⊗[R] S`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

/-- The canonical fibre map of a commutative square of ring maps with a marked base prime.
It sends `λ ⊗ s` to `κ(a)(λ) ⊗ b(s)`; its data are Mathlib's heterobasic tensor map.
Source: Stacks Project, More on Flatness, Tag 05IG, first proof paragraph, with the
second fibre taken over `κ(p')`, as required by its base ring
(blueprint: lem-trf-flat-algebra-etale-projective-neighborhood). -/
noncomputable def Ideal.Fiber.mapOfPrimeSquare
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime]
    (hp : p = p'.comap (algebraMap R R'))
    (hcomm : (algebraMap S S').comp (algebraMap R S) =
      (algebraMap R' S').comp (algebraMap R R')) : p.Fiber S →+* p'.Fiber S' :=
  Algebra.TensorProduct.mapRingHom (algebraMap R R')
    (Ideal.ResidueField.map p p' (algebraMap R R') hp) (algebraMap S S')
    (RingHom.ext (Ideal.ResidueField.map_algebraMap p p' (algebraMap R R') hp)) hcomm

namespace Algebra

/-- A flat finitely presented algebra admits elementary étale neighborhoods on source
and base over which it is projective as a module, with the induced pointed étale fibre map.
Source: Stacks Project, More on Flatness, Tag 05ID (structure-sheaf specialization),
and Tag 05IG, first proof paragraph
(blueprint: lem-trf-flat-algebra-etale-projective-neighborhood).

Proof:
1. Apply [lem-trf-complete-algebra-devissage-etale-existence] to `N = S`, generated as
   an S-module by 1. This gives a pointed étale square `R → R₀`, `S → S₀` with unchanged
   residue fields. The multiplication isomorphism `S ⊗[S] S₀ ≅ S₀` transports its
   complete dévissage to `S₀/S₀/R₀`.
2. Put `T = S ⊗[R] R₀`. The projection `Spec T → Spec S` is étale by
   [lem-weil-pbc-fibre-product-affine-spectra] and
   [lem-weil-pbc-etale-scheme-base-change]. Its composite with `Spec S₀ → Spec T`
   is étale, so [lem-weil-pbc-etale-composition-cancellation] makes that map étale.
   The original square need not be cartesian.
3. By [lem-weil-pbc-lfp-affine-opens-finite-presentation], the affine étale map
   `T → S₀` is finitely presented. Base change and composition in
   [lem-weil-pbc-finite-presentation-base-change-composition] give finite presentation
   of `S₀` over `R₀`.
4. Translate flatness to affine spectra using [lem-weil-pbc-flat-ring-map-iff-flat-affine],
   base change by [lem-weil-pbc-flat-morphism-base-change], and translate back.
   The étale map `T → S₀` is flat by [lem-weil-pbc-etale-algebra-flat]. Composition
   by [lem-weil-pbc-flat-ring-map-comp] makes `S₀` flat over `R₀`.
5. The S₀-module S₀ is finitely presented. Apply
   [lem-trf-complete-algebra-devissage-projective-localization] to obtain an element
   f outside p₀ such that `(S₀)f` is projective over `(R₀)f`. Set `R' = (R₀)f` and
   `S' = (S₀)f`. By [lem-trf-localization-finite-presentation-ring-map], finite
   algebra presentation persists. The fraction maps identify `S₀ ⊗[R₀] (R₀)f` with
   `(S₀)f` by `b ⊗ (a/f^k) ↦ ab/f^k`, with inverse `b/f^k ↦ b ⊗ (1/f^k)`.
6. By [lem-weil-pbc-principal-localization-open-immersion], these localizations are
   standard opens, hence étale, and their composites are étale by
   [lem-weil-pbc-etale-composition-cancellation]. Both marked primes avoid f, so
   [lem-weil-pbc-localization-prime-residue-field-iso] gives their extensions,
   all contractions, and the unchanged local rings and residue fields. Explicitly,
   localizing at the primes after inverting f adds no denominators; the inverse
   local-ring maps are `a/s ↦ (a/1)/(s/1)` and
   `(a/f^k)/(b/f^l) ↦ af^l/(bf^k)`.
7. Repeat step 2 for the final square and base change to `κ(p')`. The base-change
   and affine-fibre-product nodes identify the resulting étale map with the fibre
   map after identifying `κ(p)` and `κ(p')` by their induced isomorphism.
   Tensor reassociation sends `(s ⊗ a) ⊗ t` to `s ⊗ at`, with inverse
   `s ⊗ t ↦ (s ⊗ 1) ⊗ t`. Thus the canonical fibre map is étale.
8. Its composite with `S → κ(p) ⊗[R] S` is the composite of `S → S'` with the
   corresponding inclusion into the new fibre. Therefore the inverse image of
   the fibre prime of q' contracts to q. Uniqueness in
   [lem-weil-pbc-fibre-ring-primes-bijection] identifies it with the fibre prime of q.

No finite generation of S' as an R'-module is asserted. -/
theorem exists_etale_projective_neighborhood
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    ∃ (R' : Type u) (S' : Type v) (_ : CommRing R') (_ : CommRing S')
      (_ : Algebra R R') (_ : Algebra S S') (_ : Algebra R' S')
      (p' : PrimeSpectrum R') (q' : PrimeSpectrum S')
      (hcomm : (algebraMap S S').comp (algebraMap R S) =
        (algebraMap R' S').comp (algebraMap R R'))
      (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
      (hq : PrimeSpectrum.comap (algebraMap S S') q' = q)
      (hpq' : PrimeSpectrum.comap (algebraMap R' S') q' = p'),
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap S S'))) ∧
      Function.Bijective (Ideal.ResidueField.map p.asIdeal p'.asIdeal
        (algebraMap R R') (congrArg PrimeSpectrum.asIdeal hp.symm)) ∧
      Function.Bijective (Ideal.ResidueField.map q.asIdeal q'.asIdeal
        (algebraMap S S') (congrArg PrimeSpectrum.asIdeal hq.symm)) ∧
      Algebra.FinitePresentation R' S' ∧ Module.Projective R' S' ∧
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Ideal.Fiber.mapOfPrimeSquare p.asIdeal p'.asIdeal
            (congrArg PrimeSpectrum.asIdeal hp.symm) hcomm))) ∧
      PrimeSpectrum.comap (Ideal.Fiber.mapOfPrimeSquare p.asIdeal p'.asIdeal
          (congrArg PrimeSpectrum.asIdeal hp.symm) hcomm)
        (PrimeSpectrum.preimageOrderIsoFiber R' S' p' ⟨q', hpq'⟩) =
          PrimeSpectrum.preimageOrderIsoFiber R S p ⟨q, hpq⟩ := by
  sorry

end Algebra
