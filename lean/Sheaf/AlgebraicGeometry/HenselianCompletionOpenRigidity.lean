/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Henselian completion rigidity on the open complement

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XX, section 4.4,
printed pages 373--374 (CTC and its open-complement cohomology formulation);
Fujiwara 1995, Corollary 6.6.4 (the Noetherian case).
(blueprint: lem-per-henselian-completion-open-rigidity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a Noetherian henselian pair `(C, I)`, the canonical completion morphism induces
an isomorphism on the etale cohomology of its open complement with arbitrary torsion
abelian coefficients. The source of the projection is exactly the fibre product of
`Spec (AdicCompletion I C)` with `Spec C` minus `V(I)`. Here torsion is local torsion
of sections, without a uniform annihilator. Degrees `q : ℕ` include degree zero.
The comparison is the canonical inverse-image map, hence natural in the sheaf.

Source: ILO, Travaux de Gabber, Expose XX, section 4.4, printed pages 373--374;
Fujiwara 1995, Corollary 6.6.4.
(blueprint: lem-per-henselian-completion-open-rigidity)

Proof:
1. The Noetherian hypothesis makes I finitely generated. The completion algebra
   in lem-weil-pbc-adic-completion-mod-ideal identifies the quotient of the completion
   by the extended ideal with C/I and makes the completion adically complete.
   The completed pair is henselian by lem-weil-pbc-complete-pair-henselian.
   A prime contains the extended ideal exactly when its contraction contains I,
   so the complement after completion is the indicated fibre product.
2. Apply lem-per-admissible-modification-cohomology-presentation to obtain the common
   closed-fibre limit topos and the comparison of first-quadrant spectral sequences
   computing cohomology of the two open complements. The abutment map is precisely
   the canonical pullback, and all maps are natural in F.
3. The conservative family in lem-per-admissible-modification-valuative-stalks
   identifies each stalk of the coefficient comparison with the cohomology pullback
   for a dense inclusion of henselian valued fields. Apply
   lem-per-dense-henselian-field-etale-comparison to each stalk. Conservativity gives
   isomorphisms of the coefficient sheaves, hence of all E2 terms.
4. Induct on pages using kernels modulo images. In each bidegree the differentials
   eventually vanish because the sequences are first-quadrant, giving isomorphisms
   on E-infinity. In degree q the filtration has only the pieces 0 through q.
   Induction through its short exact sequences proves the abutment map bijective.
   This includes q=0. For nilpotent I both open complements are empty and their
   cohomology groups vanish.
-/
theorem bijective_cohomologyMap_henselianCompletion_openComplement
    (C : Type u) [CommRing C] [IsNoetherianRing C] (I : Ideal C) [HenselianRing C I]
    (F : Sheaf
      (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
        ⟨(PrimeSpectrum.zeroLocus (I : Set C))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus (I : Set C)).isOpen_compl⟩).smallEtaleTopology
      AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) :
    Function.Bijective
      (cohomologyMap
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap C (AdicCompletion I C))))
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            ⟨(PrimeSpectrum.zeroLocus (I : Set C))ᶜ,
              (PrimeSpectrum.isClosed_zeroLocus (I : Set C)).isOpen_compl⟩)) F q) := by
  sorry

end AlgebraicGeometry.Etale
