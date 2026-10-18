/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LocalCurveBranches
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Limits

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.NagataRing
import Sheaf.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.SemilocalNormalizationDimOne
import Sheaf.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.LocalCurvePrincipalTotalFractions
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# DVR branches of a punctured strictly local curve

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
`lem-exc-punctured-curve-branches.md`,
order 1918 (Stacks Tags 0C3S and 00PD)
(blueprint: lem-exc-punctured-curve-branches).
-/

noncomputable section

@[expose] public section

set_option autoImplicit false

universe u

open Set RingTheory AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- The punctured spectrum is the finite scheme coproduct of the canonical component
fields, whose normalization rings are excellent strictly henselian DVRs with the original
residue field. Source: blueprint lemma 1918; Stacks Tags 0C3R, 0C3S and 00PD
(blueprint: lem-exc-punctured-curve-branches).

Proof:
1. Minimal primes are finite by Noetherianity. Each quotient by a minimal prime is a
   one-dimensional local Noetherian domain (a longer chain contradicts dimension one).
2. Excellence implies Nagata (lem-exc-quasi-excellent-nagata). Apply N-2 to the identity
   field extension to obtain finite normalization of each component and their product.
3. Apply lem-sc-semilocal-dim-one-normalization: each normalization is a semilocal normal
   Noetherian one-dimensional domain with the original component fraction field.
4. The finite-over-henselian-local-product theorem decomposes each normalization. A domain
   has no nontrivial idempotents, so there is exactly one local henselian factor. Its residue
   extension is finite over the algebraically closed original residue field, hence the
   canonical residue map is an isomorphism and the normalization is strictly henselian.
5. Apply lem-sc-normal-dim1-dvr (Stacks 00PD) to each normal one-dimensional local domain.
6. Finiteness implies finite type, so lem-exc-finite-type-localization-excellent gives
   excellence of every normalization.
7. Choose the principal puncture of lem-exc-local-curve-principal-total-fractions. Its
   localization is the total fraction ring, canonically the product of component fields by
   lem-weil-pbc-reduced-noetherian-total-ring-fractions. The component maps are quotient
   maps followed by fraction inclusions and agree with the branch-algebra construction.
8. The principal-localization open immersion identifies the puncture as schemes with this
   product's spectrum. The finite affine coproduct theorem gives the displayed coproduct
   over Spec R, with the canonical component maps.
-/
theorem punctured_curve_has_dvr_branches
    (R : Type u) [CommRing R] [IsReduced R]
    (hExcellent : IsExcellent R) [IsStrictlyHenselianLocalRing R]
    (hDim : ringKrullDim R = (1 : WithBot ℕ∞))
    (p : ℕ) (hp : Nat.Prime p)
    (hChar : ringChar (IsLocalRing.ResidueField R) = p)
    (hAlgClosed : IsAlgClosed (IsLocalRing.ResidueField R)) :
    Finite (excLocalCurveBranchIndex R) ∧
    ∃ hLocal : ∀ a : excLocalCurveBranchIndex R,
        IsLocalRing (excLocalCurveBranchIntegralClosure R a),
      (∀ a : excLocalCurveBranchIndex R,
        IsDiscreteValuationRing (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R,
        IsStrictlyHenselianLocalRing (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R, IsExcellent (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R,
        ∃ e : @IsLocalRing.ResidueField (excLocalCurveBranchIntegralClosure R a) _ (hLocal a) ≃+*
            IsLocalRing.ResidueField R,
          ∀ r : R, e (@IsLocalRing.residue (excLocalCurveBranchIntegralClosure R a) _ (hLocal a)
            (excLocalCurveBranchAlgebraMap R a r)) = IsLocalRing.residue R r) ∧
      (∀ a : excLocalCurveBranchIndex R,
        IsFractionRing (excLocalCurveBranchIntegralClosure R a)
          (excLocalCurveBranchFractionRing R a)) ∧
      ∃ U : (Spec (.of R)).Opens,
        (∀ x : Spec (.of R), x ∈ U ↔ x ≠ IsLocalRing.closedPoint R) ∧
        ∃ e : U.toScheme ≅
            ∐ (fun a : excLocalCurveBranchIndex R ↦
              Spec (.of (excLocalCurveBranchFractionRing R a))),
          e.hom ≫ Sigma.desc (fun a ↦ Spec.map
            (CommRingCat.ofHom (algebraMap R (excLocalCurveBranchFractionRing R a)))) = U.ι := by
  sorry

end
