/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology

import Sheaf.SixFunctors.TraceFormula.NodalLogRegularity
import Sheaf.AlgebraicGeometry.TameNormalizationLogRegular
import Sheaf.AlgebraicGeometry.TameLogQuotientModification
import Sheaf.AlgebraicGeometry.NoetherianLogPairStrictResolution
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-!
# Gabber's prime-to-ell covering by regular pairs

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IX, Theorem 1.1 and
its proof in 1.3--2.4, printed pp. 131--134; Expose II, 1.2.2 and 2.3.1; Expose VIII,
4.1.4 and 4.2.2(i) (blueprint: lem-per-gabber-prime-to-ell-regular-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reduced quasi-excellent Noetherian scheme has a finite prime-to-ell alteration
cover by regular Noetherian schemes with the exact inverse image of the prescribed
nowhere dense closed set as a strict normal crossings boundary. The object `base`
is required to be the identity scheme over `S`; it only bundles the target of the
covering family in the full subcategory `alt/S`.

Source: ILO, Expose IX, Theorem 1.1, printed p. 131, with reduced boundary as in
VIII 4.1.4 and 4.2.2(i) (blueprint: lem-per-gabber-prime-to-ell-regular-cover).

Proof:
1. Apply `lem-per-uniformization-nodal-quotient-reduction`. Its marked nodal
   quotient assertion is proved in the following steps. In its notation, `Y` is
   affine excellent regular, `Y'` is the normalization in a connected finite etale
   `G`-torsor off `T`, `C` is integral excellent, and the inverse image of the
   effective Cartier divisor `E` on `X = C/G` lies in
   `B = |D| union f⁻¹(b⁻¹|T|)`. No regularity of `X` is assumed.
2. The group `G` has ell-power order invertible on `Y`. Apply
   `lem-per-tame-normalization-log-regular` to the given torsor and its normalization
   `Y'`. The pair `(Y', b⁻¹|T|)` is log regular; its underlying scheme need not be regular.
3. Apply `lem-trf-nodal-log-regularity` to the projective, flat, finitely presented
   nodal morphism `C → Y'`, using `lem-kun-projective-implies-proper`. The geometric
   fibres are nonempty connected nodal curves, the morphism is smooth off the base
   boundary, and `D` is effective Cartier, etale over `Y'`, in the relative smooth
   locus. Hence `B` is nowhere dense and `(C, B)` is log regular.
4. The action preserves `B` and is free above the torsor open: each stabilizer
   maps into a trivial stabilizer downstairs. That dense open contains `C ∖ B`.
   The order is invertible on `C`, which is separated Noetherian, and the action
   is admissible. Apply `lem-per-tame-log-quotient-modification` to obtain a proper
   birational `rho : M → X`, with `M` integral excellent Noetherian and log regular
   boundary `B_M` containing `rho⁻¹(pi(B))`. Surjectivity of `pi` and
   `pi⁻¹|E| ⊆ B` imply `rho⁻¹|E| ⊆ B_M`.
5. Apply `lem-per-noetherian-log-pair-strict-resolution` to obtain a proper
   birational `e : R → M`, with `R` integral regular Noetherian and strict normal
   crossings boundary `A` containing `e⁻¹B_M`. The composite `r : R → X` is proper
   by `lem-weil-pbc-proper-composition`, and birational by intersecting the dense
   isomorphism opens. Thus `r⁻¹|E| ⊆ |A|`.
6. Check equality with a boundary, not just containment. A local nonzero equation
   `a` of `E` stays nonzero by dominance. In local parameters for the branches
   of `A`, it is a unit after inverting their product. By
   `lem-trf-regular-local-ufd-boundary-factorization`, it is a unit times a monomial
   in those parameters. Its reduced support consists exactly of the branches
   with positive exponent. Taking closures shows that these are global components
   of `A`. Deleting the other components preserves the regular-intersection and
   codimension conditions of `def-trf-strict-normal-crossings-boundary`; the product
   of the remaining distinct parameters gives a radical effective Cartier ideal.
   With no remaining branches the boundary is empty. This proves the marked assertion.
7. The reduction of Step 1 now gives the finite covering in `alt/S` for the given
   `S`, `Z`, and `ell`, with all stated regularity, Noetherianity, and exact support
   clauses. Objects of `alt/S` are finite type by
   `def-per-prime-to-ell-alteration-topology`. Neither finite dimension nor excellence
   of the original scheme is required. -/
theorem gabber_primeToEll_regular_cover
    (S : Scheme.{u}) [IsReduced S] [IsNoetherian S]
    (hS : ∀ V : S.affineOpens, IsQuasiExcellent Γ(S, V.1))
    (Z : Set S) (hZ : IsClosed Z) (hZrare : IsNowhereDense Z)
    (ell : ℕ) [Fact ell.Prime]
    (hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)) :
    ∃ base : PrimeToEllAlteration.Alt S,
      base.obj = Over.mk (𝟙 S) ∧
      ∃ (n : ℕ) (T : Fin n → PrimeToEllAlteration.Alt S) (q : ∀ b, T b ⟶ base),
        PrimeToEllAlteration.IsCoveringFamily ell T q ∧
        (∀ b, IsRegularScheme (T b).obj.left ∧ IsNoetherian (T b).obj.left) ∧
        ∀ b, ∃ H : (T b).obj.left.IdealSheafData,
          IsStrictNormalCrossingsBoundary H ∧
          (H.support : Set (T b).obj.left) = (T b).obj.hom ⁻¹' Z := by
  sorry

end AlgebraicGeometry
