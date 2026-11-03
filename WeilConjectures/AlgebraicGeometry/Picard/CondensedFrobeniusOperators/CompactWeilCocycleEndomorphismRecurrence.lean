/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaIteratedWeil

/-! # Recurrence for the direct compact-support Weil operator

Source: latest blueprint compact-description proof, expanded transport-composition,
Weil-cocycle and naturality calculation.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The direct (r+1)-power transport and Weil map give the r-power operator
followed by the degree-one operator, on the derived coefficient complex.
Source: latest blueprint compact-description proof and this node's steps 2--5.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).

Proof: paste the direct compact-support squares for g and g^r using one retained
compactification. Point insertion and normalized proper/open exchange composition
identify their composite with the (r+1)-square followed by the inverse pullback
compositor. The defining Iso.powStr recursion expresses phi^[r+1] as the forward
compositor, pullback of phi, and phi^[r]. The two compositors cancel after applying
compact sections. Naturality of r-power compact transport at phi moves that map
past the transport. Associativity yields U_r followed by U_1. The degree-one
formula is the definition of the global operator, with the unit-normalized
iterated Weil map at one. Pullback unit coherence identifies it with phi. No homology is applied.
The finite transport data agree by their unique normalization; Iso.pow and Aut.pow
agree by induction. These identifications use the same positive coefficient ring.
-/
theorem compact_weil_cocycle_endomorphism_recurrence
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (c : Compactification (condensedFrobeniusGeometry F Y₀).a)
    :
    condensedGlobalFrobenius F Y₀ ell hEll E n hn K c 1 (Nat.le_refl 1) =
      (let Λ := finiteCoefficient ell E n
       let S := finiteTransportData F ell hEll E n hn
       let q := poweredGeometry F Y₀ 1
       compactTransport Λ S.val q c c K.carrier
           (S.property.pull_constructible q K.carrier) ≫
         (Γ Λ (Spec (.of F.k))).map
           ((C Λ c).map
             ((eqToIso (congrArg (fun f => (L Λ f).obj K.carrier.obj)
               (congrArg Iso.hom (Iso.pow_one (condensedFrobeniusGeometry F Y₀).h)))).hom ≫
               K.φ.hom))) ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        condensedGlobalFrobenius F Y₀ ell hEll E n hn K c (r + 1) (by omega) =
          condensedGlobalFrobenius F Y₀ ell hEll E n hn K c r hr ≫
            condensedGlobalFrobenius F Y₀ ell hEll E n hn K c 1 (Nat.le_refl 1) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
