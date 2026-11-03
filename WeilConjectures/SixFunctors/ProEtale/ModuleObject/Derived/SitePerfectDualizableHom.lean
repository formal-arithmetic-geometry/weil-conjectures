/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeSitePerfectDual

/-! # Internal Hom through the coefficient dual

Source: current Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-dualizable-biduality/`
`prop-sf-dualizable-hom.md`, order 3499 (blueprint: prop-sf-dualizable-hom).

The declarations state the pro-étale condensed-coefficient assertion and its finite
coefficient small-étale realization.  The displayed map is the existing canonical
`ihomUnitTensorToIhom`: its source is the coefficient dual tensored with the target,
and its target is the derived internal Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! The pulled-back coefficient ring uses the canonical ring-object structure induced by
`p_X^*`; the local instance below keeps the derived module category notation independent
of any local Brown-hypothesis bundle. -/

section

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  (X : Scheme.{u})

local instance condensedRingObj_monObj : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

/-! The hypotheses `hK` and `hM` render membership in the bounded constructible
finite-Tor subcategory `D^b_ctf(X, Λ)`; `hPerfect` renders the local bounded
finite-projective hypothesis. -/

/-- In the current condensed coefficient-site interpretation, a locally bounded
finite-projective object is dualizable: for every bounded constructible finite-Tor
target, coefficient dual tensor target maps isomorphically to derived internal Hom.

Source: current Weil conjectures blueprint,
`part-duality-trace-formula/sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/`
`sk-thm-sf-kunneth-verdier/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`,
statement and proof steps 1--5 (blueprint: prop-sf-dualizable-hom).

Proof: `native_sitePerfect_dual` performs the local finite-projective calculation:
finite free retract terms have duals, their bounded signed dual complexes are K-flat,
and their exact pairing localizes and descends over the perfect cover. It supplies an
exact pairing with the actual coefficient dual. The closed-category evaluation comparison
for this pairing is precisely `ihomUnitTensorToIhom`, so it is invertible. No biduality,
constructibility, or six-operation comparison is used in this local calculation. -/
theorem sitePerfect_dualizable_hom
    [IsCommMonObj Λ]
    (K M : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : constantModelBoundedConstructible Λ X M ∧
      DerivedCategory.finiteTorAmplitude _ M)
    (hPerfect : IsPerfectOnCoefficientSite Λ X K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  have _ := hK
  have _ := hM
  obtain ⟨_, ep, _⟩ := native_sitePerfect_dual Λ X K hPerfect
  let := ep
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom ((ihom K).obj (𝟙_ _)) K M

end

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.Etale.DerivedCategory

/-! For a finite coefficient ring the same assertion is stated on the small étale site,
using the recorded bounded-constructible predicate `isBoundedConstructible`
(def-weil-pbc-constructible-complexes) and the finite-Tor predicate `hasTorAmplitudeIn`
(def-kun-tor-amplitude). -/

variable {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}

/-- The finite-coefficient small-étale realization of
`prop-sf-dualizable-hom`.  Its hypotheses spell out the bounded constructible
finite-Tor subcategory, and `IsSitePerfect` is the local bounded
finite-projective condition on the coefficient site.

Source: current Weil conjectures blueprint,
`part-duality-trace-formula/sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/`
`sk-thm-sf-kunneth-verdier/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`,
finite-coefficient small-étale clause (blueprint: prop-sf-dualizable-hom).

Proof: the existing small-etale site-perfect theorem carries out the same bounded
finite-projective local dual calculation and descent. Its right dual is also a left dual
by the derived braiding. Apply the closed-category theorem to that exact pairing; its
conclusion concerns the specified canonical evaluation comparison. -/
theorem sitePerfect_dualizable_hom_etale
    (K M : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : DerivedCategory.isBoundedConstructible A X M ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b M)
    (hPerfect : IsSitePerfect K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  have _ := hK
  have _ := hM
  let := hPerfect.isDualizable.some
  let : BraidedCategory (DerivedCategoryModule A X) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  let := BraidedCategory.exactPairing_swap K Kᘁ
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K M

/-- Internal Hom through the coefficient dual, in the setting of `def-sf-datum`: let `k` be
a field, `Λ` a finite commutative ring with a Tate twist datum whose exponent is invertible
on `X`, and `X` separated, of finite type and compactifiable over `k`. If
`K ∈ D^b_ctf(X, Λ)` is, locally on the small étale site, quasi-isomorphic to a bounded
complex of finite projective `Λ_X`-modules (`IsSitePerfect`), then for every
`M ∈ D^b_ctf(X, Λ)` the canonical comparison `K^∨ ⊗^L M ⟶ RHom(K, M)`
(`ihomUnitTensorToIhom`, with `K^∨ = RHom(K, Λ_X)`) is an isomorphism.

Source: current Weil conjectures blueprint,
`part-duality-trace-formula/sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/`
`sk-thm-sf-kunneth-verdier/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`,
order 3499, and its proof (blueprint: prop-sf-dualizable-hom).

Proof (node steps 1--5, on the ringed site `(X_et, Λ_X)`):
1. The derived internal Hom `H = RHom_Λ` is the right adjoint of the K-flat derived tensor
   (lem-sf-ringed-derived-closed-symmetric-monoidal, def-weil-derived-pullback-tensor-hom);
   the comparison is evaluation `e : M ⊗ H(K, Λ_X) ⟶ H(K, M)` after symmetry. Choose on
   each chart a bounded representative `P` of `K` with finite-free retract terms.
2. `D = Hom^•(P, Λ[0])` represents `H(K, Λ_X)` and `Hom^•(P, F)` represents `H(K, M)` for
   any representative `F` of `M` (lem-sfb-ringed-site-finite-retract-dual-exact,
   lem-pc-bounded-exact-term-hom-quasi-iso, def-pur-derived-internal-hom); `D` is bounded
   flat, hence K-flat (lem-sfb-ringed-site-bounded-dual-components,
   lem-pc-bounded-above-flat-kflat-site); choose `F` K-flat with flat terms
   (lem-pc-kflat-resolution).
3. Termwise `B ⊗ (P^i)^∨ ≅ Hom(P^i, B)` (lem-sf-hom-finite-projective,
   lem-pc-finite-projective-internal-hom-evaluation) assembles to a chain isomorphism
   `Tot(F ⊗ D) ≅ Hom^•(P, F)` (lem-sfb-ringed-site-bounded-evaluation-assembly).
4. The representative normalization of lem-sfb-ringed-site-duality-maps identifies this
   chain isomorphism with `e` on the chart, compatibly with restriction.
5. Slice restriction is exact (lem-pur-site-restriction-module-adjunction-exact), so the
   cohomology sheaves of the cone of `e` vanish on a cover, hence globally; `e` is an
   isomorphism, and so is the displayed map.
The existing small-étale site-perfect theorem realizes the local finite-projective
calculation and descent. As in `sitePerfect_dualizable_hom_etale`, take its right dual,
use the derived braiding to obtain a left dual, and apply the closed-category comparison
theorem to the specified map `ihomUnitTensorToIhom`. -/
theorem sitePerfect_dualizable_hom_general
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    (k : Type u) [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [HasInvertibleExponent Λ X]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX]
    (K M : DerivedCategoryModule Λ X)
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (hM : DerivedCategory.boundedConstructibleFiniteTor Λ X M)
    (hPerfect : IsSitePerfect K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  have _ := hK
  have _ := hM
  let := hPerfect.isDualizable.some
  let : BraidedCategory (DerivedCategoryModule Λ X) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  let := BraidedCategory.exactPairing_swap K Kᘁ
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K M

end AlgebraicGeometry.Etale.DerivedCategory
