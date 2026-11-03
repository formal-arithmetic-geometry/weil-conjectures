/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Normalized projective-line adjunction on the intrinsic finite-ctf domain

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, lines 20--35;
`det-sp-et-proet-adjunction-transfer`.
(blueprint: lem-sp-p1-finite-ctf-normalized-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.P1FiniteCtf
open AdjunctionTransfer OrdinaryScalarSite

local instance proEtaleEssentiallySmallNormalized (S : Scheme.{u}) :
    EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _

/-- The ordinary projective-line adjunction transfers to the intrinsic domain with
its specified counit normalization.
Source: latest blueprint, reduction-exceptional proof, Charts, lines 20--35;
finite-site adjunction transfer.
(blueprint: lem-sp-p1-finite-ctf-normalized-adjunction).

Proof: finite type over k and properness of the projective-line projection make S
and P Noetherian. Intrinsic bounded constructibility equals the essential image of
bounded constructible etale complexes; exact faithful comparison preserves and
reflects every Tor interval. Thus exact comparison restricts to finite-ctf
 equivalences on S and P, and every intrinsic object has an etale origin.
The chart-domain theorem preserves the etale domains under proper compact support
and twisted shifted pullback. Identify proper compact support at the trivial
compactification with direct image by its identity-open normalization. Identify
the right operation with ordinaryFiniteP1Right by symmetry and the tensor-shift
comparison. Transfer preservation to the intrinsic domains using these comparisons
and the origins. Restrict the ordinary normalized adjunction and transfer it through
the two equivalences using the proper counit-mate site comparison. Compose the
transported right functor with the natural isomorphism rightSite and the comparison
equivalence's counit. Its component at an etale origin is the given rightSite:
the quasi-inverse unit and counit cancel by the triangle identity. The formula for
ofNatIsoRight_counit then gives exactly counit_normalization. Package these
preservation results, origins and the transported adjunction as NormalizedAdjunction.
All objects are obtained from the actual functors and their unique adjoint comparisons;
no arbitrary object is selected from a mere existence assertion. -/
theorem p1FiniteCtfNormalizedAdjunction
    (ℓ n : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    (R : Type (u + 1)) [CommRing R] [Finite R] (hR : ((ℓ ^ n : ℕ) : R) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [IsNoetherian S]
    (hN : 0 < ℓ ^ n) (hS : IsUnit ((ℓ ^ n : ℕ) : Γ(S, ⊤))) :
    Nonempty (NormalizedAdjunction R (ℓ ^ n) hN hR S hS) := by sorry

end AlgebraicGeometry.ProEtale.P1FiniteCtf
