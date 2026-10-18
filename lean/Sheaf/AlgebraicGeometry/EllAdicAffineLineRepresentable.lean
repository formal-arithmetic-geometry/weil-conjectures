/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Bounded constructible affine-line duality -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) [IsFinitenessCoefficient ℓ Λ]

include ℓ hΛ in
/-- The affine-line compact-support adjunction on bounded constructible complexes.

Source: blueprint `sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md` (1)--(3)
and `sk-cor-affine-space-rational/sk-cor-affine-space-rational-induction.proof.md`.

Proof: the right adjoint is the actual smooth formula `p*(-)(1)[2]`.
Here is the trace argument producing its natural Hom equivalences.

First work over an arbitrary separated finite-type base `T`, with projective-line projection
`q : Q = P1_T → T`. Put `W = Q ×_T Q`, with projections `r1,r2` and diagonal `Delta`.
Let `TQ` and `TW` be the Tate lines shifted by two. The integral diagonal class is
`delta : Delta_* R_Q → TW`, and the trace is `tq : Rq_* TQ → R_T`. Proper base change
identifies `q* Rq_*` with `Rr2_* r1*`. Projection formula for the diagonal identifies
`a_M : r1* M tensor Delta_* R_Q ≅ Delta_* M`. Apply `Rr2_*` to
`a_M.inv` followed by `1 tensor delta`. The identities `r2 Delta = id` and proper base
change followed by projection formula identify its source with `M` and its target with
`G Rq_* M`, where `G = q*(-)(1)[2]`. This defines the unit `eta_M`.
Projection formula followed by `1 tensor tq` defines the counit
`epsilon_K : Rq_* G K → K`. Both maps are natural.

The first triangle composite is `Rq_* (1_M tensor (tr_r1 Rr1_* delta))`: move the
projection comparison across base change, then use its naturality for `delta` and the
section identity for `r1 Delta = id`. The trace/diagonal normalization says the parenthesized
map is the identity, so this composite is the identity. For the second triangle use
`r2 Delta = id` and `r1* G K = r2* G K` on `W`; the same calculation gives
`1_GK tensor (tr_r2 Rr2_* delta) = id`. All shifts are even, so the interchange sign is one.
Consequently the maps `h ↦ G(h) eta_M` and `a ↦ epsilon_K Rq_*(a)` are inverse Hom maps:
naturality and the respective triangle identity compute their two composites. This proves
`Rq_*` is left adjoint to `G`, without assuming an exceptional adjoint.

For the standard affine chart `j : A1_T → Q`, compose this Hom equivalence with the
exact open adjunction `Dj! ⊣ Dj*`. Pullback composition and Cartesian Tate lines identify
`j* q* K(1)[2]` with the affine-line formula. Compactification independence compares the
chosen affine-line compact support with `Dj!` followed by `Rq_*`. The comparison is available
for all three coefficient certificates in the compact-support composition module.

Exact pullback preserves bounded constructibility. The Tate line is pro-etale locally free
of rank one; tensoring with it is an exact equivalence, with inverse the opposite twist.
On every constructible stratum refine a trivializing cover by one trivializing the line;
the local finitely presented model is unchanged. A shift only reindexes the finite range of
nonzero homology. Thus the right adjoint preserves bounded constructibility. The integral
trace and diagonal permit torsion. For finite rational extensions the same trace calculation is
obtained by scalar
extension, and for the algebraic closure by compatible finite-subextension realization, as in
the rational induction source. These are Hom calculations in the ordinary module-object
derived category; no derived completion is taken. Restrict the resulting natural Hom maps to
bounded constructible tests. The two naturality laws give an adjunction of the bounded
constructible restrictions, hence the asserted `IsLeftAdjoint` certificate.
(blueprint: lem-sfb-adic-affine-line-adjunction) -/
theorem affineLine_compactSupport_isLeftAdjoint
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    let A : Over (Spec (.of k)) :=
      Over.mk ((𝔸(PUnit.{u + 1}; T.left) ↘ T.left) ≫ T.hom)
    let p : A ⟶ T := Over.homMk (𝔸(PUnit.{u + 1}; T.left) ↘ T.left) rfl
    letI : LocallyOfFiniteType A.hom :=
      inferInstanceAs (LocallyOfFiniteType ((𝔸(PUnit.{u + 1}; T.left) ↘ T.left) ≫ T.hom))
    letI : QuasiCompact A.hom :=
      inferInstanceAs (QuasiCompact ((𝔸(PUnit.{u + 1}; T.left) ↘ T.left) ≫ T.hom))
    letI : IsSeparated A.hom :=
      inferInstanceAs (IsSeparated ((𝔸(PUnit.{u + 1}; T.left) ↘ T.left) ≫ T.hom))
    (boundedConstructibleLowerShriek Λ ℓ p).IsLeftAdjoint := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
