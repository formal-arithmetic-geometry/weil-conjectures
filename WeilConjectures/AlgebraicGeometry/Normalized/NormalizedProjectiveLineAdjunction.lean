/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTateLineComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteP1AdjunctionOfIntegrals

/-! # The projective-line adjunction for a normalized twist datum

The projective-line geometric input to the affine-space induction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Projective-line direct image is left adjoint to normalized twisted pullback.
Source: blueprint sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the diagonal-kernel construction and its two triangles.
(blueprint: lem-normalized-projective-line-adjunction).

Proof in words: extract the normalized Kummer datum underlying the given twist.
Its hyperplane class gives the projective-line decomposition and its trace.
On P times_S P the supported diagonal class has trace one along both projections.
For an arbitrary complex M define the unit by the diagonal class tensored with
p1^*M, followed by proper base change. Define the counit by inverse projection
formula followed by tensoring with the trace. For the first triangle, proper base
change and direct-image composition identify the composite with Rq_* applied to
M tensored with the first diagonal integral, hence the identity. For the second
triangle, pull the common coefficient q^*K outside the second projection: the
composite is the identity on q^*K(1)[2] tensored with the second diagonal integral,
again the identity. All shifts are even. The maps are natural and the triangle
identities give the adjunction on the entire unbounded categories. The arbitrary
base assertion uses a positive annihilator n and the universal base Spec Z[1/n].
The given Tate line pulls back from that base by its pullback isomorphisms.
Over Q, the normalized zero-section boundary and the rank-one local cohomology
calculation identify it with the finite root-of-unity line tensored with Lambda.
Both are locally constant finite rank-one sheaves on the normal connected base
Spec Z[1/n]. Its generic-point fundamental group surjects onto its fundamental
group: every connected finite etale cover stays connected at the generic point.
Thus the generic identification descends uniquely as a module-sheaf map and is
an isomorphism; pull it back to S. The case n=1 is the zero coefficient ring.
Transport the concrete trace and diagonal class along this identification;
proper exchange and projection commute with that transport. The trace and
supported class commute with base change, so their two integral identities
hold over every S. No definitional equality of twist models is assumed. -/
theorem nonempty_normalizedProjectiveLineAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
      L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) := by
  obtain ⟨N, hN, hΛ, hS⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  let P := ℙ(Option (ULift.{u} (Fin 1)); S)
  have : HasInvertibleExponent Λ P := .of_hom (P ↘ S)
  have hP : IsUnit (N : Γ(P, ⊤)) := by
    simpa using hS.map (P ↘ S).appTop.hom
  obtain ⟨e⟩ := nonempty_normalizedTateLineComparison Λ N hN hΛ P hP
  obtain ⟨t, d, hbc, hi⟩ := exists_arbitraryBaseFiniteP1Integrals N hN Λ hΛ
  obtain ⟨a⟩ := nonempty_finiteP1AdjunctionOfIntegrals Λ N hN hΛ t d hbc hi S hS
  exact ⟨a.ofNatIsoRight (Functor.isoWhiskerLeft _
    (Functor.isoWhiskerRight
      ((derivedTensor (ModuleCat.{u + 1} Λ) P).flip.mapIso e.symm)
      (shiftFunctor _ (2 : ℤ))))⟩

end AlgebraicGeometry.Etale
