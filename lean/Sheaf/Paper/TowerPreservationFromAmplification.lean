/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.TowerPreservation
public import Sheaf.Paper.WitnessCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Tower preservation from finite amplification and witness compatibility

This is amplification step (c), after its finite-level and normalization inputs.
Source: blueprint main-20261015, sec-proper-base-change/sk-thm-properbasechange,
`thm-weil-pbc-amplification-proper.proof.md`
(blueprint: lem-weil-pbc-tower-preservation-from-amplification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- On a proper square, finite amplification and compatible normalized witnesses
supply preservation of bounded constructible strict completed-coefficient towers.
Source: blueprint main-20261015, sec-proper-base-change/sk-thm-properbasechange,
thm-weil-pbc-amplification-proper.proof.md, step (c), with the uniform bound and
local-effectivity argument of the node's repaired proof steps 5-6.
(blueprint: lem-weil-pbc-tower-preservation-from-amplification).

Proof: take a uniformly bounded constructible input adic tower. Its supplied common
local complexes have terms in one interval [d0,d1]. The uniform perfect-quotient bound
gives a single r such that all A/I^(n+1) have finite projective resolutions in [-r,0]
over A. The flat constant-to-completed comparison transports this bound to the actual
completed coefficient sheaf, including its restricted version on each covering member.
Tensor the local complexes with these resolutions; all input levels have cohomology
in [d0-r,d1]. Their finite-lisse cohomology is intrinsically constructible. The normalized
local-effectivity theorem therefore gives bounded constructible etale origin at every
level. No finite projective dimension over one of the intermediate quotients is used.

Apply AMP with the supplied bound c. Its direct-image containments give bounded
constructible finite output levels in [d0-r,d1+c], and its pullback containments give
[d0-r,d1]. For direct image choose these quotient-linear output levels. Derived tower
evaluation and the coefficient-restriction/direct-image comparison identify their
scalar restrictions with the evaluations of the actual completed tower direct image.
The quotient projection formula and WIT give their normalizations, transitions and
cocycle, including compatibility with those evaluation identifications.

For pullback take finite pullbacks of the input levels. The objectwise K-flat tower
construction and constant-to-completed comparison identify their restrictions with
evaluations of the actual completed tower pullback: if R is the constant A sheaf,
B is inverse image of the source completed ring, B' is the target completed ring and
S_n is the target quotient, flatness and the finite quotient identities give
B tensor^L_R S_n = S_n and B' tensor^L_R S_n = S_n. Reassociation gives
B' tensor^L_B S_n = S_n. This proves the evaluation comparison for a supplied
quotient-linear level, without identifying the ambient completed and constant module
categories. Naturality gives the transition equation. WIT and tensor balancing give
the normalized reductions and their quotient cocycle.

Apply normalized constructible local effectivity to each of these four output adic
towers with its common interval. Its construction chooses a common finite stratification,
compatible pro-etale trivializations and a bounded finite-type adic-lisse complex on each
covering member. The complexes are truncated in the stated cohomological interval;
only finite module terms, not projective terms, are needed. Their derived reductions
remain the specified output levels with their normalizations. This gives uniform
bounded constructibility and an isomorphism of the output strict tower with the actual
functor value. Finally repeat the same construction for every c' satisfying AMP and
every interval [a,b] of the supplied input levels. AMP gives [a,b+c'] for direct images
and [a,b] for pullbacks; the same local-effectivity construction supplies output models
in those intervals. Thus the already chosen output adic towers satisfy
HasTowerAmplitudeCompatibleModels, and all four preservation clauses hold. -/
theorem towerPreservation_of_amplification_witnesses
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    [IsProper f] [IsProper f'] (c : ℕ)
    (hAmp : Scheme.HasFiniteLevelAmplification sq d c)
    (hWit : WitnessCompatibility sq d) : Scheme.HasTowerPreservation sq d := by
  sorry

end AlgebraicGeometry.ProEtale
