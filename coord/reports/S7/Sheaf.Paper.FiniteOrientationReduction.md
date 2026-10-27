## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.finite_orientation_reduction`
with a specialization of the proved generic finite-ring comparison
`AlgebraicGeometry.Etale.FiniteSmoothPurity.normalizedOrientation_scalar`.
Its signature, every existing definition and all public imports are unchanged.
The actual quotient supplies the coefficient map; primality supplies positive
exponents, `m ≤ n` supplies divisibility, and `finiteGeneralRingPrimeSetting`
supplies invertibility on the schemes. The supplied orientations and Tate
comparison are passed unchanged.

The generic theorem has its complete combining proof in the new module
`Sheaf.Paper.FiniteNormalizedOrientationScalar`. It unpacks the normalization
equations and cancels the invertible bundle and normal-section factors to write
each orientation as diagonal factor followed by integrated specialization.
It pastes the two coefficient squares and cancels the orientations to obtain
the inverse equation. The ring map supplies target annihilation at the common
larger exponent. No invertibility of the exceptional coefficient mate is assumed.

Two new modules isolate the remaining mathematical steps:
`Sheaf.Paper.FiniteSmoothDiagonalScalar` concerns only the diagonal exceptional
base-change factor; `Sheaf.Paper.FiniteSectionIntegratedScalar` concerns closed-section
specialization and normal-bundle integration, without a diagonal or supplied
orientation. Each has one public theorem, its source, complete proof in words,
and a DAG node. Neither remaining statement repackages the orientation equation.
The generic combining theorem adds no hole.

The proof was first checked inside the assigned module, where the server accepted
its mathematics but measured 75–78 seconds. Profiling found expensive concrete
quotient checking and exported indexing. Local unfolding restrictions caused
instance mismatches. The generic argument is therefore in its own module, with
coefficient structures as parameters, and `quotientCoefficientCommRing` caches the
existing lifted quotient-ring structure for the concrete specialization. Either
change alone still exceeded 60 seconds; together they passed at 38.6 seconds with
diagnostics present. No check or index is disabled. The cache is direct structure
synthesis and is registered only locally around `finite_orientation_reduction`;
it changes no coefficient operation or existing statement text. Existing definition
bodies, attributes and global instances are unchanged. The record is
`coord/changes/finite-quotient-orientation-ring-cache.md`. Both direct importers
are compiled against the final cache; unchanged copies are removed before delivery.

Validation: all four delivery modules compiled through `lcompile.py`. The final
non-diagnostic assigned module and both direct importers,
`ProEtaleCtfPullbackDomains` and `CompositeProjectionCoefficients`, also compiled
cleanly against the cache. No consumer adaptation was needed; the unchanged
validation copies have been removed. Every file passed the per-file limit.

## Proved and sorry left

Original module: two holes on entry. One upper hole is closed by decomposition:
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.finite_orientation_reduction`
(node `lem-sp-finite-orientation-reduction`). Its specialization and the generic
combining proof contain no `sorry`. This is a decomposition, not a net proof gain.

The original hole left unchanged is
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.uniformizer_orientation_agreement`
(node `lem-sp-finite-orientation-reduction`).

Two holes are added, each in its own new module:

- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothDiagonalScalar`
  (node `lem-sp-finite-smooth-diagonal-scalar`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.integratedSpecialization_scalar`
  (node `lem-sp-finite-section-integrated-scalar`).

The proved generic theorem is
`AlgebraicGeometry.Etale.FiniteSmoothPurity.normalizedOrientation_scalar`
(node `lem-sp-finite-normalized-orientation-scalar`). It uses those two strictly
smaller factor statements through a real factorization, pasting and cancellation
proof. Thus one existing hole is closed and two are added, leaving three direct
holes across the delivered Lean files. All other existing proofs are preserved.

## No longer needed

No pre-existing Lean imports were removed and no modules were withdrawn.
The assigned module now privately imports only
`Sheaf.Paper.FiniteNormalizedOrientationScalar` for its new proof; that module
privately imports the two factor modules. All are used in the proof closure.
The fifth proof step no longer directly invokes `det-sp-scalar-extension-functor`;
its normalized Tate comparison remains in the statement and is used below by the
section-square node. It is consequently removed only from the item's direct
`proof_deps`, not pruned from the library. Other recorded dependencies remain
needed by the companion statements, unchanged uniformizer hole, or existing unit
and tower proofs. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old fifth proof step has an interface gap: `reductionOrientation` and
`reductionCompatibilities_purity` use one exponent on both coefficient rings.
This item's target line uses `l^(m+1)` while its source uses `l^(n+1)`.
Neither declaration directly proves the equation with the supplied comparison `t`.
The normalization equations instead allow the diagonal and integrated-section
factor squares to be pasted, with divisibility of the two exponents explicit.

Mathlib and adopted-source searches found no direct theorem. Project search found
`diagonalBaseChangeReduction`, but it concerns a uniformizer-setting pro-etale
presentation and separately named comparisons. `integratedSpecialization_baseChange`
changes the geometric base with fixed coefficients; the new section theorem changes
coefficients on a fixed pair. The generic combining statement also permits arbitrary
finite rings and two exponents, unlike the existing single-exponent or prime-ring
reduction statements. None of these existing statements is duplicated.

The new statements were checked at equal exponents, dimension zero, empty schemes,
and the zero coefficient ring. Positivity and `M ∣ N` make the specified root power
the Kummer transition. The generator and derived-normalization fields of `t`
exclude an arbitrary line comparison. All scalar products are derived, including
ramified non-flat quotients. The blueprint's diagonal, deformation and integration
route is retained.

## New nodes

`lem-sp-finite-smooth-diagonal-scalar`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-smooth-diagonal-scalar.json`, states the
scalar square for the diagonal factor alone. Its proof uses the exceptional mixed
square at the unit and scalar section-compositor coherence, from existing nodes
`lem-pur-section-scalar-base-change` and `lem-pur-scalar-section-compositor`.

`lem-sp-finite-section-integrated-scalar`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-section-integrated-scalar.json`, states
coefficient compatibility of integrated specialization of a closed smooth section.
Its proof follows the normalized Rees-family square, the normal-bundle comparison
and the Kummer-normalized integration square. Generic finite-ring family constancy,
section scalar base change, shifted-line rigidity, vector scalar trace and integration
transpose supply its constituent theory. The prime-ring DNC transport statement
is not applied outside its hypotheses.

`lem-sp-finite-normalized-orientation-scalar`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-normalized-orientation-scalar.json`, is
proved by factoring normalized orientations and pasting the preceding two squares.
It is a generic finite-ring theorem and has no `sorry` in its proof. Moving this
self-contained argument to its own module follows profiling and local simplifications;
it adds no mathematical hole.
The assigned theorem specializes it to the actual ell-power quotient.

All three nodes inherit the item's chapter, unit and nearest blueprint ancestor
`det-sp-integral-adjunction-bijection` and record actual semantic/source searches.
Full-blueprint searches found no separate matching factor statements. The direct
quotient-ring structure cache is recorded in
`coord/changes/finite-quotient-orientation-ring-cache.md`; the dictionary is
definitionally unchanged and its registration is local.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
