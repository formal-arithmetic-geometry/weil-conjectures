## What changed

Completed `AlgebraicGeometry.ProEtale.constant_square_zero_tor_example` in
`Sheaf.Paper.ConstantSquareZeroTorExample`, preserving its signature and public imports.
All new helpers are private and proved. The periodic resolution and its derived
self-tensor are constructed directly in the internal module category. A double complex
in degrees -1 and 0 supplies the finite-free example, with its kernel/cokernel homology
and its upper truncation computed explicitly. Updated the existing node's proof route
and dependencies to describe these constructions.

The proof-context change record is
`coord/changes/E3-square-zero-internal-proof-context.md`. It records the added commands
flagged by server preflight, the unchanged public signature, and all downstream users.
The only external textual consumer, `LocalizingClosureCtfEqualsBc`, was checked at
each of its three applications; its conclusions and hypotheses are unchanged.

The finite-discrete normalized encoding is used only for its proved canonical abelian
coefficient isomorphism, through a private proof import. The abstract coefficient
isomorphism in the statement is handled on the underlying abelian sheaf before the
internal exactness calculation. Finite presentation, singleton covers, pullback of
constant models, and the trivial stratification prove constructibility.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.ProEtale.constant_square_zero_tor_example`
(node `lem-sfb-constant-square-zero-tor-example`). Added zero holes; no `sorry` remains
in the delivered Lean module. No intermediate public theorem, axiom, or definition
with postponed data is introduced. The existing foundational dependencies of the
internal derived tensor remain the library's shared dependencies.

Source and edge checks: the blueprint's Examples paragraph supplies the periodic
resolution and the two-term finite-free complex. The arithmetic proof uses only
primality and positivity, includes ell = 2, and imposes no relation between ell and
the characteristic of k. The geometric argument uses only nonemptiness of Spec k.
Generic internal lemmas explicitly assume exactness and nonzero unit; they therefore
do not assert a false nonvanishing result for the zero ring or the empty scheme.

## No longer needed

The statement's three public imports are preserved. Compared with the old node plan,
this proof does not use:

- `lem-sfb-square-zero-periodic-tensor` / `Sheaf.Paper.SquareZeroPeriodicTensor`:
  the internal chain complex, its K-flatness and the termwise self-tensor calculation
  are constructed directly, so no intrinsic/fixed derived-category transfer is needed.
- `lem-weil-pbc-finite-discrete-condensed-ring-constant` /
  `Sheaf.Paper.FiniteDiscreteCondensedRing` and
  `lem-weil-pbc-finite-discrete-scheme-ring-constant` /
  `Sheaf.Paper.FiniteDiscreteSchemeRing` as separate proof steps:
  the already normalized canonical abelian coefficient comparison suffices. The latter
  module is still a transitive dependency of the normalized encoding and is not withdrawn.
- `det-def-sfb-constructible-local-model` /
  `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: the actual condensed 1 by 1
  cokernel presentation directly meets `HasFiniteConstantLocalModel`; no scalar-matrix
  equivalence is invoked.
- `lem-sfb-condensed-coefficient-iso-constructible` /
  `Sheaf.Paper.CondensedCoefficientIsoConstructible`: transport the underlying unit
  before constructing the internal resolution; no derived coefficient equivalence
  is invoked.

The proof keeps `lem-sf-derived-concentrated-single` and uses the existing generic
source bounded-flat K-flat and tensor-single comparison declarations. New proof tools
are `lem-sf-finite-discrete-normalized-encoding` and
`new-unbounded-pullback-finite-constant-local-model`; both are already proved.
The unit `sk-def-localizing-closure` has empty realized statement/steps, so no fixed
unit route is bypassed. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original route needlessly passed from the intrinsic constant-ring sheaf tensor
calculation to the internal tensor and then used a derived coefficient equivalence.
The underlying abelian comparison transfers the two elementary properties needed
for a direct internal proof: square-zero and exactness. Nonzero constant sections
and cokernel cancellation give the requisite nonzero residue without identifying
an intrinsic quotient module. The theorem itself was not changed.

Validation: the complete module compiled without errors or warnings through
`lcompile.py` in 23.1 seconds. The resumed draft required explicit preservation of
finite limits for point inverse image, the nonempty prime spectrum of k, and classical
selection of the single-degree isomorphism. All selected objects are determined up to
the isomorphism used in the proof; no arbitrary existence supplies coefficient data.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
