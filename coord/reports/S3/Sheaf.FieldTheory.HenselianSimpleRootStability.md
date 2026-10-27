## What changed

Replaced the proof of `AddValuation.exists_open_coefficients_simple_root` in
`Sheaf.FieldTheory.HenselianSimpleRootStability`, preserving its signature and all
public imports. The discrete case uses the singleton coefficient neighbourhood.
The nondiscrete case is reduced to integral normalization, followed by a proved
algebraic root-lifting lemma and explicit evaluation and differentiation of
`g(a+sX)=tH(X)`.

Added `Sheaf.RingTheory.HenselianResidueXRoot`, proving
`HenselianLocalRing.exists_simple_root_of_map_eq_X` for an arbitrary henselian
commutative local ring, without a domain or monicity assumption. The proof makes
`H(1-X)` monic by coefficient reflection and the inverse unit `H(1)`, uses
Mathlib's monic residue-root lifting, and returns along the inverse unit. Choosing
the reflection length `H.natDegree+1` avoids any assertion that reduction preserves
the degree. The reduced monic polynomial is `X^(m+1)-X^m`, with derivative one at
one, including positive characteristic.

Added `Sheaf.FieldTheory.SimpleRootPerturbationNormalization`, stating exactly
the finite valuation estimates and integral normalization from the original
node's steps 1--3. This is the remaining split theorem: it assumes no
henselianity, supplies no perturbed root, and has a complete proof in words in
its docstring and node. Updated the item's proof route and added both nodes.
No existing module besides the item, shared definition, target statement or
unit route was changed.

## Proved and sorry left

Closed the item's one original hole:
`AddValuation.exists_open_coefficients_simple_root`
(`lem-per-henselian-simple-root-stability`). Its proof is complete from the
normalization statement and the proved algebraic helper.

Proved without sorry:
`HenselianLocalRing.exists_simple_root_of_map_eq_X`
(`lem-per-henselian-residue-X-root`). It uses Mathlib's
`HenselianLocalRing.TFAE` and polynomial reflection, not a project theorem
containing sorry.

Added one hole, the only sorry in this delivery:
`AddValuation.exists_open_coefficients_residue_X`
(`lem-per-simple-root-perturbation-normalization`). The remaining work is choosing
finite valuation bounds, proving the coefficient neighbourhood open, and
constructing the integral normalized polynomial. The henselian root construction
and transfer back to the original polynomial are already formalized.

This is a decomposition: one existing hole closed, one lower hole added, net
zero holes removed. The new normalization statement is strictly a part of the
argument; in particular it cannot supply any perturbed root by itself. The
algebraic helper is fully proved and has no topological or valuation hypotheses.

## No longer needed

Removed the private proof import
`WeilConjectures.RingTheory.HenselianLocalRootLifting`. The item's original sole
proof dependency `lem-weil-pbc-henselian-local-root-lifting`, declaration
`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`, is not used:
Mathlib's `HenselianLocalRing.TFAE` already supplies the monic residue-root
lifting implication needed here. The equivalence with idempotent lifting is
unnecessary for this proof. This records local dependency pruning, not withdrawal
of that module, which other consumers may still need.

All four original public imports remain necessary for the statement's polynomial,
valuation-subring, product-topology and henselian interfaces. Both added private
imports are used. No other declared dependency, module or node was pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original five-step plan required substantial
valuation and reciprocal-polynomial glue that was not present in its one stated
proof dependency. The reciprocal part is now proved, and the valuation part is a
separate, explicitly stated task. The original proof used the full project
idempotent/root-lifting equivalence where Mathlib's monic Hensel interface
suffices.

Checked the edge cases of the new statements. Integral normalization needs
nondiscreteness because ambient value balls need not contain nonzero elements
in the discrete case; that case is handled before normalization. The estimates
use only finitely many bounds, not powers cofinal in the value group. Zero Taylor
coefficients and binomial coefficients impose no bounds, and `E_n=0` covers
`n=1`. The algebraic lemma works with nilpotents as well as domains: cancellation
is only by units, and its derivative computation uses `m+1-m=1`, valid in every
characteristic. The affine transfer uses nonzero `t` and the image of a unit to
prove simplicity, with no unjustified domain cancellation in the valuation ring.

Searches by LeanSearch, LeanFinder/Loogle and source grep are recorded in each
new node. Read Mathlib's `RingTheory/Henselian.lean`, polynomial `Reverse.lean`,
`Derivative.lean` and evaluation interfaces. The root-scaling and integral
normalization search hits do not assert the valuation estimate; the existing
monic Hensel theorem is used rather than restated. Read the current blueprint
unit record and latest unit text; neither the assigned node nor either new
helper realizes a unit's own statement or mandatory step, and that route is
preserved.

## New nodes

`lem-per-henselian-residue-X-root`, in
`dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-residue-X-root.json`, attaches
the fully proved local-ring lemma to
`Sheaf.RingTheory.HenselianResidueXRoot`. It is the original reciprocal/Hensel
step, generalized to arbitrary commutative henselian local rings, with no new
hole.

`lem-per-simple-root-perturbation-normalization`, in
`dag/nodes/sec-deligne-laumon-a1/lem-per-simple-root-perturbation-normalization.json`,
attaches the valuation estimate to
`Sheaf.FieldTheory.SimpleRootPerturbationNormalization`. It is the original
steps 1--3 and asserts only normalized coefficients and a neighbourhood
inclusion. Both nodes have the item's chapter and unit and preserve its blueprint
ancestor through the item. No change record is required: all existing signatures
and public imports are unchanged and the only other modules are new.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
