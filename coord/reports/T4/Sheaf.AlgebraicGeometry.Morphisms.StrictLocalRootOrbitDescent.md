## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.strict_local_root_orbit_descent`
without changing its signature. The proof constructs the ring map from the
R-root algebra to the H-root algebra by `AdjoinRoot.lift`, restricts its spectrum
to the two principal opens, and proves its equation over R. It also proves the
rotation identity/composition laws by checking the root, finite faithful flatness
from the monic relation, and nonvanishing of the divisor in the root algebra.
It then combines two independent new lemmas: strict-local root torsor properties,
and orbit descent for an arbitrary finite faithfully flat domain algebra with a
finite group action and an etale torsor puncture. The latter allows any splitting
scheme T receiving a map from the puncture, so no root-algebra base-change
isomorphism or transported arbitrary algebra data is needed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.strict_local_root_orbit_descent`
(node `lem-sbc-strict-local-root-orbit-descent`). No sorry remains in the item.

Added exactly two named public holes, each in its own new module:

- `AlgebraicGeometry.Scheme.strict_local_root_torsor_properties`
  (`lem-sbc-strict-local-root-torsor-properties`). This asserts only properties of
  the explicit root algebra; it has no cover Y, no splitting, and no stabilizers.
- `AlgebraicGeometry.Scheme.affine_torsor_fixed_puncture_descent`
  (`lem-sbc-affine-torsor-fixed-puncture-descent`). This is generic torsor descent;
  it has no regularity, strict henselianity, root polynomial, or root exponent.
  The action and its fibrewise simple transitivity are hypotheses, supplied by
  the first lemma and the proved rotation laws in this delivery.

This is a decomposition, not a sorry-free proof: one hole closed, two added,
net -1 before any other target-closure effects. The combination and all glue
in the original module are proved Lean. No axiom, data definition, arbitrary
witness choice in a definition, or target signature was added or changed.

## No longer needed

All original public imports are retained, preserving the public interface.
Removed the direct proof import `Sheaf.RingTheory.RootAlgebraRegularAtRoot` from
the item and retained it in `StrictLocalRootTorsorProperties`, where regularity
is needed. Its node is therefore still needed transitively, and is not pruned.
No existing proof-dependency node or module is claimed globally pruned.
Theorem `strict_local_root_invariants` is not used: only that module's actual
rotation and fixed-subalgebra definitions are used. No intermediate-root
identification, root-algebra base-change isomorphism, cyclicity/order computation
for the group, or strict henselianity of the root algebra is required by the
generic descent interface.

## Where the brief, the DAG or earlier work was wrong

The old node had no Lean declarations for its torsor and orbit-descent steps
(steps 2 and 3 had empty `uses`, despite being non-elementary). Those steps are
now explicit independent interfaces. The original statement is retained.
The unit `sk-prop-input-spreading` is retained, including its trait/root-cover
route; no unit statement or realization is bypassed.
The closed regular-local-domain node is used as a generic ring-theoretic tool.

Checked edge cases mathematically before stating the new lemmas: n=1 gives
C=H and the identity action; h=0 and h a unit are excluded by the original
hypotheses; d=0 yields no orbits and the zero product ring/empty spectrum;
the trivial group makes the generic torsor an isomorphism. In the general
lemma h need not be a parameter or lie in a maximal ideal: the explicitly
assumed domain, nonzero image, finite faithful flatness, etaleness and unique
rotations are exactly what the descent proof uses. Field maps are compared
only when they agree on H and the divisor has nonzero image. These checks do
not rely on a quotient of a non-domain or on inverting a zero divisor.

Searches: LeanFinder, Loogle and source/Mathlib ripgrep found ingredients
(KummerTorsor, finite-etale Galois quotients, monic root algebras) but neither
new statement. LeanSearch returned Internal Server Error and is recorded as
unavailable. Blueprint searches for root torsors, root algebras, Galois
quotients, and Tags 0EYG/03SF found no duplicate blueprint node. Each new node
carries the nearest blueprint ancestor of the item. The sources read were
Stacks Tags 0EYG, 09EV and 03SF.

## New nodes

`lem-sbc-strict-local-root-torsor-properties`, module
`Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorProperties`: the domain,
etaleness and unique-rotation assertions needed before any descent; it retains
the existing root-regularity and regular-local-domain inputs.

`lem-sbc-affine-torsor-fixed-puncture-descent`, module
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent`: general finite
etale orbit descent and invariant-localization identification. Its proof in
words describes the torsor recognition, permutation action, stabilizers,
fixed fractions, and finite product of punctures. Existing Galois-category
tools are recorded as proof dependencies. No change record is needed because
no existing statement, definition or visibility was changed.

## Second reading by T4

1. **Statements and interfaces.** Compared the delivered orbit-descent module with the repository version. The existing target signature is byte-for-byte unchanged. The two added theorem signatures are independent reductions: the first isolates strict-local root-torsor properties, and the second isolates generic affine torsor descent. Neither weakens the target or adds a hypothesis to an existing declaration. Verdict: pass.

2. **Proof and trust basis.** Compiled all three sandbox modules with `lcompile.py --all`; they compile cleanly. The target has no `sorry`, while the two intentionally split-off theorem declarations retain their named `sorry`s and matching DAG nodes. No definitions contain `sorry`; no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations were added. The target's proof uses only ordinary Lean constructions and the two split interfaces; its remaining axiom dependency is therefore exactly the documented `sorryAx` of those interfaces. Verdict: pass.

3. **Truth and reuse of split statements.** Checked the edge cases recorded above (unit exponent, empty splitting, trivial group, and excluded zero/unit divisor cases). The root-torsor statement is restricted to the explicit AdjoinRoot and its puncture; the generic descent statement assumes exactly the domain, finite faithfully-flat, etale, and unique-rotation data used by its stated route. Source and local searches found no duplicate declarations. Verdict: pass, with the two holes correctly recorded as a decomposition.

4. **Pruning and imports.** The direct `RootAlgebraRegularAtRoot` import was removed from the target and retained in the root-torsor interface where its proof obligation belongs. The remaining plain regular-local definitions import is necessary for the domain and finite-roots instances used by the target proof. No existing proof-dependency node is incorrectly claimed pruned, and the unit route remains the root-cover/torsor route. Verdict: pass.

5. **DAG and report consistency.** Compared the three node records with the declarations and their documented proof routes. The target node records both new interfaces and the regular-local-domain dependency; the new nodes contain source, proof text, statement dependencies, and module/declaration paths. The report lists the closed target hole, the two added holes, and the intended decomposition. Verdict: pass.

Changed during second reading: restored the necessary plain regular-local definitions import after a compile test showed that removing it loses the regular-local-domain and finite-roots instances; added this review section. No theorem statements or proofs required repair.
