## What changed

In `Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellationAt`, replaced the sole whole-proof
hole by a compiling proof of `AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation_at`.
Two proved private helpers show that a unit-sheaf endomorphism is determined by its value at
1 on the terminal open, and that a nonzero finite-free sheaf map has nonzero matrix.
The proof conjugates the supplied differential by chosen free identifications, cancels the
pulled-back isomorphisms, extracts a nonzero residue coefficient using `freeMatrix_pullback`,
and proves that its original coefficient is a unit using `ΓSpecIso_naturality` and
`IsLocalRing.residue_ne_zero_iff_isUnit`.

Added `Sheaf.AlgebraicGeometry.AffineFreeComplexUnitCancellation`, which isolates the affine
module-to-sheaf splitting and contracting-homotopy argument (original plan steps 3–4).
The assigned proof applies that theorem, defines the complementary sizes explicitly,
transfers zero terms outside the interval along the unchanged-term isomorphisms, and proves
all three rank clauses. Existing theorem signatures and visibility are unchanged.
Updated the item's node proof, proof dependencies and proof origin to match this route.
Both modules compile without warnings using the prescribed launcher.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation_at`
(node `lem-pc-finite-free-stalk-unit-cancellation-at`). No direct hole remains in the item.

Hole added: `AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_unit_cancellation`
(node `lem-pc-affine-free-complex-unit-cancellation`), in its own new module.
It is exactly a named public theorem with whole proof `by sorry`, a source and complete
proof sketch. The remaining work is lifting free-sheaf differentials through the fully
faithful tilde functor, applying the existing algebraic splitting theorem, constructing
the identity-summand contraction and applying the additive tilde functor to the homotopy.

This is a decomposition: one upper hole closed, one lower hole added, net zero direct
holes. The item still transitively depends on the new theorem's hole. The residue
coefficient detection, both support bounds and every exact rank equation are proved.
The new statement contains no scheme stalk, residue morphism, nonzero residue differential,
interval bound, cancellation-degree inequality, or exact rank equations. Those portions
of the original conclusion are established by the assigned proof, rather than handed
to a renamed copy of its original statement.

## No longer needed

Removed the direct proof imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Sheaf.Algebra.Homology.UnitEntrySplits` from the assigned module; the new bridge module
imports them because its remaining proof uses them. Added only the private proof import
`Sheaf.AlgebraicGeometry.AffineFreeComplexUnitCancellation` to the assigned module.

The item's direct proof dependencies `lem-weil-pbc-spec-tilde-free-module` and
`lem-weil-pbc-free-complex-unit-entry-splits` are replaced by the new bridge node.
Both original nodes remain needed below that bridge. No node or module is globally
pruned; no public import is removed and no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The given module and algebraic splitting theorem have compatible mathematical content,
but the algebraic theorem's conclusion supplies differential-compatible direct sums,
not a sheaf-complex homotopy equivalence. No existing declaration found implements
that full affine transfer and contraction. This is the remaining bridge, not an
objection to using stated dependencies with holes.

The local source checkout contains no `literature/stacks-project/algebra.tex`; I read
[Stacks Tag 00MT](https://stacks.math.columbia.edu/tag/00MT) online instead. The lemma
splits a unit coefficient over an arbitrary ring. Its identity summand contracts,
which explains the homotopy-equivalence clause. The bridge preserves the source's
unit-entry route and uses the existing `ChainComplex.exists_splitting_of_isUnit_entry`.

Edge cases: empty pivot sets cannot satisfy the supplied pivot binders; when either
size is one, subtraction yields the zero-size free sheaf. The affine bridge permits
negative cancellation degrees and unbounded complexes. The zero ring causes no false
nonzero-residue claim: the main theorem's nonzero hypothesis excludes it, while the
bridge's algebraic splitting remains valid. For `i=0` and `i=d-1`, both modified terms
stay inside the interval, so the support argument still applies. The unit record
`sk-thm-picard-perfect` has no realized node attachment to bypass.

## New nodes

`lem-pc-affine-free-complex-unit-cancellation`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-free-complex-unit-cancellation.json`, records
`AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_unit_cancellation` in
`Sheaf.AlgebraicGeometry.AffineFreeComplexUnitCancellation`. It groups the algebraic
splitting, contraction and associated-sheaf transfer, without the local/residue or
support arguments. Its proof uses the existing tilde/free comparison and unit-entry
splitting nodes. Its searches were actually run through `msearch.py`; LeanSearch was
unavailable (HTTP Internal Server Error), and Loogle, LeanFinder and grep found no
matching cancellation theorem. No interface changes or change records are needed.

## Second reading by P2

1. I compared both delivered modules with the repository versions. The assigned target declaration's
signature is unchanged byte for byte; the added affine bridge is a new declaration recorded by its
node. Verdict: pass.

2. I compiled both modules with `lcompile.py --all`. There are no errors or warnings, no forbidden
constructs, and the only remaining `sorry` is the named bridge theorem listed above. The target proof
uses no new axiom beyond the permitted open theorem. Verdict: pass.

3. The bridge statement is strictly weaker than the target: it assumes an explicit unit coefficient
and concludes only affine homotopy cancellation and termwise free identifications. It adds no stalk,
residue, support, or rank hypotheses. Its docstring and DAG node give the source and proof route.
Verdict: pass.

4. The proof follows the shortest available route below the unit: it uses the existing affine
unit-entry splitting and tilde/free comparison, then proves residue detection, support, and rank
arithmetic directly. Unused direct imports were removed from the target; the bridge retains the two
imports it needs. Verdict: pass.

5. The target's DAG proof, proof dependencies, and proof origin match the Lean proof, and the unit
route remains attached to `sk-thm-picard-perfect`; no unit step is bypassed. Verdict: pass.

I changed only this report section during second reading. No Lean statements or definitions were
changed, and no additional holes were introduced.
