## What changed

Replaced the sole sorry of `Sheaf.AlgebraicGeometry.CompletionFromRestriction` by a
complete Lean proof from the single-immersion quotient comparison. Constructed the
termwise isomorphisms explicitly, proved the adjacent transition equation using a
private generic categorical lemma, obtained every transition by induction, proved
naturality by canceling quotient projections, and lifted the resulting natural
isomorphism through the full coherent formal subcategory. Existing signatures and
visibility are unchanged. Added a proof-only import of ClosedImmersionPowerQuotient.
Updated the parent node's proof route and added the new single-immersion node.

## Proved and sorry left

Closed: `AlgebraicGeometry.completion_from_restriction` (1 original hole).
Proved private helpers: `AlgebraicGeometry.restriction_transition` and
`AlgebraicGeometry.quotient_comparison_naturality`.
Added and left: `AlgebraicGeometry.closedImmersion_power_quotient`, node
`lem-weil-pbc-closed-immersion-power-quotient` (1 new hole).
This is a decomposition, with net holes closed minus added equal to zero, rather
than a sorry-free proof of the target closure. The remaining theorem handles just
one closed immersion and one module; it contains no tower, R, Phi, beta, transition
compatibility, naturality, or coherent formal category construction. Its quotient
normalization determines the isomorphism uniquely, because the projection is epi.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`
from the item. Its node `lem-weil-pbc-closed-immersion-unit-quotient` remains needed
below the new quotient bridge, so this is not a pruning of its transitive closure.
No modules are removed from the target closure. No unit statement or realized unit
step is bypassed. The second projection equation hi₂ is retained verbatim but is
not needed for this assembly, once the supplied normalized comparison data hold.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or signature change. The first plan step did not yet provide
an interface comparing the recursively realized ideal power with the power of
IdealSheafData and preserving the unit for an arbitrary supplied adjunction. The
new bridge isolates precisely this missing calculation. The existing affine
ideal-times-module theorem and closed-immersion unit quotient theorem remain the
planned inputs for its proof. The unit record sk-thm-p1 is unchanged.

Local compilation uses only lcompile.py. Both modules compile without warnings.
The delivery dry run passed its compilation, axiom probe, and preflight; nothing
was pushed. The second reading is reserved for the independent second reader.
Checked the bridge on n=0 (unit ideal and empty closed subscheme), J=0 at positive
levels (restriction is an isomorphism), the unit ideal, and F=0. These yield the
expected zero or identity quotients. LeanSearch was unavailable and is recorded
as unavailable. LeanFinder, Loogle, source grep, and blueprint searches ran.
The Stacks text was read at [087T](https://stacks.math.columbia.edu/tag/087T),
[088F](https://stacks.math.columbia.edu/tag/088F), and
[0880](https://stacks.math.columbia.edu/tag/0880); the corresponding local literature
file is absent on this machine.

## New nodes

`lem-weil-pbc-closed-immersion-power-quotient`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionPowerQuotient`: the normalized quotient
comparison for a single closed immersion with kernel an ideal power. It is strictly
the first step of the parent argument and has its own source, proof in words,
search records, and edge-case checks. There are no change records: no existing
interface, statement, or definition changed.

## Second reading by V3

1. I compared the delivered item module with the repository version. Existing declaration signatures and visibility are unchanged; the only interface addition is the separately stated split-off theorem and its node.
2. I compiled both delivered modules with `lcompile.py`; they compile without errors or warnings. The only remaining `sorry` is the named theorem `AlgebraicGeometry.closedImmersion_power_quotient`, with its matching node.
3. The split-off statement is the one-immersion, one-module quotient comparison. It is strictly simpler than the parent target, has the stated Stacks source, and was checked on zero powers, zero ideals, unit ideals, and zero modules.
4. The proof uses the supplied quotient comparison exactly to build the termwise maps, then proves transitions and naturality by cancellation. The proof dependency import was changed to the split-off module, and no unused import remains. The unit route and its realized steps are retained.
5. The delivered DAG proof and `proof_deps` match the Lean proof: the parent uses the new quotient node, while the new node records its lower dependencies.

I changed only the report after the first reading: this section records the independent checks above. No Lean code, signatures, definitions, or DAG statements were altered during second reading.
