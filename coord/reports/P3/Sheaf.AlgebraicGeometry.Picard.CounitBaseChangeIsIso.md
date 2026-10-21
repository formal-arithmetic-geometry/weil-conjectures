## What changed

Repaired the returned no-op delivery at 405ac4e03c against the current source.
The previous restoration is already present, so repeating it would add nothing.
The item's sole actual DAG parent no longer uses the generic derived comparison:
its adopted ZeroScheme proof proves invertibility of the ordinary mate by
checking that it is nonzero on every residue-field fibre. Reconciled that parent
node with the actual complete argument, and withdrew the now redundant item as
required by step 8d. Its mathematical DAG statement remains; its Lean attachment
and retired proof dependencies are cleared. deleted.txt records the withdrawal.

Attached the two existing source results used in the replacement argument as
DAG nodes, with complete proofs in words and searches. They are already proved
in InvertibleFibre.lean and Picard/CounitBaseChange.lean. No new Lean declaration,
module, hypothesis, definition, or theorem signature is introduced.

A scratch module importing the published ZeroScheme implementation compiled in
9.3 seconds. Its axiom checks for the parent theorem and both helper declarations
show exactly propext, Classical.choice and Quot.sound, without sorryAx. This
verifies that the existing replacement proof is complete through its entire
dependency closure. Every adopted source declaration, attribute, signature,
public import and non-theorem body remains unchanged. Change record:
coord/changes/P3-counit-base-change-is-iso-pruning.md.

## Proved and sorry left

The live item initially had 0 holes. This delivery closes 0 holes, adds 0 holes,
and splits off 0 holes. No sorry is left or added by this packet.
The retired declaration is
AlgebraicGeometry.Scheme.Modules.isIso_counitBaseChange_of_invertibleDirectImage
(node lem-pc-counit-base-change-is-iso). This is pruning of a redundant proved
intermediate, not a new proof of a formerly holed theorem.

The actual required parent theorem
AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit retains its full
existing proof. The two newly attached declarations are already proved:
AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_pullback_ne_zero and
AlgebraicGeometry.pullback_baseChangeMap_map_counit_ne_zero. They introduce no
proof obligation or split-off work. On empty bases the fibrewise criterion is
vacuous; the nonzero-counit lemma correctly requires a nontrivial affine source.

## No longer needed

Withdraw Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso, node
lem-pc-counit-base-change-is-iso. A full scan of DAG stmt_deps, proof_deps and
proof-step uses found just lem-pc-arrow-iso-pullback-counit as an actual parent;
that edge is replaced in this packet. Other DAG occurrences are historical
creation or blueprint ancestry. No unit realization names the withdrawn node.
The representability unit's zero-scheme naturality argument is preserved.

Removed from that parent's route: lem-pc-counit-base-change-is-iso and the two
obsolete duplicated tool_uses entries for lem-pc-rf-base-change-flat-module. Its
new route records the subfunctor stability already supplied by
lem-pc-f-open-subfunctor, the two attached source lemmas, and lem-pc-smooth-flat
(reviewer correction: smoothness supplies, by instance, the flatness and local
finite presentation that pullback_baseChangeMap_map_counit_ne_zero and
IsInvertibleDirectImage.map_of_isProper need, so the edge stays in step 2).

With the item, remove its two private imports:
Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison and
Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange.
Their corresponding nodes, lem-pc-counit-base-change-degree-zero-comparison and
lem-pc-flat-invertible-canonical-derived-base-change, are no longer needed by this
branch. Those modules and their declarations remain in the library; this packet
makes no claim that they are unused by every other branch. The item's three
public imports disappear only from its withdrawn module stub.

There are zero Lean downstream modules. Searches of both live lean/ and
quarantine/ find no importing file or use of the retired theorem outside its own
live file. Thus this withdrawal is supported by the actual complete replacement
argument and its reconciled parent dependencies, not merely by zero importers.

## Where the brief, the DAG or earlier work was wrong

The retained report described an absent quarantined module. On the current
source it is already restored, explaining the return's identical-text finding.
There is no remaining missing-definition repair. The old parent DAG route also
predated the adopted fibrewise proof and incorrectly kept the derived comparison
reachable. The repaired packet follows that existing proof, preserving the
source-library boundary and the unit's naturality statement.

An exploratory recompilation of the unchanged 1,000-line ZeroScheme source hit
the 60-second limit. That source is not edited or delivered; the published
implementation is already built. The direct import/axiom check described above
succeeded and certifies that the relevant published proof has no unproved
assumption. No proof or file was split and no compile limit was raised.

## New nodes

lem-pc-invertible-morphism-iso-on-residue-fibres attaches the already proved
AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_pullback_ne_zero in
WeilConjectures.AlgebraicGeometry.Modules.InvertibleFibre. It detects a line-bundle
isomorphism by the nonvanishing of its residue-field fibres. This is an
attachment of an existing proof, with no new Lean statement or hole.

lem-pc-counit-nonzero-after-affine-base-change attaches the already proved
AlgebraicGeometry.pullback_baseChangeMap_map_counit_ne_zero in
WeilConjectures.AlgebraicGeometry.Picard.CounitBaseChange. It supplies precisely
the nonvanishing contradiction in the parent proof. Its full source hypotheses,
including flatness, properness, finite presentation, injective resolutions,
affineness, a local free generator and nontrivial target functions, are retained.
No new Lean statement or hole is added.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
