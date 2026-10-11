## What changed

Replaced the one sorry in `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange`
with a proof reducing arbitrary base change to base change to geometric points. Added proof-only
imports of `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange`,
`WeilConjectures.SixFunctors.BaseChange.Pasting`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.
The existing public import and every existing declaration signature are preserved.
Updated the underived-exchange node's proof, proof_deps, and proof_origin to the actual reduction.

For each algebraic-closure point of Yprime, the proof forms the second pullback square and
its horizontal paste. Properness of fprime permits the geometric-point lemma on both squares.
The proved pasting law cancels their exchange isomorphisms and the composition isomorphisms.
The natural stalk-pullback comparison transports this to the original geometric stalk;
stalk conservativity and componentwise natural-transformation invertibility finish the proof.

## Proved and sorry left

`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`
(node `lemma-weil-pbc-proper-underived-exchange`) has a complete proof with no direct sorry.
This is a partial delivery: its non-formal geometric-point case remains open, so the theorem
still depends transitively on sorryAx and is not yet closed under the project's axiom criterion.

The only sorry added or left in the delivery is
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isProper_geometricPoint`
in `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange`, node
`lem-weil-pbc-proper-geometric-point-exchange`. Its whole proof is `:= by sorry`.
Its docstring and node retain the canonical strict-henselization, henselian degree-zero,
field-extension, and germ-compatibility proof, with no torsion assumption.

Both modules compile locally without warnings. Edge cases checked for the remaining lemma:
empty X/fibre gives zero section modules; identity f gives the adjunction identity;
a geometric point with transcendental field extension still uses the pullback sheaf,
not a newly formed structure or multiplicative-group sheaf over the larger field.

## No longer needed

No existing import is removed: the public DegreeZero import is part of the existing interface.
No original mathematical input is globally pruned by this partial delivery. The canonical
comparison dependencies are concentrated in the new geometric-point node, not discarded.
In particular proper-strict-henselian-h0, sections-base-field-extension, cartesian-square,
underived-exchange, proper-base-change, and geometric-stalk-conservative remain needed.
The torsion-only `prop-weil-pbc-strict-henselization-stalk-formula` /
`Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` is not used by this route; it is
replaced for degree zero by `lem-weil-pbc-sets-pushforward-stalk-strict-henselization` /
`Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`. This is a local route
replacement, not a claim that the torsion formula can be removed from other proofs.
`def-weil-pbc-etale-sheaves` and `def-weil-pbc-scheme-conventions` remain statement/proof
inputs of the new lemma; they are not pruned. No additional Sheaf module was imported unused.

## Where the brief, the DAG or earlier work was wrong

The original DAG's stalk-formula application explicitly assumes torsion, whereas the source
Lean theorem covers arbitrary module sheaves. The degree-zero argument needs the unrestricted
sets-valued stalk formula, which already exists as a stated node. No signature was weakened.
The remaining lemma must use the actual canonical exchange map; an abstract identification of
source and target sections alone does not prove the required compatibility.

The module's existing Stacks annotation names 0A3T, which is the canonical stalk-to-fibre
comparison; general base change is 0A3U. The new lemma's proof uses both appropriately.
Verified the published sources [0A3T](https://stacks.math.columbia.edu/tag/0A3T),
[0A3U](https://stacks.math.columbia.edu/tag/0A3U), and
[0A3I](https://stacks.math.columbia.edu/tag/0A3I). The local literature tex file is absent;
these published sources supply the reading. No source statement was changed.

Mathlib searches were actually run through msearch: LeanFinder returned morphism-stability
and topological stalk facts, Loogle returned generic Guitart-exact Kan-extension facts,
and grep returned no Mathlib match. LeanSearch returned HTTP 500 and is recorded as unavailable.
The complete imported-blueprint search for geometric-point base change found no matching node.
The sk-thm-iff unit route remains: the non-formal comparison uses sections over the strict
henselization and closed geometric fibre; only the general-square compatibility is proved
using the already established pasting law.

## New nodes

`lem-weil-pbc-underived-horizontal-pasting`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-underived-horizontal-pasting.json`, recording the existing proved declaration `Etale.baseChangeMap_paste_horiz_app` from `WeilConjectures.SixFunctors.BaseChange.Pasting` and its exact component identity.

`lem-weil-pbc-proper-geometric-point-exchange`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-proper-geometric-point-exchange.json`,
with new module `lean/Sheaf/AlgebraicGeometry/ProperGeometricPointExchange.lean`.
This is the geometric-point special case, applied separately to f and its proper base change;
it has a source and complete proof in words and becomes the next proving item.
No definition or existing statement changed, and no change record is required.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations and signatures.** Compared the delivered underived-exchange module with the repository version. The existing theorem statement, namespace, variables, and documentation are unchanged byte for byte; only proof-only imports and the proof body were added. The geometric-point theorem is a new declaration recorded by its node, with no alteration of an existing declaration. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; they compile without errors or warnings. The underived theorem has no direct `sorry`; the only split-off `sorry` is the named geometric-point theorem, whose docstring and DAG node give its source and complete proof plan. No forbidden declarations occur. The underived theorem is consequently still transitively open exactly where the report says. Verdict: pass.

3. **Split-off statement.** Checked the geometric-point statement against the existing base-change definitions and the Stacks 0A3T/0A3U route. It has no added torsion hypothesis and states the actual exchange component, rather than an abstract comparison. Its edge cases (empty fibre and identity morphism) are covered by the same section-map argument. Search records and the repository search found no existing declaration of this statement. Verdict: pass.

4. **Route and pruning.** The proof reduces the general square to two geometric-point squares using the existing horizontal pasting identity, then transports through the existing pullback-stalk comparison and conservativity. The unit route through the underived exchange coherence and stalk comparison is retained. The proof-only imports are minimal for the declarations used; no old dependency is claimed pruned beyond the report's explicit route replacement. Verdict: pass.

5. **DAG agreement.** Repaired the citation in proof step 2 to the new node `lem-weil-pbc-underived-horizontal-pasting`, whose statement records exactly the existing proved declaration `Etale.baseChangeMap_paste_horiz_app` and its signature from `BaseChange/Pasting.lean`. Updated `proof_deps` accordingly. The geometric-point node has its statement, source, proof steps, dependencies, Lean record, chapter, and unit metadata. No definition, target statement, or unit realization was changed. Verdict: pass.

Changes made during this second reading: none to the Lean or DAG files; appended this review record only.

## Second reading by G1

1. **Visible declarations and signatures.** Compared the delivered existing module with the
repository version byte for byte. The theorem statement and documentation are unchanged; only
proof-only imports and the proof body differ. The geometric-point theorem is a new declaration
with its own node. Verdict: pass.

2. **Proof and axioms.** Compiled all delivered Lean modules with `lcompile.py --all`; both
compile without errors or warnings. There is no forbidden declaration. The target theorem has no
direct `sorry`; the only remaining `sorry` is the named split-off geometric-point theorem, as
listed in the report and node. Verdict: pass.

3. **Split-off statement.** The geometric-point lemma states the actual base-change component
for an arbitrary module sheaf and commutative ring, with no torsion assumption. Its parameters
match the square used by the target proof, and the node records the source, proof plan, and
edge-case checks. Repository and Mathlib searches found no duplicate declaration. Verdict: pass.

4. **Route and pruning.** The target proof uses properness under pullback, the existing horizontal
pasting identity, geometric-point exchange, and stalk conservativity. The unit route is retained;
the three added imports are proof-only and all are used. The report records the replaced torsion
stalk route and no unjustified pruning. Verdict: pass.

5. **DAG agreement.** The target node's proof steps and dependencies match the Lean proof,
including the existing `baseChangeMap_paste_horiz_app` declaration. The split-off node's Lean
record matches its theorem signature and module. No target, definition, or unit realization was
changed. Verdict: pass.

Changes made during this second reading: appended this section only; no Lean or DAG repairs were
needed.
