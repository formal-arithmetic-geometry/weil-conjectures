# Q15 stage-1 delivery: lem-sf-native-adic-qcqs-stratification

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-adic-qcqs-stratification.json`: statement; four-step split, no item-level Mathlib match. Statement and original statement dependencies unchanged.
- No new nodes and no new Mathlib leaves.
- `citations.json`: eight verbatim statement quotations, one for each step/node pair.
- `searches.jsonl` and `search-*.txt`: actual helper queries and complete returned results. The four inherited Mathlib searches were retained, and five new logged searches (including two semantic phrasings) were added after reading their results.

## Attachments

None proposed. The current brief expressly requires a split after the preceding attachment attempt received no answer from the server. I read `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicStratifiedLisseSheaf` and `exists_isAffineOpen` in the live read-only `ExtensionByZero.lean`; I use their argument as source material, without claiming a transitive Lean closure check or an attachment.

## WANTED

None. All source material used is available in the read clone.

## Findings and corrections

The imported item is a true native-coefficient assertion with both quasi-compactness and quasi-separatedness. Its empty proof did not expose the finite-cover and refinement argument. Its statement is preserved verbatim, including arbitrary schemes, the coefficient sheaf on X itself, varying finite local rank, and empty X. Some prose docstrings in the source say only quasi-compact, but the theorem's Lean signature also assumes `QuasiSeparatedSpace X`; the item already includes this essential hypothesis.

The main potential C4 trap is `lem-weil-pbc-etale-stratification-local-gluing`: its statement assumes an etale map and proves finiteness of its base changes, so it cannot globalize this native adic sheaf. I instead found and opened `lem-weil-pbc-etale-stratification-local-gluing-core`. Despite its historical name, its statement is purely geometric, assumes only a qcqs scheme, a finite affine cover and local constructible immersed stratifications, and explicitly supplies actual factorization morphisms. This exactly fits the argument. No finite/discrete coefficient category is substituted for the native module category.

Another potential C4 trap is `lemma-constructible-pullback-stratification`: its statement gives locally closed immersed partitions but does not assert constructibility of their images. Step 2 separately cites `lem-weil-pbc-constructible-open-restriction`, because the map there is an open inclusion. For lissity and composition, it cites precisely the existing native node `lem-sf-native-adic-pullback-exact-lisse`; no assertion about etale finite locally constant sheaves is used.

## Not duplicates

No new nodes. I searched the whole DAG and blueprint for stratifications, refinement, retrocompactness, affine covers and native lisse pullback, and the Lean source by the item tag, theorem name and notions. The existing geometric refinement core and native pullback statement cover the non-elementary inputs, so neither was duplicated. The generic finite-coefficient sheaf globalization nodes are not exact duplicate statements of this item; the condensed coefficient definition also does not state the native qcqs globalization theorem.

## Review by Q15

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md` including all three blueprint levels, `GOAL.md`, the worker role, the package unit and six-functors chapter, and both copies of delivery-errors B through E. I read the item's actual source, `lean/WeilConjectures/SixFunctors/ProEtale/Adic/ExtensionByZero.lean`, especially lines 108-198, and the coefficient/lisse/constructible and pullback declarations in `Adic/Constructible.lean` (definitions around lines 80-161, pullback around lines 187-233). The proof is marked agent-origin because it adapts the project's source argument using an existing geometric black box. I also read Stacks `etale-cohomology.tex`, tag 095E (`lemma-constructible-quasi-compact-quasi-separated`), implication (2) to (3), and tag 03S0 (`lemma-etale-stratified-finite`), as well as `schemes.tex`, tag 01IT (`lemma-basis-affine-opens`). Tag/label pairs were checked in `tags/tags`. No SGA source is used. There are no new-node sources to review.

For step 1 I opened the framework's full current statement. It explicitly defines local constructibility with finite constructible locally closed pieces and a finite rank per pro-etale covering member. The item itself extends that construction to X rather than a geometric fibre. I opened `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`: it refines every open cover of a qcqs scheme by finitely many affine opens, each contained in a selected original member. Both its hypotheses are present. No intersection of affine opens is claimed affine.

For step 2 I opened all three cited statements. `lemma-constructible-pullback-stratification` gives precisely the fibre-product schemes, their immersions and the inverse-image partition. `lem-weil-pbc-constructible-open-restriction` gives constructibility in each new affine chart, since it is an open subspace of the original neighbourhood. `lem-sf-native-adic-pullback-exact-lisse` is stated for arbitrary scheme morphisms in the very same locally finite continuous-coefficient module category. Its final sentences supply the composition comparison, and its middle sentence supplies lisse preservation. The cartesian-square equality is explicitly written before applying that comparison. Neither exactness nor the coefficient-map-isomorphism clause is needed for this split.

For step 3 I opened the geometric core's whole statement and proof. Its finite affine cover and finite constructible immersed partition hypotheses are supplied by steps 1 and 2. Its conclusion says that each global stratum factors by an actual scheme morphism through a local stratum. That is exactly what the step quotes and uses. I do not deduce a factorization from image containment, which can fail for nonreduced schemes. The core's existing proof uses closed-subscheme pullbacks when disjointifying the charts. I declare this and the other off-unit geometric statements as generic tools in `split_report.tool_uses`; none changes the package unit's route.

For step 4 I rechecked the native pullback statement's lissity and composition clauses against the displayed factorization. Applying them to the lisse local restriction gives the required lisse restriction on each global stratum. `def-constructible-stratification` supplies exactly a finite immersed locally closed partition; the stronger constructibility of the images comes from the core, not from that definition. Isomorphism invariance here is immediate by composing each local trivialization with the pulled-back isomorphism. Empty X is handled by the empty family independently of any nonempty-cover choice. No new hypothesis is introduced.

I tested the argument on empty X, a point, M=0, repeated local charts and empty intersection strata, varying ranks on disconnected covering members, nonreduced schemes, and qcqs schemes that are non-Noetherian or nonseparated. It never assumes Noetherianity, reducedness, separation, a constant global rank or positive ranks. A two-affine nonseparated cover still uses the qcqs geometric core; it does not assume its overlap affine. Omitting quasi-separatedness would remove a hypothesis of the core, so that hypothesis is retained.

Against B: there are no new statement-only nodes to leave underspecified, no unlogged searches and no claimed Mathlib leaf. The fresh searches returned structure-sheaf identities, Chevalley constructibility, topological constructibility and finite cover constructions, not this native lisse-sheaf theorem; Loogle and the native-name grep returned zero hits. Against C: every non-elementary input is an existing cited statement; all eight quotations were copied from the actual statement files. A read-only dependency traversal of each input found no path back to the item. Against D: the proof carries the cover selection, chart restriction, global refinement and lissity argument itself, with no renamed clause moved to a child node. Against E: all hypotheses and native coefficient categories agree, and actual pullback schemes and factorization morphisms handle the scheme-theoretic issue. Each step is below 2000 characters and hides no separately invoked lemma.

## Unfinished work

None at stage 1. No Lean was written or compiled. The server dry run and direct push are the required final checks/actions.
