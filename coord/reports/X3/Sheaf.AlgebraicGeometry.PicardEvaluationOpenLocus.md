## What changed

Completed the proof of `AlgebraicGeometry.Scheme.exists_picardEvaluationOpenLocus`.
The proof obtains the cup-product transpose criterion, extracts finite local freeness
of the direct image from the identity rank test, installs the dual instances, applies
the determinant isomorphism-open theorem, and composes the two universal equivalences.
The proof-only imports of `PicardCupProductCriterion` and
`FiniteLocallyFreeMapIsoOpen` are used. The identity test requires rewriting
`Category.id_comp` before extracting its first conjunct.

The two strictly smaller assertions remain isolated in their own modules as the
stage-3 decomposition: `exists_picardCupProductCriterion` and
`Modules.exists_finiteLocallyFreeMapIsoOpen`.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.exists_picardEvaluationOpenLocus` (node
`lem-sc-picard-evaluation-open-locus`). The delivery leaves the two intentional
sorries in the new declarations `exists_picardCupProductCriterion` (node
`lem-sc-picard-cup-product-criterion`) and
`Modules.exists_finiteLocallyFreeMapIsoOpen` (node
`lem-sc-finite-locally-free-map-iso-open`). No other new declarations contain sorry. The unchanged local compile-support copy
of `PicardDirectImageRankLocus.lean` retains the pre-existing hole
`AlgebraicGeometry.Scheme.exists_picardDirectImageRankLocus`; it is byte-identical to
the repository and is not a delivered change. This is a decomposition: one original
hole closed, two new holes added, net -1 holes closed; the target still uses sorryAx.

## No longer needed

No imports or modules were pruned. The public rank-locus import is required by the
original signature, and both proof-only imports are used. The old direct proof
dependencies `lem-pc-module-pullback-adjunction` and
`def-amb-finite-locally-free-module` are no longer direct dependencies of the item's
proof; they remain dependencies of the cup-product criterion. Thus neither can be
pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier local check was blocked by an unavailable compiled object for the
unchanged public dependency `PicardDirectImageRankLocus`. For this validation the
identical source was present in the sandbox, and the complete four-module sandbox
compiled successfully; `deliver3.py ... --no-push` also completed successfully
(the second reading subsequently removed the `letI` style warnings). No target signature or definition was
changed.

## New nodes

`lem-sc-picard-cup-product-criterion` records the cup-product transpose and its
base-change equivalence with the evaluation counit. `lem-sc-finite-locally-free-map-iso-open` records the determinant principal-open construction and its universal
property. Their declarations and proof docstrings are in the corresponding new
modules.


## Second reading by X3

1. Compared all existing sandbox modules with the repository by `diff`. The entire
   original theorem signature is byte-for-byte unchanged; only its proof and two
   private imports differ. The rank-condition definition and rank-locus theorem are
   byte-identical. There are no interface changes or change records needed. Verdict:
   pass.
2. Compiled all four modules in import order with `lcompile.py`. Removed the three
   `letI` style warnings. The only added holes are the two named new theorems listed
   above; there is no data definition in the new modules, no forbidden declaration,
   and no arbitrary witness selected to define data. The item's axiom check contains
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this
   decomposition. Verdict: pass as a decomposition, not an axiom-free proof.
3. Read both split-off signatures and complete proof docstrings against Stacks
   [Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) and
   [Section 10.79](https://stacks.math.columbia.edu/tag/05GD), Lemma 10.79.4.
   Checked empty schemes, zero rank, unequal bundle ranks, varying ranks, and
   nonreduced test rings. The determinant criterion uses units over the test ring,
   not just a nonzero determinant. The cup-product argument uses the stated
   canonical base-change isomorphisms and equal ranks to turn a left inverse into
   an inverse. Each statement is a proper part of the original argument: the first
   constructs a detecting bundle map without a locus; the second constructs its
   universal open without any Picard-family assumptions. New searches with
   leanfinder (bundle-homomorphism determinant open and global-section pairing),
   loogle (`SheafOfModules, IsIso`, which could not resolve `IsIso`), and grep,
   plus `rg` in both library roots, found no existing theorem closing either hole
   in a few minutes. Verdict: pass; both holes remain.
4. Read the proof from the conclusion backwards. Its final iff composition,
   determinant-open application and identity-rank test are the real reduction.
   All imports are needed for signatures or the proof. Updated `No longer needed`
   to list the old direct dependencies replaced by the two new lemmas; no module
   becomes unreachable. Read `dag/units/sk-prop-av-cube.json`: its recorded
   `realized` arrays are empty, and the cube/general-cube/Picard route is unchanged.
   Verdict: pass.
5. Compared all three nodes to their Lean declarations. The existing node's three
   proof steps, dependency union and provenance describe exactly the implemented
   reduction. Both new nodes have source, proof, searches, creation, blueprint,
   chapter/unit and Lean records. Made their `lean.statement` strings verbatim
   multiline signatures instead of whitespace-normalized signatures. Verdict: pass.

Changes in this reading: replaced three `letI` commands by `let`; corrected the
pruning and hole-accounting report; recorded verbatim signatures for the new nodes.
No mathematical statement, definition, or proof route was changed.
