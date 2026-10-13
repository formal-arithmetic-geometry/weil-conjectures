## What changed

The existing signature and docstring of `exists_adjoin_singleton_splitting_cover` are
unchanged. Its proof now unpacks uniform split-polynomial construction data and applies
Mathlib `Ideal.IsPrime.prod_mem_iff` to a maximal, hence prime, contracted ideal.
The original three public imports are retained for the existing signature. Added imports
`Sheaf.RingTheory.AdjoinSingletonSplittingPolynomialCover` and
`Mathlib.RingTheory.Ideal.Operations` are proof-only, written `import`.

The new module `Sheaf.RingTheory.AdjoinSingletonSplittingPolynomialCover` states
`exists_adjoin_singleton_splitting_polynomial_cover`: the construction through the finite
localized cover, with a uniform positive-degree product certificate, before choosing a
factor. Its docstring gives the full construction and source. No definitions were added.

Removed the first worker's two undelivered helper declarations and their undelivered node
records. The root-witness helper was false; the finite-cover helper lacked the polynomial
data needed by any valid root extraction. Their signatures were not library interfaces.

## Proved and sorry left

Hole closed in the existing module: `exists_adjoin_singleton_splitting_cover`
(node `lem-weil-pbc-monogenic-splitting-cover`). Its root extraction is a genuine Lean
proof using Mathlib, but the full theorem still depends on the construction hole below.

Hole added: `exists_adjoin_singleton_splitting_polynomial_cover`
(node `lem-weil-pbc-monogenic-splitting-polynomial-cover`), in the new module. This is
exactly the whole proof `:= by sorry`, with a construction proof in its docstring.

This is a decomposition, not a complete proof: one old hole closed, one new hole added;
net zero holes closed relative to the repository. The first worker's two proposed holes
are not delivered. Both delivered declarations have axiom sets exactly
`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`; the latter comes from the named
construction theorem. No other sorry, axiom, unsafe code, or hollow definition is present.
Both delivered modules compile, in dependency order, without warnings.

## No longer needed

No original imports were removed. No module is claimed pruned: the new construction node
retains the original algebraic route below this node. The parent no longer directly uses
its old proof-dependency list; its actual proof dependency is the new construction node.
All old dependencies below remain in that construction's plan:

- `lem-weil-pbc-zariski-lemma`
- `lem-weil-pbc-nagata-localization`
- `def-weil-pbc-nagata-ring`
- `def-weil-pbc-japanese-domain`
- `lem-weil-pbc-integral-closure-finite-extension-normal`
- `lem-weil-pbc-finite-over-nagata-nagata`
- `def-weil-pbc-integral-closure`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-integral-maximal-contracts-maximal`
- `lem-weil-pbc-integral-prime-over-maximal-maximal`
- `def-weil-pbc-localization-at-prime`

The invalid `lem-weil-pbc-monogenic-splitting-cover-root-witness` and incomplete
`lem-weil-pbc-monogenic-splitting-cover-data` were never repository nodes and are omitted.

## Where the brief, the DAG or earlier work was wrong

The first worker's root-witness assertion is false. Take Rprime = Q[s,t], fraction field
Q(s,t), z=s/t and M={1}. Then T=Rprime[z] is isomorphic to Q[t,z], with s=tz.
All maximal ideals of the localization contract maximally because localization at {1}
is an isomorphism. However the maximal ideal (t,z^2+1) has residue field Q(i).
The image of Rprime in this quotient is just Q, while the image of z is i, so no
coefficient r in Rprime has z-r in this ideal. Rprime is a normal domain. Normality
and maximality cannot replace the missing splitting-polynomial hypothesis.

The old helper docstrings/node records also failed the documentation requirements:
the root-witness theorem had no proof docstring; the data docstring named the parent
blueprint node; both Lean signature records held only declaration names, their proof
steps were incomplete, and the node files were at the sandbox root rather than under
`dag/nodes/`. These are repaired by a single correct construction node/module.
The first proof also produced six letI style warnings, eliminated in the replacement.

The source is Stacks Tag 0334, Step 5 (https://stacks.math.columbia.edu/tag/0334).
The certificate retains its uniform split polynomial, which the first worker discarded.
The extraction uses an existing Mathlib theorem and introduces no duplicate helper.
LeanFinder, Loogle and grep searches succeeded; LeanSearch returned Internal Server Error
and is recorded as unavailable. Local searches found no existing construction theorem.

## New nodes

`lem-weil-pbc-monogenic-splitting-polynomial-cover` states the finite-cover construction
with a uniform positive-degree split-polynomial evaluation certificate, a concrete
intermediate stage of the original argument. All roots are fixed before the maximal
ideal is selected; the new statement does not assert the final individual root witness.
Its full source proof, dependency steps and matching verbatim Lean signature are recorded
in `dag/nodes/sec-proper-base-change/lem-weil-pbc-monogenic-splitting-polynomial-cover.json`.
Its module is `lean/Sheaf/RingTheory/AdjoinSingletonSplittingPolynomialCover.lean`.
No change record is required: no existing statement, definition or public import changed.

## Second reading by E1

1. Compared the delivered item with the repository using diff and checked its declaration
   signature byte for byte: unchanged. The original declaration/docstring and all public
   imports remain intact; only proof imports and its proof were added. No definitions or
   existing interfaces change. The new module declares a new statement, not a replacement
   interface for an existing declaration. Verdict: pass after repair.
2. Compiled both files individually/in dependency order through lcompile.py. No errors or
   warnings remain. Appended #print axioms in scratch copies of both files: each reports
   precisely propext, Classical.choice, Quot.sound and sorryAx. There is exactly one named
   sorry, in the documented construction theorem, and no forbidden declaration or data
   chosen in a definition from an unproved existence theorem. Verdict: decomposition only.
3. Tested the first split's edge cases and found the explicit Q[s,t] counterexample above.
   Replaced it with a uniform split-polynomial certificate and reused Mathlib for factor
   extraction. The repaired construction is the original source argument up to product
   membership, without the final prime-ideal step. Positive degree excludes the empty
   product; independently an empty product could not belong to a proper ideal. Degree one
   reduces to direct membership of the sole linear factor; repeated roots and positive
   characteristic cause no issue for the finite-product theorem. Its source/docstring and
   node are complete. Searched via LeanFinder, Loogle, grep and local lean/ with different
   queries; no matching cover construction found. Verdict: corrected statement is true,
   needed, and isolates construction from extraction; one hole remains.
4. The shortest available root extraction is Mathlib's product lemma, now used directly.
   The proof-only imports are private imports; all public imports supply types in the
   unchanged target signature. All old parent proof dependencies are accounted for above.
   Checked dag/units/sk-thm-p1.json realized statement/steps: the splitting-cover node is
   below unit level, and no realized node or unit step is bypassed. Verdict: route preserved,
   no claimed pruning or net closure progress.
5. Existing node changed only in proof, proof_deps and proof_origin. Its two proof steps
   match the Lean proof: unpack construction; apply Mathlib to extract a factor. The new
   node has a self-contained statement, complete proof plan, union of used dependencies,
   source, searches, ancestry, creation metadata, and matching Lean module/signature.
   Node files now occupy the paths deliver3.py reads. Verdict: pass after repair.

Changes made by this second reading: removed the false root-witness assertion and the
insufficient data split, added the correct uniform polynomial construction, replaced
root extraction with Mathlib, removed letI warnings, repaired node paths/records and
rewrote this report to distinguish decomposition from proof.
