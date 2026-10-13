## What changed

Repair B9 (reviewer X-d15c3): corrected both new nodes' blueprint objects to
name `thm-sc-theorem-of-cube` as the nearest blueprint ancestor, with intervening
nodes `lem-sc-picard-cech-cup-pullback-compat` and `lem-sc-picard-kunneth-qcoh`
nearest first. Used the reviewer's exact ancestor place and added `same_as: []`
to record the blueprint search result. No Lean proof or statement changed in
this repair.

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.cechCupPullbackCompat`
by a reduction to `cechRefinement_comparison_square` and
`cechCup_resolution_representatives`. The first gives the arbitrary-cover
refinement comparison square. Surjectivity of cycle classes, the cup cocycle,
and the two existing cup characterizations give the product equality from the
second. Injectivity of the final comparison proves the inverse clause.
Both new intermediate modules are proof-only imports. The second reader demoted
`Sheaf.Paper.CechComparisonMapNaturality` to a plain import because only a proof
uses its theorem; the signature-level definitions remain publicly available.
All existing declaration signatures and definitions are unchanged.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.cechCupPullbackCompat`, node
`lem-sc-picard-cech-cup-pullback-compat`. This is a decomposition, not a completed
axiom-free proof: one of the three original holes is replaced by two strictly
smaller named holes (local hole balance: 1 closed minus 2 added = -1).

Original holes still left in the item, both on
`lem-sc-picard-cech-cup-pullback-compat`:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

Holes added:

- `AlgebraicGeometry.Scheme.Modules.cechRefinement_comparison_square`, node
  `lem-sc-cech-refinement-comparison-square`.
- `AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives`, node
  `lem-sc-cech-cup-resolution-representatives`.

No other holes added or closed. The four previously proved public naturality
statements remain unchanged. No whole-library progress or fully proved target
is claimed; the maintainer's pinned sorry ledger determines closure progress.

## No longer needed

Removed the parent node's direct proof dependency on
`def-pc-tensor-complex-sheaves`: the concrete proof uses the existing Cech Leibniz
and cup interfaces, rather than constructing a tensor complex itself. All other
old proof dependencies are still used by the reductions or the existing
naturality proofs. No module is claimed pruned from the target import closure.
No direct import was removed. `Sheaf.Paper.CechComparisonMapNaturality` was
demoted from public to proof-only, not removed; its theorem is still used by the
composition proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery's two new blueprint objects named the immediate parent
instead of the nearest blueprint ancestor and omitted the intervening route
and `same_as` search result. Repair B9 corrects all these fields exactly as
requested under stages/1-dag.md §6.

The first worker's parent node added the new dependencies without adding them
to the proof steps, so proof_deps was not the union of uses. The new nodes had
placeholder natural-language statements, empty statement dependencies and empty
proof dependencies. Their lean.statement fields contained literal Unicode escape
sequences instead of Lean source. The second reader repaired these, restored the
unchanged parent lean record, and removed the duplicated proof-origin suffix.
The initial report did not distinguish the decomposition from a completed proof.
The public comparison-naturality import was needed only in a proof.

## New nodes

`lem-sc-cech-refinement-comparison-square`: one-coefficient, arbitrary-cover
refinement naturality of canonical comparisons, without any cup statement.
Source: [Stacks Tag 01FD](https://stacks.math.columbia.edu/tag/01FD), Lemma 20.15.1.
The docstring supplies the four-double-complex proof. Its node names the existing
comparison naturality theorem used to identify the canonical comparison.

`lem-sc-cech-cup-resolution-representatives`: compatible cocycles in an actual
computing acyclic resolution pairing, before either cohomological cup product is
chosen. Source: [Stacks Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV), Lemma
20.31.4, and the signed pairing of Tag 07MB. Its node names the existing Godement
pairing, flasque acyclicity and canonical-comparison interfaces. Neither split
statement restates the conjunction in the item. Both remain substantial work;
no quick existing theorem found closes either.

Change record:
`coord/changes/CechCupPullbackCompat-comparison-proof-import.md`.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered existing module and its node to the read-only
   repository. The only existing Lean changes are two plain proof imports, one
   import demotion, and the body of cechCupPullbackCompat. All seven public theorem
   signatures, private helper signatures, local options and definitions remain
   byte-for-byte unchanged. No hypothesis added, conclusion weakened, or data
   definition altered. Verdict: pass.
2. Compiled all three modules through lcompile.py, with no errors or warnings.
   Read each new statement and the entire changed proof in the context of its
   imports. All remaining sorry bodies are exactly named theorem holes listed
   above; no forbidden declarations or data chosen from an unproved existential
   theorem are introduced. Scratch #print axioms probes and delivery-tool axiom
   checks are recorded below. The existential resolution witnesses are eliminated
   only inside a theorem proof, never used to define data. Verdict: pass subject
   to the recorded open dependencies.
3. Checked both intermediate statements against their definitions and Stacks
   01FD/0FKV. The refinement statement needs neither an affine nor an acyclic cover.
   The representative statement uses flasque resolution complexes as D.K, with
   computing maps to injective resolutions; it does not assert an injective tensor
   pairing. At p=q=0, augmentation pairing recovers the tensor of global sections.
   Zero coefficients/classes admit zero cocycles. Empty index sets can cover only
   the empty scheme, where all sections and classes are zero. Identity refinements
   give the ordinary canonical square; repeated indices are allowed by the tuple
   formula. Independent leanfinder, loogle and grep searches used new wording:
   only basic sheaf restrictions/nonabelian H1/flasque definitions appeared, not
   either intermediate statement. Repository searches found the Godement and
   flasque interfaces now recorded as dependencies, but no direct replacement.
   Each hole has a source, proof docstring, matching node and separate module.
   Verdict: true, needed, and strictly smaller than the combined item.
4. The proof follows the shortest available interfaces: existing cycle
   surjectivity and Leibniz, the two cup characterizations, then the two remaining
   geometric comparisons. The inverse clause is proved directly by injectivity.
   No additional split or duplicate existing theorem is introduced. The new
   imports are plain imports. Pruning is listed above; dag/units/sk-prop-av-cube.json
   has empty realized lists and is unchanged, and its cube-theorem route is not
   bypassed. Verdict: pass; decomposition only.
5. Repaired the new nodes to give self-contained statements, explicit stmt_deps,
   substantive sourced proof steps, and proof_deps equal to the union of uses.
   lean.statement is now the exact multiline source signature. Updated parent
   proof steps to match the actual refinement/representative reduction and
   inverse-comparison cancellation. Its proof_deps is now the union of those
   steps and all unchanged naturality steps; proof_origin records this route.
   Chapter/unit/source and existing statements are unchanged. Verdict: pass.

Second-reading changes: DAG statements/dependencies/proof routes/search records,
proof-only import correction and its change record, and an accurate decomposition
report. The Lean proof itself was correct and was not rewritten.

Validation: the scratch probes for all seven original public declarations and
both new declarations compiled cleanly. Every axiom list was a subset of
propext, Classical.choice, Quot.sound and sorryAx; the three direct Cech
coefficient/refinement naturalities have no sorryAx. The combined compatibility
and composition declarations retain sorryAx through the open geometric results.
Probe timings: 53.6 seconds for the main module, 6.8 and 4.5 seconds for the new
modules. The scratch copies were removed before delivery.

The first dry run compiled and passed the axiom checks, but preflight required a
separate LeanSearch record in addition to leanfinder, loogle and grep. Both
LeanSearch requests returned Internal Server Error; their unavailability is now
recorded without a mathematical verdict. The successful alternative searches
remain recorded. This fixes the two reported preflight failures.

Dry run: deliver3.py --no-push printed OK and passed preflight, including its
compilation and per-declaration axiom checks. Review class CODEX: new nodes,
new intermediate modules, and the proof-import visibility correction. A final
notation cleanup in the new refinement node's natural-language statement changes
no Lean statement or mathematical content; delivery reruns the same checks.

## Second reading by D4

1. Compared each delivered existing module with the repository version. The only
   Lean changes are the proof of `cechCupPullbackCompat` and the demotion of
   `Sheaf.Paper.CechComparisonMapNaturality` to a proof-only import; existing
   declarations and definitions have byte-for-byte unchanged signatures. Verdict:
   pass.
2. Compiled all three delivered modules with `lcompile.py`. The remaining
   `sorry`s occur only in the two named new theorem declarations and the two
   pre-existing sheaf-cup naturality declarations. No forbidden declaration or
   hollow definition was introduced; the proof-only imports are used. Verdict:
   pass.
3. Read both new statements and their docstrings against Tags 01FD, 07MB and
   0FKV, including zero degrees, zero classes, empty covers, and identity
   refinements. They are true, needed, and strictly smaller than the parent
   conjunction; each has a matching node and source. Verdict: pass.
4. Checked the proof route and pruning. The parent proof uses the two new
   comparison/representative interfaces, existing Cech cup characterizations,
   and injectivity for the inverse clause; no shorter available declaration was
   found. The unit route remains recorded and no unnecessary module was claimed
   pruned. Verdict: pass.
5. Checked that the new node `proof`, `proof_deps`, `proof_origin`, and Lean
   records match the actual proof and that the parent node records the reduced
   route. Verdict: pass.

Second-reading changes: added this required review section only; no Lean proof or
statement was changed.
