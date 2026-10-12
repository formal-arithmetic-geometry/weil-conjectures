## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange` with
an unchanged-signature proof. For each further base change and each of E and its dual,
the proof combines finite generation and an equal-rank linear equivalence on the stalks
with surjectivity of the specific canonical map. Mathlib's
`OrzechProperty.bijective_of_surjective_of_injective` supplies injectivity over the
commutative stalk ring; the proved source-library
`Scheme.Modules.isIso_of_bijective_stalkLinearMap` then proves the sheaf isomorphism.
No Noetherian hypothesis is introduced.

Added two statement modules with complete source-based proof descriptions:
`Sheaf.AlgebraicGeometry.PicardBaseChangeStalkRanks` and
`Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective`. The first only compares
the two stalk objects and asserts finite generation; it says nothing about the map.
The second asserts only surjectivity of that particular map at a single point.
Neither is the original isomorphism assertion under another name.

Updated the original DAG proof and created the two intermediate nodes. The local
perfect-complex/rank-locus route is retained inside the surjectivity calculation.
The cube unit statement and its realized steps are unchanged.

All three modules compile together through lcompile.py. The Mathlib searches were
performed through msearch.py and recorded in searches.jsonl. LeanSearch was unavailable;
Loogle found the generic Orzech lemma, not a geometric cohomology base-change result.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picardRankMatch_baseChange`
(node `lem-sc-picard-rank-match-base-change`). There are no sorries in the item module.

Added and left:
- `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_ranks`
  (node `lem-sc-picard-base-change-stalk-ranks`).
- `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_surjective`
  (node `lem-sc-picard-base-change-stalk-surjective`).

This is a decomposition, not a complete axiom-free proof of the geometric theorem:
one upper hole closed, two lower holes added. The lower modules contain exactly
one public named theorem each, with the entire proof `:= by sorry`.
The rank statement does not imply invertibility of any particular map; the
surjectivity statement alone does not imply injectivity. Their combination uses
finite generation, commutativity, and the independently proved stalk criterion.

Edge cases checked mathematically: rank zero gives zero stalks; an empty test
scheme has no stalks; empty fibres vanish over an open neighbourhood because the
proper morphism has closed image. Nonempty fibres remain nonempty after residue
field extension, so comparing the rank of pulled-back E at a common fibre point
identifies the two ranks. Connectedness, surjectivity of f, a structure-sheaf-unit
hypothesis, and Noetherianity are not required. Choosing frames in a proof is only
an existential witness; no definition chooses arbitrary unproved data.

## No longer needed

Removed the item's direct proof imports:
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
  (`lem-pc-rf-perfect-base-change`).
- `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus`
  (`lem-sc-perfect-h0-locally-closed`).

These are still mathematical dependencies of the new surjectivity node; they are
not claimed as globally pruned. The original open-restriction module remains a
public import because it defines the canonical map in the statement. Its
open-square calculation is needed below, in the surjectivity node, rather than
in the final stalk assembly. No globally unnecessary planned module is claimed.

The generic stalk-isomorphism criterion is the existing node
`lem-weil-pbc-module-iso-on-stalks`, implemented by the proved source helper used
in the Lean proof. No duplicate node or duplicate sheaf notion was added.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no existing signature or definition was changed.
The old proof plan describes a canonical degree-zero comparison, but the stated
`exists_perfectLowestCohomologyLocus` provides only `Nonempty` object isomorphisms;
it does not assert the required compatibility with `moduleBaseChangeMap`.
The new surjectivity statement isolates exactly this missing local calculation,
including naturality and adjunction triangle identities. The rank lemma isolates
the iterated-pullback and common-rank object comparisons separately.
The generic commutative-ring Orzech lemma avoids proving a separate geometric
injectivity statement.

## New nodes

`lem-sc-picard-base-change-stalk-ranks`: the two stalk modules are linearly
isomorphic and the target is finitely generated. Its proof uses common-rank
neighbourhoods, pullback stalks, rank comparison on a common residue-field fibre,
and the empty-fibre case. Source: Stacks 0BDP, 01C6, 0098.

`lem-sc-picard-base-change-stalk-surjective`: the canonical ordinary base-change
map is surjective at each stalk, for E or its dual. Its proof retains Stacks
0B91/0BDL, the zero outgoing matrix on the lowest-cohomology locus, and the
specific canonical comparison and open restriction. It asserts no injectivity.

There are no statement-change records or forced adaptations.

## Second reading by Q1

1. Compared all delivered modules with the repository versions. The existing
   target signature is byte-for-byte unchanged; the two additional declarations
   are new split-off statements. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all` and checked the target
   proof uses only the permitted algebraic route. The target has no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the two named
   intermediate theorems are the only remaining holes. Verdict: pass.
3. Checked both split-off statements against their source descriptions and
   searched Mathlib and the source library for existing declarations. The rank
   statement omits any claim about the canonical map, and the surjectivity
   statement omits injectivity; neither repeats the target. Verdict: pass.
4. Checked the proof from the target downward, including the stalk criterion,
   Orzech argument, and the two local geometric calculations. The removed
   direct proof imports are no longer used by the target module, while their
   mathematics remains recorded in the surjectivity node; no unit realized
   field was changed. Verdict: pass.
5. Compared the Lean signatures, DAG `lean` records, proof dependencies, and
   proof origins. The target node records the two intermediate declarations as
   its route, and each new node records its theorem and module. Verdict: pass.

Changed after this reading: added this review record only; no Lean statement,
definition, proof, import, or DAG node required repair.
