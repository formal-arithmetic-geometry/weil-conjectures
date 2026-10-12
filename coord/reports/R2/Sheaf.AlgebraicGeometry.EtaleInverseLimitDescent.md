## What changed

Proved `AlgebraicGeometry.Etale.exists_stage_of_inverseLimit` with its statement unchanged.
The proof chooses an affine triple around each point, restricts the étale limit map,
uses chart descent, takes a finite subcover, finds a common upper bound including i₀,
and applies étaleness local on the source.

Added `Sheaf.AlgebraicGeometry.EtaleAffineChartDescent`. Its public theorem
`AlgebraicGeometry.Etale.exists_stage_on_affine_chart` applies the existing
`Etale.exists_stage_of_directedColimit` to ring data supplied by the geometric
comparison theorem. Three proved private helpers show that Over.pullback gives a
cartesian square, that restriction to a source open preserves that square, and that
étaleness on a chart persists under an additional base change. This persistence is
proved by pullback pasting and scheme étale base change, without tensor cancellation.

Added `Sheaf.AlgebraicGeometry.AffineChartDirectedRingModel`, containing the remaining
geometric comparison as one named theorem. It supplies a finitely presented algebra
map over a directed ring system on the upper tail, compares étaleness at the limit,
and transfers ring-model étaleness to the chart at each individual stage. It has no
étaleness hypothesis, no compactness hypothesis, and no conclusion asserting the
existence of an étale stage. Thus this is a part of the affine argument, not the
original descent statement under another name.

Updated the original DAG proof and added nodes for both public helper theorems.
The unit `sk-thm-p1`, its realized nodes, and the chapter route are unchanged.
The original six-step affine/locality argument is retained, with its geometric
comparisons grouped into the one remaining theorem.

All three modules compile locally without warnings. The single-chart and global
proofs contain no `sorry`. The dry run performs the server compile and preflight.

## Proved and sorry left

- `AlgebraicGeometry.Etale.exists_stage_of_inverseLimit`
  (`lem-weil-pbc-descend-etale`): original `sorry` replaced by a complete proof.
- `AlgebraicGeometry.Etale.exists_stage_on_affine_chart`
  (`lem-weil-pbc-etale-affine-chart-descent`): proved from the ring-model comparison,
  the existing directed-colimit descent theorem, and Mathlib pullback/base-change facts.
- `AlgebraicGeometry.exists_affineChart_directedRingModel`
  (`lem-weil-pbc-affine-chart-directed-ring-model`): the delivery's only remaining
  `sorry`, exactly `:= by sorry`. Its docstring and node give the full geometric proof.
- The three private helpers `etale_on_open_of_isPullback`, `over_pullback_square`,
  and `etale_on_open_pullback_comp` are proved.

The imported `AlgebraicGeometry.Etale.exists_stage_of_directedColimit` remains an
existing admitted dependency, not a new or changed `sorry` in this delivery. Neither
the original theorem nor the chart theorem is claimed to have a closed axiom closure.

Edge cases checked in the argument: an empty source permits the empty finite cover;
inserting i₀ into the finite set of indices still supplies an admissible stage.
The upper tail is nonempty because it contains i₀. Directedness of a preorder,
not antisymmetry or a linear order, is all the proofs use. Distinct proofs of the
stage inequalities cause no mismatch because Lean identifies proofs. The ring-model
statement allows empty affine opens, whose coordinate rings are zero rings; its
pullback and spectrum identifications still hold. It imposes no nonzero-ring condition.

## No longer needed

Removed the public import `Sheaf.AlgebraicGeometry.LimitAffineTransition` and the
proof dependency `lem-weil-pbc-limit-affine-transition`. Its assertion that some
limit exists is unnecessary when the theorem is already given a limiting cone.
The remaining comparison uses the existing Mathlib leaf
`lem-weil-pbc-limit-cone-affine-projections-opens`, together with
`lem-weil-pbc-spec-colimit-limit`. This is pruning of this proof route, not a claim
that no other target branch imports `LimitAffineTransition`.

Removed the direct proof import `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent`
from the original module and moved it to `EtaleAffineChartDescent`, where its theorem
is actually applied. The module and `lem-weil-pbc-colimit-etale-ring-map` remain needed.

The geometric persistence argument no longer uses
`lem-weil-pbc-tensor-cancel-base-change` or `lem-weil-pbc-etale-ring-base-change`;
it uses `lem-weil-pbc-etale-scheme-base-change` instead. Those ring lemmas remain
among the existing directed-colimit theorem's planned dependencies, so they are not
claimed to be globally pruned. The original affine-open, finite-presentation,
restricted-limit, spectrum-colimit, open-pullback, affine-pullback, and étale
composition/cancellation ingredients remain in the ring-model theorem's DAG route.

The import change record is
`coord/changes/etale-inverse-limit-prune-import.md`. It lists all 215 downstream
modules reported by `tools/downstream.py`, which found no use of the removed
existence theorem. `tools/import_prune_check.py` passed. No downstream statements
or definitions are adapted by this delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original limit-existence
proof dependency was stronger than needed for this theorem's given limiting cone.
The affine comparison is the substantial glue that the source's proof omits; none
of the existing ingredient declarations alone states it. It is now isolated with
its coordinate-ring construction and projection compatibility spelled out.

The local literature files named by the node are not present on this worker machine.
Read the official Stacks pages for Tags 07RP, 07RI, and 081D instead. The source's
proof is the affine reduction followed by the algebra descent lemma. LeanSearch
returned HTTP 500 for both new helper searches; those searches are recorded as
unavailable, not as negative results. Loogle, LeanFinder, and source grep ran.

## New nodes

`lem-weil-pbc-etale-affine-chart-descent` records the proved local descent theorem
in `Sheaf.AlgebraicGeometry.EtaleAffineChartDescent`: a fixed affine triple descends,
then its chart map stays étale at all later stages. It needs no ambient qcqs
assumptions and does not assert global étaleness. Its proof combines the ring model,
the existing ring descent theorem, and the fully proved cartesian-square persistence.

`lem-weil-pbc-affine-chart-directed-ring-model` records
`AlgebraicGeometry.exists_affineChart_directedRingModel` in the new module
`Sheaf.AlgebraicGeometry.AffineChartDirectedRingModel`. It is the one remaining
geometric step: construction of coordinate rings on the upper tail, finite
presentation of the chart map, and its affine pullback/limit identifications.
Its statement contains no hypothesis of limit étaleness and no eventual-étaleness
conclusion. The node's four proof steps name all the existing geometric ingredients.

Change record: `coord/changes/etale-inverse-limit-prune-import.md`.

## Second reading by R2

1. I compared the delivered item module with the repository version. The target
   theorem signature is byte-for-byte unchanged; the item change is its proof and
   the proof-only import adjustment declared in the change record.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors or warnings. The only remaining `sorry` is the named public
   theorem `AlgebraicGeometry.exists_affineChart_directedRingModel`, and it has a
   matching node, source, and full proof docstring. No forbidden declarations or
   hollow definitions occur.
3. I checked the two split-off statements against their uses and searched the
   library for duplicates. The chart theorem is exactly the local descent claim;
   the ring-model theorem contains only the geometric comparison and does not
   assume or conclude eventual etaleness. Both are true at empty charts and use
   only the stated directed-preorder hypotheses.
4. The proofs follow the shortest available library route after the affine chart
   reduction: the existing directed-colimit etale theorem, pullback/base-change
   lemmas, finite subcover, and source-locality. The removed limit-existence import
   and unused dependencies are recorded under `## No longer needed`; the node
   proof dependencies match the route written in the modules.
5. The unit `sk-thm-p1` and its realized route remain unchanged. The item node and
   both new nodes agree with the Lean declarations, including proof origins and
   dependencies. I found no statement or unit-route error.

I changed only this report after the first delivery attempt: added this required
second-reading record.
