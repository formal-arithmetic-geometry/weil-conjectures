## What changed

Proved `PrincipalWLocalization.points` with its original signature and all ten conjuncts.
The prime correspondence and its closed fibre charts are proved in the new module
`Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts`. Its evaluation maps are constructed and
proved surjective in `Sheaf.RingTheory.PrincipalWLocalizationEvaluation`. Both new modules are
fully proved; neither introduces a deferred obligation.

The main proof explicitly presents the defining colimit as an upstream `Algebra.IndZariski`
algebra. The existing proved `Algebra.IndZariski.bijectiveOnStalks_algebraMap` and
`Module.Flat.of_indZariski` give the local-ring identifications and flatness. Specialization to
the diagonal establishes the connected components and closed-point characterization. A
compact-to-Hausdorff argument gives the diagonal homeomorphism. The complement-of-diagonal
calculation proves its closedness, and the diagonal gives spectrum surjectivity and faithful
flatness. No existing definition or statement changes; no forced adaptations or change records
are needed. The original node's proof, proof dependencies and proof origin now describe this
route. The blueprint unit's own statements and route are retained.

All three files compile cleanly with the permitted single-file compiler, in import order
(about 3.2, 5.6 and 3.5 seconds respectively). Cut partitions omit empty parts, so the zero-ring
case needs no extra hypothesis. Evaluation is a concrete colimit-desc construction; choices of
partition parts and inverse equivalences are uniquely determined, rather than arbitrary data
selected from an unproved existence assertion.

## Proved and sorry left

Closed one original hole: `PrincipalWLocalization.points`
(`lem-weil-pbc-w-localization-points`). All its clauses are proved, including the `A`-algebra
local-ring equivalences, the patch topology, and the closed immersions.

Added zero holes. The new main auxiliary theorems
`PrincipalWLocalization.evaluation_surjective` and `PrincipalWLocalization.primeCharts`, and
all their supporting declarations, are proved. No `sorry` remains in any of the three delivered
Lean files. This is a proof of the item, not a decomposition into new deferred theorems. The
existing construction module `PrincipalWLocalization` still has its own named obligations;
this delivery neither changes nor claims to close those existing dependency holes.
The axiom audit of every public delivered declaration found only `propext`, `Classical.choice`,
`Quot.sound`, and inherited `sorryAx` from that existing construction module. Thus the one hole
closed here is conditional on the pre-existing construction obligations; this is not a claim
that the complete import closure is free of `sorryAx`.

## No longer needed

Removed these direct proof imports from the original item:

- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Sheaf.RingTheory.WLocalClopenPartitions`
- `WeilConjectures.RingTheory.ProEtale.WLocal`

The third and fifth imports are redundant direct imports: the construction's public interface
and the proved upstream ind-Zariski API already provide the concepts needed here. Their
transitive appearances elsewhere are not claimed to be eliminated.

The new proof of this item no longer needs these nodes (and their dedicated statement modules, where present):

- `lem-weil-pbc-filtered-colimit-localization-at-prime`
  (`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`): replaced by the proved
  ind-Zariski bijective-on-stalks API, which already supplies the canonical local-ring map.
- `lem-weil-pbc-spec-map-stalk-localization`
  (a Mathlib leaf in `Mathlib.AlgebraicGeometry.AffineScheme`): the statement asks for prime
  localizations; no separate scheme-stalk comparison is needed.
- `lem-weil-pbc-w-local-partition`
  (`Sheaf.RingTheory.WLocalClopenPartitions`): Mathlib's compact constructible spectrum and a
  direct separation by `D(f)` and `V(f)` suffice.
- `lem-weil-pbc-spec-clopen-idempotent`
  (a Mathlib leaf in `Mathlib.RingTheory.Spectrum.Prime.Topology`): characteristic tuples and patch
  continuity criterion supply the required basic opens; their preimages are clopen.
- `lem-weil-pbc-ind-etale-stability`
  (`Sheaf.RingTheory.IndEtaleStability`): direct ind-Zariski flatness avoids the weakly-étale
  detour.

No kernel computation for the evaluation maps, quotient identification `W/J_x`, independence
or Boolean identities for characteristic elements, residue-field construction, or additional
fraction calculation for the topology on the diagonal is needed. The closed immersion follows
from evaluation surjectivity; its range follows from the localization prime correspondence.
The generic localization universal-property and elementwise filtered-colimit nodes remain
needed in the auxiliary proofs, and have not been pruned. Other parents can still need the
listed nodes; these are removals from this item's proof dependencies, not claims about the
entire library's import closure.

The removed direct dependencies
`lem-weil-pbc-ring-localization-universal-property` and
`lem-pc-filtered-colimit-commrings-elementwise` are retained transitively through the new
evaluation and prime-chart nodes. Together with the five eliminated dependencies listed above,
this accounts for every old `proof_deps` entry absent from the main node's new direct list.
Second reading also removed the redundant direct proof import
`WeilConjectures.RingTheory.ProEtale.IndZariski`: it is already public through
`PrincipalWLocalization` -> `IndPrincipalZariski` -> `IndEtale` -> `IndZariski`.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned proof is longer than needed:
the existing proved ind-Zariski interface supplies the local-ring and flatness arguments, and
compactness plus the Hausdorff patch spectrum supplies the diagonal topology. The full proof
in the original DAG node was available and read; its cited blueprint Markdown source is not
materialized in this machine's read-only literature checkout. The source citations are retained
from that node, with the actual formal route recorded explicitly. No target signature or
meaning is changed.

## New nodes

`lem-weil-pbc-principal-w-localization-evaluation` records the explicit compatible evaluation
maps to `A_x` and their surjectivity, from original proof steps 3 and 6. Its module is
`Sheaf.RingTheory.PrincipalWLocalizationEvaluation`. The map is constructed by factor
projection, principal-localization lifts and the colimit universal property. Surjectivity uses
the two-part `D(s), V(s)` partition and a fraction representative. The node lists all public
supporting declarations. It is fully proved and has no remaining work.

`lem-weil-pbc-principal-w-localization-prime-charts` records original proof steps 1–3 and 5–7:
prime pairs, contraction, patch continuity and closed fibre charts. Its module is
`Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts`. Selected finite-product factors and
compactness give a first coordinate; contraction gives the second. Explicit characteristic
tuples and localization contraction prove the bijection, continuity and range formula. It is
fully proved and has no remaining work. Both nodes record real LeanFinder, Loogle and grep
searches from `searches.jsonl`, plus the attempted LeanSearch search (service unavailable).
Their hits supply tools, not either full theorem. Neither node
bypasses a blueprint unit statement or its realized proof steps.

## Second reading by E1

1. Compared all delivered modules with the repository. Evaluation and PrimeCharts are new;
   Points is the only existing module changed. Its existing declaration signature now matches
   byte for byte, and its public imports are unchanged. No definition, target statement or
   existing visibility changed. The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. No change record or forced adaptation is required. Verdict: pass.

2. Read the three complete files and compiled them in import order with `lcompile.py`.
   No errors, warnings, direct `sorry`, forbidden declaration forms, or hidden holes occur.
   A scratch copy with `#print axioms` for all 15 public declarations found only the three
   permitted axioms and the inherited `sorryAx` already described above. In particular the
   colimit, evaluation cocone and cut indices are explicit data; the part and prime-equivalence
   choices are uniquely determined. The old construction's unfinished proof laws are not new
   arbitrary existence witnesses. Verdict: pass, with existing dependency holes still open.

3. No statement is split off with `sorry`. Both new nodes have real proofs and are strictly
   smaller than Points. Checked fraction surjectivity using the denominator `s` on `D(s)`;
   finite-product factor selection and compact intersection; uniqueness via contraction;
   characteristic tuples and the closed immersion induced by evaluation. Checked the empty
   spectrum, empty cut parts, `D(0)`, `D(1)`, fields, and the pair `y = x`; none requires an
   extra hypothesis. Fresh LeanFinder and Loogle searches with different queries, plus `rg`
   over Sheaf, upstream and Mathlib, found component tools but no replacement for either
   specific colimit theorem. Their nodes and source-bearing proof docstrings are present.
   Verdict: pass.

4. Read from Points downward. The canonical bijective stalk map fixes `A`, so its inverse is
   the stated `A`-algebra equivalence. Specialization to the diagonal gives the components;
   closed immersions give closed diagonal points; the explicit open complement makes their
   union closed. Compact-to-Hausdorff then proves the patch homeomorphism, and the diagonal
   proves spectrum surjectivity for faithful flatness. This uses the proved upstream route
   and avoids all five listed old proof detours. `sk-thm-properbasechange.json` has realized
   statements torsion assembly and bounded-below, and steps projective line, reduction/prime
   base change, torsion assembly; none is removed or bypassed. Accounted for all old proof
   dependencies, including the two retained through helpers. Verdict: pass.

5. Compared each node's statement and Lean record with its actual declaration; checked that
   each `proof_deps` list is exactly the union of its proof steps' `uses`, every cited node
   exists, and the origins describe the written argument. Both new nodes carry the required
   source, creation, blueprint, unit, chapter, searches and Lean fields. Verdict: pass.

Second reading changed only the redundant direct IndZariski proof import, the extra space
before Points' `:=` to restore the exact original signature text, and this report's axiom,
dependency-accounting and independent-review details. The mathematical proofs were retained.
