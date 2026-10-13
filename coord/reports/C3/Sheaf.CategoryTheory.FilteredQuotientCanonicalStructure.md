## What changed

Completed the proof of `CategoryTheory.filteredQuotient_canonical_structure` with its
original hypotheses, conclusion, universes, and visibility. The first conjunct follows
by composing `hd` with the first connecting comparison. For the second conjunct the
proof uses explicitly constructed homology terms and maps, takes `eD` to be identity,
and defines `eC` in the existential proof as `eQ` followed by `eZ` inverse. It proves the
inclusion equation by definition, the initial projection equation by the normalized
base comparison and inverse cancellation, and the derived differential equation by
postcomposing with `eZ.hom`, rewriting `hd`, cancelling inverses, and using `hQ`.

Added five modules: `FilteredHomologyCoupleData`, `FilteredHomologyCoupleExactness`,
`FilteredHomologyExactCouple`, `FilteredHomologyCoupleQuotientPages`, and
`FilteredQuotientFirstConnecting`, all under `Sheaf.CategoryTheory`. The first defines
actual homology objects and actual inclusion, projection, and connecting maps and
proves `filteredStep_shortExact` directly from Mathlib. The exact-couple definition
assembles those data with a named, postponed exactness theorem. It chooses no data from
an existence theorem. The other two postponed comparisons are independent of the
supplied spectral sequence. Only proof imports were added to the existing module;
its public imports are unchanged. The DAG proof follows this assembly.

Second reading removed the redundant plain import
`Mathlib.CategoryTheory.Abelian.Exact` from the new exactness module; its
statement already elaborates through the concrete-data import.

The whole six-module sandbox compiles with `lcompile.py --all`. New statements were
checked on zero complexes, constant filtrations (graded homology zero, inclusion
identity), and a complex supported in a single filtration grade (no higher
differentials). A two-step filtered complex gives the expected first connecting map
with the sign prescribed by Mathlib's connecting morphism. The representative
normalization fixes `eH` by an epic composite, and the representative condition fixes
`D`; the comparisons therefore cannot be arbitrarily rescaled. Integer index
transports are explicit and checked by Lean. No countable sums are assumed.

Sources read: Stacks Tags 012K and 011Q, including the cycle/boundary formulas and
Lemma 12.24.3(1), and Mathlib's HomologySequence at lines 295--325. Searches used
LeanFinder, Loogle, the logged grep service, and direct `rg` on both library roots.
LeanSearch returned HTTP 500 and is recorded as unavailable. The blueprint searches
for “exact couple” and “filtered complex” found the existing general exact-couple and
spectral-object nodes, but no existing declaration for these concrete comparisons.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.filteredQuotient_canonical_structure`
(node `lem-sp-filtered-quotient-canonical-structure`). No `sorry` remains in that module.

Added three strictly smaller postponed statements:

- `CategoryTheory.filteredHomologyCouple_exact`
  (`lem-sp-filtered-homology-couple-exactness`): only the six exactness/zero-composite
  properties of fixed, explicit maps. No derived pages or spectral sequence.
- `CategoryTheory.filteredHomologyCouple_quotient_pages`
  (`lem-sp-filtered-homology-couple-quotient-pages`): comparisons between the concrete
  couple and concrete representative quotients, including base normalization and
  differential compatibility. No arbitrary spectral sequence, first two-step
  connecting comparison, or abutment.
- `CategoryTheory.filteredQuotient_first_connecting`
  (`lem-sp-filtered-quotient-first-connecting`): only the first concrete quotient-page
  differential and the two-step quotient short exact sequence. No exact couple or
  derived pages.

This is a decomposition: one upper hole closed and three lower holes added, net -2
before any pruning. It is not reported as a fully discharged theorem. Each remaining
hole is exactly `:= by sorry`, public, in its own module, with a source, complete
proof in words, and a matching node. The concrete data modules have no holes.

## No longer needed

The old direct `proof_deps` were `def-sp-exact-couple`,
`def-sp-filtered-complex-subquotients`, `def-sp-filtration`, and
`lem-sp-filtered-complex-page-differential`. All four remain transitive dependencies
of the concrete couple and comparison statements; none becomes unreachable.
They are replaced as direct proof steps by the three new nodes recorded in the
item's `proof_deps`. No old node or module is no longer needed.

Removed the redundant plain import `Mathlib.CategoryTheory.Abelian.Exact`
from the new `FilteredHomologyCoupleExactness` module. No DAG dependency is
removed: the named Mathlib exactness facts remain its intended proof route and
are transitively available. No existing import or module is pruned. The original filtration, subquotient,
exact-couple, and representative-differential definitions remain needed through the
new nodes and the unchanged public signatures. The proof does not use spectral
sequence successor-homology identifications, direct sums, naturality, stabilization,
or an abutment theorem; none has been added as a dependency. The new first connecting
module imports HomologySequence directly and does not import the concrete exact
couple or its exactness theorem.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-0d858, E3: corrected the incoming-image filtration index
in `FilteredHomologyCoupleQuotientPages.lean` from `F^(p-s)` to `F^(p-s-1)`.
At page `r=s+1`, the incoming differential starts at `p-r=p-s-1`;
the successor boundary formula uses `p-(s+2)+1=p-s-1`, as in
[Stacks Tag 012K](https://stacks.math.columbia.edu/tag/012K). The old index
described current boundaries. This repair changes only the proof docstring;
all Lean signatures, proof terms, imports, and DAG dependencies are unchanged.

The earlier sandbox contained uncompiled lower modules, an unchanged upper `sorry`,
and no nodes or report. Its attempts to simplify index transports inside the
homology exact-couple construction failed against dependent short-complex and
filtration proof arguments. This delivery separates the explicit data from their
exactness proof and completes the upper assembly. Three pages of componentwise
argument were not already covered by the original node's dependencies, which were
mostly definitions; they are now named statements rather than anonymous proof holes.

Base normalization is stated as heterogeneous equality of morphisms. This avoids an
expensive elaborator comparison of the zero-stage natural-number cast against the
first-page integer index; the upper proof converts it with `eq_of_heq`. Its content is
exactly equality with the canonical graded-homology isomorphism followed by `eH.inv`.
The recorded unit has no realized statement or proof-step nodes here. The original
spectral-object exact-couple route is retained, including the first differential.
No statement correction or forced adaptation was required. The dry run's command
comparison requests a change record for the compiler/linter options even though all
exported signatures are identical. This is documented in
`coord/changes/filtered-quotient-canonical-structure-options.md`, including the direct
user and the unchanged old and new signatures.

## New nodes

`def-sp-filtered-homology-couple-data` records the actual homology terms and maps in
`Sheaf.CategoryTheory.FilteredHomologyCoupleData`, including the proved successive-step
short exact sequence. It introduces concrete data, not an unknown witness.

`lem-sp-filtered-homology-couple-exactness` records the six homology-map properties in
`Sheaf.CategoryTheory.FilteredHomologyCoupleExactness`. Its proof is the long exact
homology sequence with equality transports.

`def-sp-filtered-homology-exact-couple` records the assembly of these terms and maps in
`Sheaf.CategoryTheory.FilteredHomologyExactCouple` and its reindexed initial graded
homology equality isomorphism. Its only postponed content is the named exactness
proof; every data field is explicit.

`lem-sp-filtered-homology-couple-quotient-pages` records the derived-couple comparison
in `Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages`. The base case is
normalized by `eH`, and the induction identifies successor cycles, boundaries, and
the differentiated representative.

`lem-sp-filtered-quotient-first-connecting` records the first-page calculation in
`Sheaf.CategoryTheory.FilteredQuotientFirstConnecting`. The projection squares fix the
two short-complex maps, and the representative formula fixes its connecting map.

Change record: `coord/changes/filtered-quotient-canonical-structure-options.md`.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered target module with the repository version. The theorem
   signature, hypotheses, conclusion, universes, and visibility are byte-for-byte
   unchanged; only proof imports, compiler options, and the proof body changed.
   Verdict: passed.

2. I compiled all six sandbox modules with `lcompile.py --all`. The target has no
   remaining `sorry`; the three postponed results are named public theorems with
   complete source and proof descriptions, and no definition contains `sorry`.
   No forbidden declarations occur. Verdict: passed, with three documented split
   statements remaining.

3. I checked the split statements against the concrete constructions and their
   edge cases (zero complex, constant filtration, and one-grade support). Each is
   strictly smaller than the target: exactness, quotient-page comparison, and the
   first connecting calculation respectively. The nodes, declarations, and
   `proof_deps` agree. Verdict: passed.

4. I checked the proof route and imports. The target uses the concrete couple,
   quotient-page comparison, and first connecting result; no existing import can
   replace them, and no import was removed. The route retains the stated exact-couple
   construction and first differential. Verdict: passed; no pruning was available.

5. I checked the DAG records, unit metadata, source references, and the options
   change record. The unit route is retained, and the options change records only
   elaboration/linter settings with unchanged exported signatures. Verdict: passed.

Changes made during second reading: added this review record only; no Lean proof,
statement, definition, node, or import required repair.


## Earlier second reading (a previous round; superseded)

1. Compared all six delivered modules with the repository. Five are new; the
   existing theorem's full signature is byte-for-byte unchanged (also checked with
   the delivery declaration parser). Its docstring and public imports are unchanged.
   The two added imports are proof-only. The option commands are covered by the
   supplied change record. Verdict: passed; no statement or definition was weakened.

2. Compiled all six modules in dependency order with `lcompile.py --all`, with no
   errors or warnings. A scratch copy with `#print axioms` confirms the upper theorem
   and the three split statements use only the standard axioms and `sorryAx`;
   `filteredStep_shortExact` uses only standard axioms. The axiom probes of delivery
   check every delivered declaration as well. The three reported named theorem
   holes are the only holes; no forbidden declaration or hollow definition occurs.
   The original direct importer `FilteredQuotientPageRealization` also compiles
   unchanged against this sandbox overlay. Verdict: passed as a decomposition,
   not a fully discharged target.

3. Read each split statement, its docstring argument, and its node. Exactness is
   exactly the six properties of the explicit homology maps, supplied by the long
   exact homology sequence after index transports. The quotient-page comparison
   concerns the fixed concrete couple, and the first connecting comparison concerns
   only the two-step quotient sequence. None restates the full item. Conceptual
   edge checks: zero complexes give zero maps and objects; a constant filtration
   gives zero graded terms and identity inclusions; a single filtration grade has
   no outgoing differential. For a differential crossing one filtration step the
   first-page formula is precisely the connecting morphism. Checked the incoming
   index `p-s-1`: at page `r=s+1`, the incoming differential starts at `p-r`, and
   successor boundaries use `p-(s+2)+1`. Checked this against
   [Stacks Tag 012K](https://stacks.math.columbia.edu/tag/012K).
   Fresh LeanFinder, qualified-name Loogle, logged grep, and direct library searches
   found the Mathlib long exact sequence lemmas and existing representative-page
   constructions, but no theorem replacing either concrete comparison. Verdict:
   passed; the three remaining statements are true, needed, and strictly smaller.

4. Read the upper proof from both conjuncts downward. It transports the first
   connecting equation by `hd`, then constructs the explicit couple and transports
   `eQ` by `eZ` inverse. Identity `eD`, inverse cancellation, and the base equation
   give the remaining equations. The proof uses no arbitrary witness to define
   data. The exactness hole needs dependent index transports in all six components;
   it is not a one-line application of the located Mathlib results. No short repair
   was identified. Public imports needed by existing exported declarations remain;
   all added proof imports are plain imports. The old proof-dependency nodes remain
   reachable transitively, now explicitly enumerated under `No longer needed`.
   Verdict: passed; no module pruned.

5. Verified each node's `proof_deps` equals the union of its proof steps' `uses`,
   and checked its Lean declaration, source, blueprint ancestry, status, creation
   record, and search record. The existing node changes only its owned proof fields.
   The unit's `realized` arrays contain no assigned statement or step node here;
   the spectral-object exact-couple and first-differential route is retained.
   Verdict: passed.

Changes in this second reading: expanded the pruning report to enumerate all four
old direct proof dependencies and added this independent review and validation
record. No Lean statement, definition, proof, import, or DAG field required repair.


## Second reading by C3

1. Compared every delivered module with the repository using `diff` and a
   byte comparison of the existing theorem signature. Five modules are new.
   The existing signature, docstring, universes, visibility and public imports
   are unchanged. Its only command changes are the options documented in the
   supplied change record. Verdict: pass; no statement or data was weakened.

2. Compiled all six modules locally in dependency order, without errors or
   warnings. A fresh scratch copy printed axioms for all twelve delivered
   declarations: only `propext`, `Classical.choice`, `Quot.sound` and, where
   postponed statements are reachable, `sorryAx`. The explicit homology terms,
   maps and step short-exactness theorem have no `sorryAx`. Exactly the three
   reported public theorems contain `sorry`; no forbidden declaration or hole
   in a definition occurs. Also compiled the unchanged direct importer
   `FilteredQuotientPageRealization` against the sandbox overlay. Verdict: pass
   as a decomposition (one original hole closed, three holes added, net -2),
   not an axiom-free proof of the target.

3. Read the three split statements and their docstrings against the explicit
   constructions. Conceptual edge checks: zero complexes give zero homology;
   constant filtrations give zero graded homology and identity inclusion maps;
   one-grade support gives zero higher differentials. A differential crossing
   one filtration step gives the ordinary connecting map. Checked the total
   degree and filtration shifts of alpha, f, g and the derived differential.
   The incoming source at stage s is p-s-1, in agreement with the successor
   boundary formula in [Stacks Tag 012K](https://stacks.math.columbia.edu/tag/012K).
   Reviewed the exact-couple derivation against
   [Tag 011R](https://stacks.math.columbia.edu/tag/011R).
   Fresh LeanFinder, qualified-name Loogle and logged grep searches located
   Mathlib's homology_exact₁/₂/₃, comp_δ, δ_comp and δ_eq', but no existing
   concrete page comparison. Direct searches of both library roots likewise
   found no replacement. Each new hole is true, necessary and strictly part
   of the argument; none restates the whole item. Verdict: pass.

4. Followed both upper conjuncts downward: hd transports the concrete first
   connecting equation; the fixed couple and eQ followed by eZ inverse supply
   the second conjunct, with identity eD and inverse cancellation. The couple
   defines actual data; the exactness theorem supplies only proof fields.
   Existential eQ witnesses are used only inside a proof, not to define library
   data. The derived maps upstream are determined by their restriction
   equations. The Mathlib exactness route still needs dependent index
   transports in all six assertions, so no short closure was identified.
   Removed one redundant proof import from the new exactness module and
   recompiled it. The old four direct proof dependencies remain transitive;
   no module is pruned. The recorded unit has empty realized statement/step
   arrays here; the spectral-object exact-couple route is retained. Verdict:
   pass after import cleanup.

5. Checked every node's statement against its declaration, its source,
   creation and blueprint records, and its proof steps. Each proof_deps set
   equals the union of the steps' uses. The existing node changes only proof,
   proof_deps and proof_origin. New nodes have the required records and the
   item's chapter and unit. Verdict: pass.

Changes made: removed the redundant plain Mathlib exactness import, updated
this report's import accounting, and appended this independent review. No Lean
signature, definition, proof body or DAG field changed during this reading.
