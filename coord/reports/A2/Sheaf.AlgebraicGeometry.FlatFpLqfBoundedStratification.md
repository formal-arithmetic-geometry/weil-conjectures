## What changed

Proved the original `exists_flat_fp_lqf_bounded_stratification` from the local
maximal-degree calculation, with its signature unchanged. The private, fully proved
`isClosed_fiber_degree_le` inducts on the bound, pulls back to the reduced closed
complement of the maximal-degree locus, and maps the resulting closed sublevel back
through the closed embedding. The main proof constructs the filtration explicitly,
identifies its differences with fibre-degree level sets, and proves monotonicity,
coverage, disjointness, and both directions of the universal property.

Added `Sheaf.AlgebraicGeometry.FlatFpLqfMaximalDegreeLocus`, with a complete Lean proof
of openness and finiteness on the maximal-degree locus. This proof constructs a
jointly surjective étale family over that locus, pastes the restriction pullback
squares, transports finite local freeness across their canonical isomorphisms, and
uses the existing étale descent theorem. The original module imports this new module
privately. All original public imports remain unchanged.

Added `Sheaf.AlgebraicGeometry.FlatFpLqfMaximalDegreeEtaleNeighborhood`, isolating
steps 2–5 of the original plan: shrinking the finite part of the étale splitting to
constant degree and proving that the complementary part is empty. This is strictly
the local calculation, with neither closedness of lower strata nor the universal
property in its conclusion. Its docstring gives the entire remaining argument.
No existing statement or definition changed; no change record is required.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Hom.exists_flat_fp_lqf_bounded_stratification`
(node `lem-weil-pbc-flat-fp-lqf-bounded-stratification`). No `sorry` remains in the
item's module. Also proved the new
`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_maximal_fiber_degree`
(node `lem-weil-pbc-flat-fp-lqf-maximal-degree-locus`) and the private closed-sublevel
induction helper.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Hom.exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree`
in `Sheaf.AlgebraicGeometry.FlatFpLqfMaximalDegreeEtaleNeighborhood`
(node `lem-weil-pbc-flat-fp-lqf-maximal-degree-etale-neighborhood`). Its proof is
exactly `by sorry`. No other hole was added. This delivery is a decomposition:
one old hole closed, one strictly smaller local geometric hole added, net zero.
The existing fibre-degree base-change, separated locally quasi-finite base-change,
and étale descent declarations are used as intended dependencies.

The three modules compile together without errors or warnings through `lcompile.py`.
Edge cases checked in the proof: bound zero, unattained maximal degree, empty base,
and degrees above the bound. Empty maximal loci use the empty covering family;
the universal property for an empty base holds for every degree.

## No longer needed

Removed proof-only imports from the item:
- `Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart`;
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`;
- `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover`;
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` (already supplied by the
  public fibre-degree-bound import).

The first two are needed by the remaining local-calculation node, and the third is
used by the proved maximal-locus module. They are relocated below the new geometric
claim, not globally pruned. No existing module is asserted unreachable from all
targets. The fourth removes a redundant direct import, not its public transitive
availability.

Original direct proof dependencies delegated to the new geometric nodes:
`lem-weil-pbc-etale-splits-off-quasi-finite-part`,
`lem-weil-pbc-finite-locally-free-degree-locally-constant`,
`lem-weil-pbc-finite-locally-free-degree-etale-descent`,
`lem-weil-pbc-etale-morphism-open-map`,
`lem-weil-pbc-morphism-factors-through-open-subscheme`,
`lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-open-preimage-fibre-product`,
`lem-weil-pbc-finite-closed-map-finite-fibres`,
`def-pc-scheme-fibre`, `def-sbc-locally-finite-presentation`,
`def-weil-finite-type-morphism`, `def-weil-etale-morphism`, `def-weil-flat-morphism`,
`def-pc-fibre-product`, and `def-weil-pbc-fibre-degree-bound`.
Definition nodes remain available through statement dependencies; geometric nodes
remain recorded where their claims are used. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The source `.tex` is not present in this read-only remote clone. Checked the actual
Stacks Tag 07RY webpage, whose maximal-degree claim and induction agree with the
node. No mathematical correction was needed. LeanSearch returned HTTP 500 on both
queries; recorded it as unavailable, and used LeanFinder and Mathlib source searches.
No existing statement changed. The existing module's docstring still describes the
original ten-step mathematical proof; the updated DAG records where those steps
are now delegated and where the Lean argument proves them.

## New nodes

`lem-weil-pbc-flat-fp-lqf-maximal-degree-etale-neighborhood`:
`lean/Sheaf/AlgebraicGeometry/FlatFpLqfMaximalDegreeEtaleNeighborhood.lean`.
The sole remaining hole is the pointwise étale splitting and degree-count argument
of Stacks Tag 07RY, proof, second paragraph (original steps 2–5).

`lem-weil-pbc-flat-fp-lqf-maximal-degree-locus`:
`lean/Sheaf/AlgebraicGeometry/FlatFpLqfMaximalDegreeLocus.lean`.
Proved openness of the maximal-degree locus and finiteness of its restriction from
the local neighbourhood result, fibre-degree invariance and étale descent.
Both nodes belong to the item's original chapter and unit, and record the original
blueprint ancestor. Three search kinds are recorded, including the unavailable
LeanSearch responses. No change records.

## Second reading by A2

1. Compared the item against the repository with `diff` and a byte comparison of the
   existing theorem header through `:= by`: identical. Public imports and all existing
   definitions are unchanged. The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`. No statement change or change record is needed. PASS.
2. Compiled all three modules in import order with `lcompile.py`: no errors or
   warnings. Scanned every delivered Lean file: exactly one named theorem has
   `sorry`, and no forbidden declaration or hollow definition occurs. Scratch
   `#print axioms` checks of the original theorem, private induction helper, and both
   new theorems show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter comes from the listed local hole and existing open dependencies; these
   are reductions, not axiom-free completed proofs. The filtration and open locus are
   explicitly constructed. Choice of covering witnesses occurs only inside a proof
   of a proposition, never in an exported data definition. PASS.
3. Read Stacks Tag 07RY (https://stacks.math.columbia.edu/tag/07RY), paragraph 2,
   and the splitting, degree-constancy, fibre-degree and descent declarations.
   The sole split-off hole is precisely the pointwise neighbourhood calculation,
   strictly smaller than the filtration and its universal property. For degree zero
   the finite fibres and both complementary parts are empty; an unattained bound
   or empty base provides no point satisfying its hypotheses. Empty maximal loci
   and empty covers are handled by the proved descent argument. Repeated searches
   with different words: LeanFinder `finite flat morphism constant fiber rank etale
   neighbourhood quasi finite` found only generic etale lemmas; Loogle on
   `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` reported unknown
   identifier/no matches; msearch grep `splits_off|finite.*flat|degree.*locallyConstant|
   IsFiniteLocallyFreeOfDegree` found FlatRank/ring flatness tools, no replacement.
   Repository `rg` on splitting, fibre rank, and stratification found the expected
   tools and the stronger downstream stratification, which depends on this item.
   The required splitting/rank/additivity argument is not a few-minute closure. PASS.
4. Read the proof top down: induction proves closed sublevels; arithmetic identifies
   strata; both universal-property directions use fibre invariance, with target-local
   finiteness in the converse. The maximal-locus proof constructs its open explicitly,
   factors a jointly covering etale family, pastes pullback squares, and descends.
   Every removed old proof dependency is named under `No longer needed`; no globally
   unreachable module is claimed. Read `dag/units/sk-thm-p1.json` `realized`: this
   auxiliary item realizes none of its fixed steps, and the reduction preserves the
   original geometric route below the unit. PASS after restoring the planned local
   proof imports described below.
5. Checked all three nodes: self-contained statements match Lean; proof dependency
   lists equal the unions of step uses; source/proof_origin agree; both new nodes have
   chapter, unit, blueprint ancestry, creation data, three search records, and Lean
   records. Trimmed the local node plan to its own conclusion. PASS.

Second reading changed no Lean statement or proof. Restored private imports of
`EtaleSplitsOffQuasiFinitePart`, `FiniteLocallyFreeDegreeLocallyConstant`, and
`FiniteFiberDegreeBaseChange` in the local-calculation module: these are its planned
proof dependencies and keep the report's relocation of the first two imports true in
the actual import closure. Removed the extraneous global openness assertion and its
`lem-weil-pbc-etale-morphism-open-map` dependency from that local node's proof plan;
openness remains proved and recorded in the maximal-locus module. Hole accounting
remains one original hole closed and one strictly smaller hole added (net zero).
