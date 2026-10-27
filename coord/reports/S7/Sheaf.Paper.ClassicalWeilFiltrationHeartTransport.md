## What changed

Decomposed `WeilConjectures.zl_classical_weil_filtration_heart_transport` into three
independent, strictly smaller geometric steps, and wrote its complete Lean assembly.
It obtains one exact finite diagram, obtains normalized fibre comparisons for that
same diagram, and proves purity quotient by quotient. The final top isomorphism is
literally the obtained last-term isomorphism composed with the supplied Weil e;
its identification is proved by reflexivity. Every specified map is retained.

`ClassicalRealizationPunctualPurity` contains a complete two-direction proof from the
local-spectrum step: forward transport uses the supplied normalized beta; reverse
transport unpacks the finite presentation witnessing an sf eigenvalue, obtains a
normalized beta, and applies classical purity to the transported eigenvalue.

Extracted existing data verbatim into `ClassicalWeilFiltrationTransportData` so the
new statement modules can depend on it without circular imports. The original module
publicly reexports it. No existing signature or definition body changes. Change record:
`coord/changes/S7-classical-filtration-data-extraction.md`. No source-tree module changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.zl_classical_weil_filtration_heart_transport` by decomposition.
There are no remaining holes in the item module.

Added three holes, each a named public theorem in a separate module:

- `WeilConjectures.zl_classical_filtration_exact_diagram`
  (`lem-zl-classical-filtration-exact-diagram`): exact finite-stage diagram and its
  actual Weil comparison arrows; no local operators, fibres or weights.
- `WeilConjectures.zl_classical_filtration_diagram_fibres`
  (`lem-zl-classical-filtration-diagram-fibres`): natural fibre identifications for
  an already supplied finite model and its arrow squares; no existence of that
  model, no new exactness and no purity.
- `WeilConjectures.zl_classical_realization_local_spectrum`
  (`lem-zl-classical-realization-local-spectrum`): one closed-point spectrum for one
  classical object, with existence and independence of normalized return path;
  no filtration, weights, or exact finite-stage diagram.

Proved the new intermediate
`WeilConjectures.zl_classical_realization_punctual_purity`
(`lem-zl-classical-realization-punctual-purity`) completely from the local-spectrum
lemma. This delivery is a decomposition: one original hole closed, three added,
net minus two holes; it does not claim a complete geometric proof.

## No longer needed

No mathematical dependency of the previous DAG route is pruned. Its four geometric
lemmas remain the proof dependencies of the three smaller steps, with the exact
interfaces and missing glue documented in their docstrings and nodes. No module
is withdrawn. No source-library declaration is removed.

The item no longer directly imports the following private planned-proof imports:
`Sheaf.Paper.LisseCompletedSystemComparison`, `Sheaf.Paper.GaloisLisseRepresentations`,
`Sheaf.RepresentationTheory.ProfiniteStableLattice`,
`Sheaf.Paper.RationalCoefficientCategoryComparison`, `Sheaf.Paper.LocalizedTStructure`,
`Sheaf.Paper.ContinuousRationalDerivedRealization`,
`Sheaf.Paper.AdicNormalizedFibreExactness`, `Sheaf.Paper.DlConstructibleFibresExact`,
and `Sheaf.Paper.CommonStageCalculus`. Its proof now imports only the three modules
it applies. The data module retains the inherited scheme-instance proof imports.
All original public imports are preserved by the data module's public reexport.
The postponed statement modules do not import their future proof dependencies:
those imports belong to the workers who write those proofs.

## Where the brief, the DAG or earlier work was wrong

The DAG described a short abstract assembly, but its declarations require nontrivial
interface glue: the exactness lemma takes a finite quiver presentation, the finite
diagram lemma returns raw-system Weil models, and the all-period comparison uses a
factorized classical operator rather than the literal orbit recursion. These gaps
are isolated in the three new geometric steps rather than hidden inside the parent.
Also, `ClassicalNormalizedTwoFibreComparison` currently has Omega in Type u whereas
the present item has Omega in Type (u+1); applying that interface requires coefficient
universe transport (or using its normalized finite-stage constructions). The new
statements preserve the item's original universes and add no smallness hypothesis.

Checked edge cases in the mathematical statements: length zero has no quotient or
arrow indices; zero fibres have no eigenvalues; empty Y has vacuous point assertions;
nonminimal positive return periods remain quantified in ZlClassicalFibreComparison;
Weil maps are rational and no invariant integral lattice is required for them.
The top comparison uses the supplied e for every R, not a newly chosen realization.

Read the current blueprint paragraph 1 and BS 6.8.4, Corollary 6.8.5, 6.8.7,
Proposition 6.8.14 and Remark 6.8.15. Searched the current source library, DAG and
blueprint for duplicates; Mathlib searches (LeanSearch, LeanFinder and grep) are
recorded with their actual outputs in the new nodes. General exactness, point
naturality and eigenvalue lemmas do not supply these specialized comparisons.

## New nodes

`lem-zl-classical-filtration-exact-diagram` realizes the diagram/exactness part of the
old steps 1--3 using the existing finite Weil diagram, normalized two-fibre and common
stage exactness lemmas. Its finite model is existential data in a proposition;
no definition chooses it from an unproved theorem.

`lem-zl-classical-filtration-diagram-fibres` is the natural all-period point comparison
for a supplied exact diagram. Its proof plan uses the existing normalized two-fibre
and local Frobenius comparison declarations and records the orbit-recursion bridge.

`lem-zl-classical-realization-local-spectrum` isolates the presentation-independent
single-point spectral comparison and the actual normalized return path. The proof
plan uses finite singleton diagram realization, normalized fibres and the existing
all-period local operator theorem.

`lem-zl-classical-realization-punctual-purity` records the proved purity argument from
that local spectrum; it adds no hole. The parent node records the actual Lean
assembly. Both existing definition ownership nodes point to the unchanged extracted
data; the unit route and all target signatures are unchanged.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
