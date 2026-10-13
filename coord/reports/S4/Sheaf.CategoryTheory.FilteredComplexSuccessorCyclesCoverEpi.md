## What changed

The existing theorem `CategoryTheory.filteredComplex_successor_cycles_cover_epi`
keeps its byte-for-byte signature, docstring, visibility and public imports.
Its proof now obtains simultaneous differential representatives from the existing
`filteredComplex_differential_representatives_cover`, pulls their epic page
projection back along `D.page.iCycles`, and proves that the lifted differential
represents a target boundary. The correction lemma gives successor representatives;
cancellation of the graded inclusion and `iCycles` produces an epic factorization
through f. Mathlib `epi_of_epi_fac` finishes.

Added two proof-only imports: `Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover`
and `Sheaf.CategoryTheory.FilteredComplexCycleRepresentativeCorrection`.
The new correction module states only the subtraction calculation for given
simultaneous representatives, without D or a map f into its kernel. It includes
a complete natural-language proof from the displayed Stacks cycle/boundary formulas.
No definitions or existing statements changed; no change record is required.

## Proved and sorry left

Hole closed: `CategoryTheory.filteredComplex_successor_cycles_cover_epi`
(node `lem-sp-filtered-complex-successor-cycles-cover-epi`). There is no sorry
in the item's module.

Hole added and still open: `CategoryTheory.filteredComplex_cycle_representative_correction`
(node `lem-sp-filtered-complex-cycle-representative-correction`). Its proof is exactly
`by sorry` in its own new module. One upper hole closed and one lower hole added:
this is a decomposition, not a completed axiom-free proof, and has net zero holes.
The shared library's existing holes are neither edited nor reported as closed.

Both modules compile without warnings. Explicit `#print axioms` in a scratch copy
shows `[propext, Classical.choice, Quot.sound, sorryAx]` for the original theorem
and the same four axioms for the new correction theorem. The delivery probe checks every
declaration again. No axiom, unsafe, opaque, implemented_by, extern or hollow
definition is introduced.

## No longer needed

No original proof-dependency node or import was removed: the abelian-category,
filtration, subquotient and page-differential definitions are still used. No
original module is pruned. The first worker's proposed new module
`FilteredComplexSuccessorCyclesLocalEpi` and its proposed node
`lem-sp-filtered-complex-successor-cycles-local-epi` were removed from the sandbox;
they had not entered the repository.

## Where the brief, the DAG or earlier work was wrong

The first worker's local-epi statement was equivalent to the entire item:
Epi f implies its existential statement with e = identity, and its existential
statement implies Epi f by epic cancellation. Its prose incorrectly attributed
an epic map onto successor cycles to the chase, which only gives a cover of the
page kernel. It was a restatement rather than a reduction and is not delivered.

The source tex file is absent on this machine. The Stacks source was read at
https://stacks.math.columbia.edu/tag/012K (the displayed Z_r, B_r and d_r formulas).
The new lemma is the finite subtraction argument following from those formulas,
not a quotation of a separately named lemma. It uses no countable sums.

The inherited unit is `sk-prop-av-pqf-finite`, whose realized arrays are empty
and whose statement concerns proper quasi-finite morphisms. This inherited
placement does not describe the spectral calculation; it is not changed here.
The existing spectral-sequence route and all existing unit realizations are kept.

## New nodes

`lem-sp-filtered-complex-cycle-representative-correction`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-cycle-representative-correction.json`,
states the strictly intermediate representative subtraction calculation. Unlike
the rejected local-epi statement it starts with t,tprime,x,y and the equation
that the target graded class is a boundary, and concludes equality in the source
graded piece. The original theorem supplies these hypotheses using the existing
representative cover, a pullback and D.on_representatives, and separately proves
its categorical epimorphy conclusion. The node includes its exact Lean signature,
source, complete proof, creation/blueprint records and searches.

## Second reading by S4

1. Compared the delivered item with the repository using diff and an exact string
comparison of its theorem signature through `:=`. Verdict: byte-for-byte signature,
visibility, existing docstring and public imports preserved. Only the proof and
proof-only imports change. The new module contains no definition or data choice.
2. Compiled the two modules in import order with lcompile.py and inspected all
source declarations. Verdict: clean compilation, no forbidden declarations,
no sorry in the item, and exactly one documented named sorry in the new module.
The scratch-copy #print axioms results are recorded above; sorryAx remains
because this is a decomposition. No data is chosen from an unproved existence
statement in a definition.
3. Read the new lemma hypothesis by hypothesis against the Stacks Z_r and B_r
formulas: j has total degree n+1 and filtration p+r; the incoming boundary
filtration is (p+r)-r+1 = p+1, so subtracting it leaves the source graded class
unchanged and raises the differential filtration to p+r+1. Verdict: true and
strictly intermediate. Small cases checked: r=1 still subtracts F^(p+1), with
no r-1 positivity assumption; zero differential already makes t a successor
representative; zero or constant graded filtration gives x=z=0 and identity
refinement. All shifts work for negative p,n. Refinements are epic pullbacks,
so no projectivity, boundedness or concrete-category hypothesis is hidden.
Attempted LeanSearch (service unavailable: Internal Server Error); searched via
leanfinder, loogle and grep, plus rg of the filtered-complex modules
in both source roots and the DAG. Generic Mathlib exact-up-to-refinements and
pullback-epi lemmas do not prove the filtered subtraction calculation. Existing
RepresentativeKernels and SuccessorBoundaryRepresentatives state different facts.
4. Read the proof from the target down. Verdict: the existing, already proved
representative cover is used first; the only split-off step is subtraction of
the boundary representative. The remaining pullback, kernel condition, two mono
cancellations and epic factorization are proved in the original module. Both
added imports are used and are proof-only; no original proof dependency is
unused. The unit record and spectral construction route are preserved.
5. Compared both node records with the Lean. Verdict: the existing node now names
the representative cover and correction step, and its proof_deps are exactly
the union of its step uses. Its statement and lean statement remain unchanged.
The new node has the exact signature and all required fields, including searches,
source, proof_origin, chapter/unit and blueprint ancestry; no circular dependence.

Second reading changed: removed the equivalent local-epi restatement and its
module/node, replaced it with the concrete representative-correction statement,
wrote the real pullback and epimorphism reduction, corrected both DAG proof
records, and corrected this report to count the delivery as a decomposition.
