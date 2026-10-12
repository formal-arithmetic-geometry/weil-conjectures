## What changed

Replaced the earlier all-conclusions core theorem with two strictly separate intermediate
statements following Stacks Tag 07CT. The existing declaration
`Algebra.exists_desingularization_strictlyStandard` retains its complete original signature.
Its proof obtains a factorization with an annihilator bound, installs the `D`-algebra structure
induced by the actual map `dB`, derives the scalar tower with `IsScalarTower.of_algHom`, and
proves finite presentation over `R` with `FinitePresentation.trans`. It then applies the generic
singular-ideal comparison to the bound and assembles the original existential conclusion.

Added proof-only imports `Sheaf.RingTheory.DesingularizeAnnihilatorConstruction` and
`Sheaf.RingTheory.SingularIdealsOfAnnihilatorBound`. The new modules each contain one public
named theorem with its complete source proof in the docstring. No definitions, target
signatures, public imports, or other modules were changed. The parent node now records this
three-step Lean argument. The two new nodes partition the original seven-step proof.

## Proved and sorry left

Closed the original hole in `Algebra.exists_desingularization_strictlyStandard`
(node `lem-weil-pbc-popescu-desingularize-strictly-standard`). Added two holes:

- `Algebra.exists_desingularization_annihilator_bound`, node
  `lem-weil-pbc-desingularize-annihilator-construction`: constructs the factorization with the
  relative annihilator bound and finite presentation over `D`. It does not assume `hR` and
  asserts neither final singular-ideal inclusion.
- `Algebra.singularIdeals_of_annihilator_bound`, node
  `lem-weil-pbc-singular-ideals-of-annihilator-bound`: compares the ideals for an arbitrary
  finitely presented tower using `hR` and a supplied annihilator bound. It mentions neither
  `A`, `Λ`, quotient compatibility, nor strictly standard elements, and constructs no ring.

This is a decomposition: one original hole closed, two strictly smaller holes added, net -1.
It is not a complete axiom-free proof of the mathematics. The original module has no remaining
`sorry`; each added module has exactly its one whole named theorem proof `:= by sorry`.
The composed reduction compiled cleanly with `lcompile.py --all`, followed by a clean single-file
compile after replacing local `letI`/`haveI` with `let`/`have` to satisfy the style linter.

## No longer needed

Removed the original module's direct proof imports
`Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`,
`Sheaf.RingTheory.PopescuDesingularize`, and
`Sheaf.RingTheory.StrictlyStandardBaseChange`.
Their mathematical work is still needed in the new nodes' proof plans; no such node is claimed
as pruned from the whole targets' closure. All original seven proof steps and their required
lemmas are retained across the two new nodes. The unpublished earlier
`DesingularizeStrictlyStandardCore` module and core node were removed from the sandbox because
they duplicated the whole conclusion. No pre-existing library node or module was deleted.

## Where the brief, the DAG or earlier work was wrong

The earlier core statement retained the whole original conclusion and added structure, so the
finite-presentation wrapper alone was not an acceptable reduction. Its node also had an
incomplete signature, a non-self-contained statement, malformed blueprint ancestry, copied
searches, and copied reviewer metadata. These were replaced rather than preserved.
The earlier report's second-reading claims are superseded; this worker has not written a
second-reading section. Duplicate file-level `set_option` commands between a docstring and
its theorem were removed. The reduction needs no file-level options.

The local checkout has no `literature/stacks-project/smoothing.tex`. Read the actual source at
https://stacks.math.columbia.edu/tag/07CT and matched its two proof paragraphs against the DAG.
LeanSearch returned HTTP Internal Server Error for both queries; recorded it as unavailable,
not as absence. LeanFinder, Loogle, Mathlib source grep, whole-library grep, and blueprint
searches found no existing theorem giving either complete intermediate statement.

Edge cases checked against the two source arguments: with `π = 0` or `π` a unit, the displayed
annihilator set is all of `D`, so the bound forces `B/D` smooth. For `π = 0`, quotient
compatibility already gives a factorization through `D`; for a unit, strict standardness
makes the inverted source smooth. With `D = R`, `hR` likewise makes that set all of `D`, and
both comparison ideals agree. Zero rings cause no exception: their prime spectra are empty.
The construction is used only by existential elimination in a theorem; no definition chooses
arbitrary data from an unproved existence theorem.

## New nodes

`lem-weil-pbc-desingularize-annihilator-construction`, in
`lean/Sheaf/RingTheory/DesingularizeAnnihilatorConstruction.lean`, realizes the tensor setup,
compatible quotient section and application of Tag 07CR (steps 1–3 of the original node).
It retains the annihilator bound rather than asserting either final inclusion.

`lem-weil-pbc-singular-ideals-of-annihilator-bound`, in
`lean/Sheaf/RingTheory/SingularIdealsOfAnnihilatorBound.lean`, realizes the finite support,
flatness and radical/smooth composition argument (steps 4–7 of the original node).
Both nodes remain in unit `sk-thm-p1`, preserve the ancestor's blueprint route, and record
current searches actually performed through `msearch.py`. No change record is needed because
all existing signatures and visibility are unchanged.

## Second reading by D2

1. **Statements and interfaces.** Compared the delivered item module against the repository version. The existing declaration signature is byte-for-byte unchanged; only proof imports and the proof body changed. The two added theorem statements are independent intermediate results with strictly smaller conclusions than the parent target.
2. **Proof and checks.** Compiled all three delivered modules with `lcompile.py --all`. The item has no `sorry`; each split theorem has exactly its named whole-theorem `sorry`. No forbidden commands or hollow definitions occur. The remaining split theorems are documented with sources and complete proof plans, and their nodes carry matching statements and declarations.
3. **Truth and strength.** Checked the annihilator-bound statement on zero and unit choices of `π`, and the comparison statement when `D = R`; the conclusions remain meaningful and agree with the Stacks argument. Neither theorem adds hypotheses or weakens a required conclusion beyond the explicit decomposition of the parent proof.
4. **Pruning and imports.** The item uses the two new modules as proof-only imports. The former three direct proof imports are removed from the item and are retained in the new nodes' recorded proof dependencies. No public import needed by existing statements was removed.
5. **DAG and unit route.** The parent node's proof and dependencies match the Lean reduction, and both new nodes have matching `lean` records, sources, proof plans, and search records. The route and `realized` unit `sk-thm-p1` are preserved.

Changed only the report to add this second-reading record; no Lean declarations or DAG statements were altered during the review.
