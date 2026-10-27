## What changed

Replaced the whole proof of
`AlgebraicGeometry.admissibleModificationCohomologyPresentation` by a compiling
field-by-field assembly of two strict parts of the recorded argument. The first
constructs only the original limit topos and the common-open embeddings. The second
constructs the natural spectral sequences and completion data over that specified
original geometry. The original theorem statement and the final
`AdmissibleModificationPresentation` structure are unchanged.

Moved the six supporting interfaces to the new public data module
`Sheaf.AlgebraicGeometry.AdmissibleModificationPresentationData`, preserving their
signatures and bodies. This makes the two private proof imports acyclic. The owning
node's Lean attachment now lists just the two declarations that remain in its module;
the new definition node records the moved interfaces. The change record is
`coord/changes/P4-admissible-presentation-interfaces.md`.

The server compiled all four modules in import order: data 13.7 s, spectral part
10.5 s, geometric part 5.3 s, and original item 14.1 s. No errors or warnings.
There are no existing direct importers in either live or quarantined sources, so no
consumer adaptation is needed. The moved interfaces were compared verbatim, apart
from blueprint tags, and the main theorem signature and final structure were checked
unchanged.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.admissibleModificationCohomologyPresentation`
(node `lem-per-admissible-modification-cohomology-presentation`) by combining the two
parts in Lean. The item now has zero textual holes.

Added exactly two named whole-proof holes:

- `AlgebraicGeometry.admissibleOpenToposPresentation`, node
  `lem-per-admissible-open-topos-presentation`, in
  `Sheaf.AlgebraicGeometry.AdmissibleOpenToposPresentation`.
- `AlgebraicGeometry.admissibleCompletionSpectralPresentation`, node
  `lem-per-admissible-completion-spectral-presentation`, in
  `Sheaf.AlgebraicGeometry.AdmissibleCompletionSpectralPresentation`.

This is a decomposition: one hole closed, two holes added, net minus one hole closed.
It is not a completed mathematical proof or a net sorry reduction. Neither new lemma
is the original theorem renamed: the geometric statement has no completion or
cohomology data; the spectral statement takes the original site, its limit property
and open embeddings as fixed inputs and constructs only the remaining data. The
combination keeps precisely those fixed inputs in all dependent normalization fields.
No definition contains a hole, and no object is chosen by a definition from an
unproved existence theorem.

## No longer needed

No mathematical dependency or module is pruned. The old direct public coefficient-data
import is now the public import of the data module, which publicly imports the same
coefficient data. The original proof has only the two private split-theorem imports.
The following old direct proof dependencies are retained in the new nodes rather
than removed from the argument:

- `lem-per-admissible-modification-system`.
- `lemma-nagata-affine-blowup-proper`.
- `lemma-nagata-ext-scheme-theoretically-dominant-separated`.
- `lem-weil-pbc-qcqs-over-affine`.
- `lem-sfb-closed-graph-universally-closed-diagram`.
- `lem-kun-proper-stability`.
- `lem-weil-pbc-closed-immersion-proper`.
- `lem-per-qcqs-etale-topos-inverse-limit`.
- `lem-weil-pbc-direct-image-preserves-injectives`.
- `prop-weil-pbc-inverse-image-exact`.
- `lem-sbc-qcqs-higher-images-prime-torsion`.
- `lem-weil-pbc-module-sheaves-enough-injectives`.
- `lem-per-proper-henselian-derived-restriction`.
- `lem-per-finite-cover-derived-sections-continuity`.
- `lem-weil-pbc-colimit-constant-connected-diagram`.
- `lem-trf-geometric-inverse-image-exact`.
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `thm-sp-truncation-e2`.
- `lem-pc-raw-truncation-couple-naturality`.
- `lem-sp-derived-couple-functoriality`.
- `lem-weil-pbc-derived-exchange-termwise`.
- `lem-weil-pbc-adic-completion-mod-ideal`.
- `lem-weil-pbc-complete-pair-henselian`.

The existing generic-tool approvals remain relevant through these split proofs.
No source-library declaration or import was altered or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and unit route are unchanged. The dependency declarations
are available, but their types do not directly construct this record: the qcqs topos
limit theorem returns its own finite-cover presentation, and the truncation theorem
returns an integer-indexed exact couple with convergence, whereas this item requires
a functorial natural-number spectral sequence with specified filtered maps. The two
new obligations expose the geometric conversion and the derived/convergence
construction needed to bridge those interfaces, following the original seven steps.

The dependency record for direct-image preservation of injectives names
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`; the declaration
actually occurs in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`.
Its name and signature are valid. No other group's node is changed.

Read ILO XX 4.4, printed pp.373–374, including the final Note. The comparison remains
a commutative blowup square, not a claim of flat base change. The spectral lemma
constructs the completed projections and site comparisons together, so it does not
assert compatibility for arbitrarily chosen incoherent completed projection data.
The chosen original presentation is transported along its limit equivalence.

Edge checks: I=0 (and nilpotent I) gives empty U and zero abutments; the corresponding
degenerate topos has all arrows invertible, so conservativity does not require a
nonempty set of points. A=0 and F=0 are compatible with both parts. For n=0 the
filtration has exactly one graded piece. Nothing requires the coefficient exchange
or the completion cohomology map to be invertible. The original geometric conclusion
also carries the nonempty cofiltered category; no empty-index constant-colimit claim
is used. The unit's realized statement and steps are not bypassed.

## New nodes

`def-per-admissible-modification-presentation-data` records the six unchanged moved
interfaces; its new module contains no theorem hole.

`lem-per-admissible-open-topos-presentation` records original proof steps 1–2, including
common-open naturality and transport of the full qcqs limit-site construction into
the existing `AdmissibleToposPresentation` interface.

`lem-per-admissible-completion-spectral-presentation` records original proof steps 3–7
over a fixed original site and open embeddings. Its statement retains coefficient
transition and colimit normalizations, torsion-only convergence, natural filtrations,
completion cofinality and canonical filtered pullback.

Each new node inherits the chapter, unit and blueprint provenance, has a source and
complete proof in words, and records LeanSearch, LeanFinder/Loogle and grep searches.
Change record: `coord/changes/P4-admissible-presentation-interfaces.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
