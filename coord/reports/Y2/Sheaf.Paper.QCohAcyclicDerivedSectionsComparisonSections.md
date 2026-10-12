## What changed

Replaced the sorry in `Sheaf.Paper.QCohAcyclicDerivedSectionsComparisonSections` with
composition of the canonical lower-truncation isomorphism and a general, proved
left-exact bottom-cohomology comparison. The existing signature, universes, visibility,
and public imports are unchanged.

Added three modules, each with one theorem and its node:
- `Sheaf.Paper.DerivedSectionsLeftExactBottom`: proves the comparison for any additive
  left exact functor between abelian categories, assuming enough injectives and
  K-injective resolutions only on its source. Its proof uses negative vanishing,
  the truncation triangle, double truncation, shifts, the derived single-object
  comparison, and `rightDerivedZeroIsoSelf`. It requires no Grothendieck hypothesis
  on the target category and does not use the still-holed truncation-iso theorem.
- `Sheaf.Paper.QCohAcyclicDerivedSectionsTruncationIso`: proves invertibility of the
  canonical projection on affine derived sections. It applies the existing unbounded
  cohomological bound with N=1 to the strictly lower truncation, takes the homology
  sequence of its triangle, and transports invertibility through exact evaluation.
  The composition comparison is constructed from the source K-injective model,
  avoiding an unnecessary K-injective-resolution hypothesis on module presheaves.
- `Sheaf.Paper.QCohInverseAffineOpenVanishing`: the remaining, strictly lower statement
  is positive cohomology vanishing for a single quasi-coherent module on an inverse
  affine open, proved in words by restriction, affine vanishing, and Leray degeneration.

Updated the item's node proof and dependencies to match the compiled argument.
Local `lcompile.py --all` compiles all four modules in import order without warnings.
No existing interface changes and no forced adaptations.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison_sections`
(node `new-qcoh-acyclic-sections-component`). Its proof is complete from the
named dependencies; it is not claimed to be free of transitive sorry dependencies.

Two new theorems have complete proofs:
`CategoryTheory.Functor.rightDerivedFunctor_truncated_bottom`
(node `new-qcoh-sections-left-exact-bottom`) and
`AlgebraicGeometry.qcoh_acyclic_derived_sections_truncation_isIso`
(node `new-qcoh-sections-truncation-projection`).

Added exactly one hole, the whole public proof of
`AlgebraicGeometry.qcoh_acyclic_inverse_affine_open_vanishing`
(node `new-qcoh-inverse-affine-open-vanishing`). No other delivered declaration
contains sorry. This is a decomposition: one upper hole closed, one lower hole added;
the net declaration-hole change is zero before import-closure pruning. The remaining
statement concerns ordinary positive cohomology of one quasi-coherent sheaf, not
unbounded objects, a natural isomorphism, or a repackaged target hypothesis.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.TruncationHypercohomology` and
the planned dependency `thm-sp-truncation-e2` from this route. The general truncation
exact couple, page convergence, finite image filtration, and spectral-sequence
naturality are unnecessary for the bottom-degree calculation. Their pruning from
the whole targets closure depends on other consumers and must be measured by the ledger.

Removed six other direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`,
`Sheaf.AlgebraicGeometry.LerayDegenerateSections`,
`Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`,
`Sheaf.Topology.RestrictInjectiveResolution`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective`.
These six are moved to the appropriate intermediate modules, not claimed as globally
unneeded. Two additional redundant direct proof imports were removed:
`Sheaf.AlgebraicGeometry.DerivedCategory` and
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`; the unchanged public import
`Sheaf.AlgebraicGeometry.DerivedSectionPresheaf` already supplies their interfaces. Restriction, Leray, affine vanishing, and the quasi-coherence clause of
`lem-pc-finite-support-hi` remain in the lower vanishing argument; the unbounded bound
remains in the proved truncation theorem. No unit statement or realized unit step
was removed. Of the nine old proof dependencies, only `thm-sp-truncation-e2`
is unnecessary throughout this new argument. The six geometric dependencies
(restriction of injective resolutions, derived open restriction, finite-support-hi
clause (1), affine vanishing, Leray degeneration, and the derived-direct-image
definition) remain in the lower lemma. The unbounded bound remains in the
truncation theorem; `def-pc-derived-category` remains a statement dependency
and is provided by the retained public imports.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the natural-isomorphism assembly interface. The
canonical truncation natural transformation, `asIso`, and a general natural bottom
comparison supply that assembly directly. Component-and-naturality data equivalent
to the target are not used as a new hole.

The original plan invokes the full hypercohomology spectral sequence in its step 3.
Only the lowest degree is needed after truncation, so negative vanishing, double
truncation, and left exactness suffice. This is a change below the unit level.

The library's `rightDerivedFunctorCompMapDerivedCategoryIso` unnecessarily requires
K-injective resolutions in its intermediate category for this application. The
proof here constructs the same exact-evaluation comparison using the shared source
K-injective model, without changing the library interface.

The `lem-pc-finite-support-hi` Lean attachment records uniform vanishing, while its
quasi-coherence clause is the separate source declaration
`Scheme.Modules.isQuasicoherent_higherDirectImage` in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`. The remaining
vanishing lemma's docstring explicitly needs only that quasi-coherence clause, not
a support bound. Its future proof must bridge ordinary and total higher direct image
using the existing single-object derived comparison; it must not add separatedness.

Checked edge cases: the empty affine open, zero quasi-coherent sheaf, zero derived
object, arbitrary integer cutoff, and objects unbounded in either direction.
The inverse image of an affine open is not assumed affine. The generic bottom
comparison assumes no quasi-coherence and no resolutions in its target category.

Searches used LeanFinder, Loogle, Mathlib source grep, the source library, and the
blueprint index. LeanSearch was attempted but returned Internal Server Error;
that unavailability is recorded without a mathematical verdict in the new nodes.
The source proof was read in the available copies of Stacks `perfect.tex` (Tag 08D4),
`derived.tex` (Tag 05TC), and `cohomology.tex` (Tag 01F4).

## New nodes

`new-qcoh-sections-left-exact-bottom`:
`dag/nodes/sec-picard-framework/new-qcoh-sections-left-exact-bottom.json`.
A proved general bottom comparison, extending the existing affine-specialized
`affineDerivedSections_truncated_bottom` argument. It carries no new hole.

`new-qcoh-sections-truncation-projection`:
`dag/nodes/sec-picard-framework/new-qcoh-sections-truncation-projection.json`.
A proved canonical truncation-map statement using the existing N=1 bound, with
presheaf evaluation and source K-injective-model compatibility proved in Lean.

`new-qcoh-inverse-affine-open-vanishing`:
`dag/nodes/sec-picard-framework/new-qcoh-inverse-affine-open-vanishing.json`.
The only new hole, strictly step 1 of the original argument, with source, full proof
in words, searches, and the original restriction/Leray/affine dependencies.

There are no change records because no existing signature or definition was changed.


## Second reading by Y2

1. **Interfaces: pass.** Read the full diff of the existing component module
against the repository. The theorem signature, universes, hypotheses, public
imports and visibility are byte for byte unchanged. The other three modules
are new; each theorem signature also matches its node's `lean.statement`
byte for byte. There are no delivered definitions or forced adaptations.

2. **Proof and trust: pass as a decomposition.** Independently compiled all
four modules through `lcompile.py --all` (2.6, 4.2, 19.6 and 5.9 seconds,
no warnings). Scratch copies with `#print axioms` verified that
`rightDerivedFunctor_truncated_bottom` uses only `propext`, `Classical.choice`
and `Quot.sound`. The other three theorems additionally use `sorryAx`, as
expected from the named remaining hole and open imported dependencies; none
uses any other axiom. The only direct sorry in the delivery is the whole
public theorem `qcoh_acyclic_inverse_affine_open_vanishing`. No axiom, unsafe,
opaque, implemented_by, extern, holed definition, or arbitrary data witness
was introduced. The final proof composes natural isomorphisms of module
presheaves, so linearity and restriction naturality are part of its type.

3. **New statements: pass.** Read the available local Stacks copies in
`/home/ubuntu/weil-launcher/maint/bp/work/literature/stacks-project/`:
`derived.tex` lemma-negative-vanishing (05TC), `perfect.tex`
lemma-application-nice-K-injective (08D4) and lemma-affine-compare-bounded
(08D5), and `cohomology.tex` lemma-apply-Leray (01F4 (2)). The generic bottom
statement is justified by negative vanishing, double truncation, the natural
single-object comparison and left exactness; it needs enough injectives only
on C, and no Grothendieck assumption on D. The projection statement uses
N=1 and b=i-1, giving exactly the two zero endpoints i and i+1. The remaining
ordinary-sheaf vanishing is strictly the first geometric step, not a rename
of the derived natural comparison. Checked the empty open and zero sheaf;
for f the identity it reduces to affine vanishing. For a nonaffine inverse
image, restriction plus Leray is essential and no affineness of that inverse
image is assumed. For the other two statements checked the zero object,
arbitrary negative cutoff, and an unbounded original object: only its lower
truncation is lifted to D+.

Independently searched with LeanFinder for "Leray vanishing over an affine
target for an acyclic quasicoherent sheaf", Loogle for
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, and `rg` on both Lean roots
for inverse-open vanishing and truncation/bottom comparisons. No existing
inverse-affine-open vanishing declaration was found. The affine-specialized
`affineDerivedSections_truncated_bottom` and
`hypercohomologyLeftEdgeTargetIso` do not have the generic signature here.
Read the existing Leray, derived-open-restriction, open-cohomology and
single-object comparison interfaces. Closing the remaining hole would require
several restriction/equivalence and ordinary-to-total comparison adaptations,
so it is not a few-minute omission. Its prose proof now explicitly includes
that bridge and the node cites the existing statements providing it.

4. **Route and pruning: pass after report repair.** The final theorem uses
only the projection isomorphism and generic bottom comparison. The latter
is fully proved; it replaces the unnecessary full spectral sequence. Read
`dag/units/sk-thm-picard-duality.json`: its `realized.statement` is empty and
its sole realized step is empty, so this replacement removes no realized
unit step. Public imports serve the signatures; imports for proofs remain
plain. Completed the report's list of all nine removed direct imports and
accounted for all nine old proof dependencies. Only `thm-sp-truncation-e2`
is dropped from the argument altogether; global pruning remains a ledger
question, not a claimed module count.

5. **DAG: pass after citation repair.** All four node signatures agree with
Lean. Read each node's proof, proof_deps, origin, source, searches, creation
record and blueprint ancestry. The final node describes the actual asIso
and whiskering composition. Added the existing
`lem-sp-derived-functor-single-identification` citation to the generic bottom
node, and `lem-weil-pbc-exact-functor-bounded-below` to the exact evaluation
step. The remaining vanishing node now also cites those two existing nodes
and `src-right-derived-functor-plus-compatibility` for the explicit bridge
between ordinary and total higher direct images. Recomputed proof_deps as
the union of uses; no new node or hole was added by the second reader.

Changed only the new vanishing theorem's proof docstring, these three new
node proof records, and this report. No Lean signature, definition or proof
body was changed. The closed upper hole and one added lower hole remain a
one-for-one decomposition, with two additional completely proved helper
theorems, not a claim of net sorry progress.
