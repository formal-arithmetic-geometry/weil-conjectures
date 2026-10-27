## What changed

Closed all ten original holes using the existing stated dependencies. The main theorem
uses normalized_continuous_set_kan_evaluation for normalization, uniqueness and bijections
on weakly contractible affines. Its Lean proof refines the equalizer and image sieves by
an affine weakly contractible covering and applies Sheaf.isLocallyBijective_iff_isIso.
The coefficient, product, scheme-pullback and coherence clauses then follow from
normalized_continuousSetComparison_coherence; invertibility follows by cancelling the
invertible realized source map. The specification is Exists.choose_spec, the component
formula is rfl, and the discrete clause comes from continuousSet_descent_components.

The existing definitions had to move to Sheaf.Paper.ContinuousSetConstructions to make
these dependencies importable without cycles. All fifteen moved declarations keep their
names, signatures, visibility and concrete non-theorem bodies. The prerequisite sheaf
and direct-image-naturality theorems are proved in that module, respectively by Mathlib
fpqc descent and the first-projection identity for base change. The original item publicly
re-exports this module, preserving its public API. The three dependency modules change
only their construction import. Five existing definition-node attachments follow the move;
the realization node records the actual assembly and removes obsolete direct tool uses.

Sources read: HRS Example 3.1 and the following pullback paragraph, p. 6; Bhatt--Scholze
Lemmas 4.2.12 and 4.2.13, pp. 30--31. No unit statement or route changes. The argument
uses no nonemptiness assumption on schemes or coefficients; the covering-sieve proof
works for an empty covering, and the existing product lemma includes the empty product.

Change record: coord/changes/continuous-set-constructions-extraction.md.

Validation: all five sandbox Lean modules compile through lcompile.py --all. The item
also compiles after removing its unused imports and the unused simp argument. The normal
server delivery preflight checks axioms and the combined interface changes.

## Proved and sorry left

Closed 10 original holes, all in namespace AlgebraicGeometry.ProEtale:

- `continuousSetPresheaf_isSheaf`.
- `existsUnique_continuousSetRealization`.
- `continuousSetRealizationHom_spec`.
- `continuousSetDirectImage_naturality`.
- `continuousSetRealization_natural`.
- `continuousSetRealization_products`.
- `continuousSetRealization_pullback`.
- `continuousSetRealization_coherence`.
- `continuousSetRealization_discrete`.
- `continuousSetRealization_components`.

Zero holes remain in the assigned module or ContinuousSetConstructions. No holes are
added, and no statement is split off. The moved prerequisite theorems are counted among
the original ten, not as new proofs of newly introduced statements.

The packet retains the two pre-existing, unchanged dependency holes:

- `AlgebraicGeometry.ProEtale.normalized_continuous_set_kan_evaluation`
  (lem-sfb-normalized-continuous-set-kan-evaluation; R7).
- `AlgebraicGeometry.ProEtale.normalized_continuousSetComparison_coherence`
  (lem-sfb-normalized-continuous-set-comparison-coherence; R6).

ContinuousSetDescentComponents has no holes. Those two existing supporting statements
are strictly separate results already declared by the DAG. The assigned module's proof
from them is complete Lean, including the local-to-global isomorphism argument.

## No longer needed

No module is withdrawn or globally pruned. RelativeProfiniteTestLabels remains needed
through the Kan and coherence dependencies, but is no longer a direct proof dependency
of the realization node: the Kan lemma already includes its normalized-map conclusion.

Removed direct proof imports from the item:

- Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite (component formula is rfl).
- Sheaf.CategoryTheory.SiteInverseImageTensor (encapsulated by comparison coherence).
- Sheaf.Paper.ProEtaleSheafificationWcontractibleSections (encapsulated by Kan evaluation).
- Sheaf.Paper.ProfiniteTestObjectFunctor (encapsulated by Kan evaluation).
- Mathlib.AlgebraicGeometry.Limits (only shared constructions need pullbacks).

The five former Mathlib/WeilConjectures public imports and ProfinitePointPullback are now
public imports of ContinuousSetConstructions, hence remain visible to every existing
importer through the item's single public construction import. This is relocation of
imports, not loss of their public API. The three supporting modules replace their public
item import by the public construction import, since their statements use only that API.
The main module adds only private proof imports for the existing Kan, coherence and
descent-components statements, while retaining the affine-cover and local-bijection imports.

Removed obsolete direct tool approvals from the realization node (the underlying nodes
remain available and may still be needed by the supporting lemmas):

- lem-cbc-set-presheaf-sheafification-local-bijection.
- lem-pe-spectral-components-profinite.
- lem-sfb-compact-hausdorff-surjection-quotient.
- lem-sfb-profinite-coherent-sheaf-criterion.
- lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction.
- lem-weil-pbc-left-exact-site-inverse-image-tensor.
- lem-weil-pbc-locally-constant-prime-spectrum.
- lem-weil-pbc-proetale-sheafification-wcontractible-sections.
- lem-weil-pbc-profinite-point-pullback.
- lem-weil-pbc-profinite-test-object-functor.
- lem-weil-pbc-qcqs-scheme-spectral.
- lem-weil-pbc-scheme-coproduct-family.

## Where the brief, the DAG or earlier work was wrong

The mathematical proof-dependency statements fit. Their original Lean imports made the
DAG assembly impossible: all three supporting modules publicly imported the assigned
module solely for its prerequisite definitions. This required extracting the definitions
before importing the existing lemmas back into the assigned module. No new mathematical
lemma or changed statement was needed. The sheaf property's direct Mathlib proof also
avoids a circular dependency on the bundled continuousSetSheaf in descent-components.

## Forced adaptations

Sheaf.Paper.NormalizedContinuousSetComparisonCoherence is held by R6. Its original
line 8 is `public import Sheaf.Paper.TotallyDisconnectedCoefficientRealization`.
Compiling originals against the changed item with lcompile.py --all reports:
`the modules import one another in a cycle: Sheaf.Paper.NormalizedContinuousSetComparisonCoherence, Sheaf.Paper.TotallyDisconnectedCoefficientRealization`.
Change that line to `public import Sheaf.Paper.ContinuousSetConstructions`.

Sheaf.Paper.NormalizedContinuousSetKanEvaluation is held by R7. Its original line 12
has the same item import. The corresponding compile reports:
`the modules import one another in a cycle: Sheaf.Paper.NormalizedContinuousSetKanEvaluation, Sheaf.Paper.TotallyDisconnectedCoefficientRealization`.
Change that line to the same construction import. Their theorem signatures, public
visibility, remaining imports and proof bodies stay identical. The adaptations compile.
ContinuousSetDescentComponents is unclaimed; its line 8 needs the same import update.

## New nodes

lem-sfb-continuous-set-proetale-descent records the already-existing, now-proved theorem
AlgebraicGeometry.ProEtale.continuousSetPresheaf_isSheaf in ContinuousSetConstructions.
It is strictly the prerequisite sheaf property, not the realization isomorphism. It adds
no Lean declaration and no hole. It is separated from the larger descent-components
conjunction because that theorem's signature already uses the bundled sheaf. The node
records the direct fpqc restriction proof, with the original source and actual searches.
The first delivery preflight required a new-node attachment for a new shared module;
existing definition-node relocations alone do not satisfy its module ownership gate.
Change record: coord/changes/continuous-set-constructions-extraction.md.

## Forced adaptations

### Sheaf.Paper.NormalizedContinuousSetComparisonCoherence
Original already fails against the compiled baseline (pre-existing):
```
no answer from the compile server within 645 s (server busy or unreachable): run it again
```
Adapted module compiled in the delivered set.

### Sheaf.Paper.NormalizedContinuousSetKanEvaluation
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
