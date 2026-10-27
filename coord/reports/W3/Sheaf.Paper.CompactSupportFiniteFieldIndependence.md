## What changed

Proved `WeilConjectures.sfCompactSupportFiniteFieldIndependence` in
`Sheaf.Paper.CompactSupportFiniteFieldIndependence`, with its statement unchanged.
The proof chooses the prescribed normalized integral and rational comparisons from
`sfCompactSupportNormalizedScalarIsomorphisms`, obtains their tower equation from
`sfCompactSupportNormalizedScalarDescent`, and builds the existing
`StageSystem.Morphism` on the recorded coefficient systems. The finite object formula
identifies its values with the previously constructed compact-support values.
Functoriality then proves all four comparison and representative laws.
The file-local instance-size and transparency options follow those of the normalized
comparison interfaces; they expose no new public instances or mathematical data.

The two existing public imports stay unchanged. The only private proof import is
`Sheaf.Paper.CompactSupportNormalizedScalarDescent`, which also supplies the
isomorphism theorem and the scalar-composition interface. The node proof and its
proof dependencies now describe the concrete assembly. No public declaration,
definition or signature changes, no adapted consumers, and no new modules.

Searches through the prescribed `msearch.py` were run with Lean Finder (coherent
finite-stage functors descending to pair categories), Loogle
(`CategoryTheory.Functor.mapIso`), and grep (compact-support/scalar compatibility).
Lean Finder returned unrelated finite-diagram results; Loogle provided the ordinary
functorial isomorphism lemmas; grep found no matching Mathlib theorem. Reading the
existing project interfaces located the complete construction used here.
The first server compile accepted the full proof in 15.3 seconds, with only three
unused simp-argument warnings, which were then removed. The final compile passed
cleanly in 10.9 seconds. Import-direction checking
permits the new proof import. A source check confirms the complete theorem signature
is unchanged, all Lean lines are at most 100 characters, and the node's proof_deps
is exactly the union of its proof-step uses.

The construction is uniform in the input: repeated fields and identity arrows use
the existing quotient identities and inverse beta cancellation; zero objects and
empty schemes require no additional choices or nonemptiness assumptions. The
coefficient comparison theorem retains arbitrary ramification and both universes;
no extra Tor, flatness, or finite-base-field hypothesis is introduced.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.sfCompactSupportFiniteFieldIndependence`
(node `lem-weil-compact-support-finite-field-independence`).
There are zero holes left in the item and zero new holes or split-off statements.
The two imported normalized scalar theorems remain their existing downstream items;
this delivery proves the assigned theorem from their declarations as required.

## No longer needed

Removed private imports `Sheaf.Paper.BasicOperationsCoefficientReduction`,
`Sheaf.Paper.QcqsCompactSupportRealization`,
`Sheaf.Paper.SfRationalizationKaroubi` and
`Sheaf.Paper.SfScalarExtensionComposition`. The last three interfaces are already
available through the action or scalar-descent prerequisites. The large basic-operation
assembly theorem is unnecessary: its normalized scalar ingredients suffice.

Removed the direct proof dependency `lem-weil-scalar-extension-composition`; its
coherence is already used within the normalized-scalar-descent theorem. The direct
proof dependency `lem-sbc-coherent-pair-functor-descent` and the corresponding abstract
module `Sheaf.CategoryTheory.StageSystemFunctorDescent` are unnecessary here: the
existing `StageSystem.Morphism.functor` supplies the actual quotient functor, with
its proved representative formula, directly through the action interface. This
prunes the extra abstract transport, not the concrete descent construction.
Removed the obsolete top-level tool approvals `lem-fix-operation-reduction` and
`lem-sbc-coherent-pair-functor-descent`; neither theorem is invoked directly.
No Lean module is withdrawn, and no claim is made that these modules are globally
unused. The unit record has no realized steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The old DAG step 2 proposed replacing identity transitions by identities and
conjugating all associators. The existing StageSystem quotient already handles
non-strict transitions: its morphism constructor requires only the tower equation.
The current generic descent node's own Lean interface explicitly documents the
same fact. Hence this normalization is unnecessary. The old proof imports did not
include the two declared normalized comparison dependencies; the new proof imports
their scalar-descent module.

The latest blueprint snapshot was checked: the historical assigned node and its
`sk-def-sf-operations` directory are absent there. The current DAG and assigned Lean
statement remain the contract; this delivery changes neither mathematical statement
nor unit route.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
