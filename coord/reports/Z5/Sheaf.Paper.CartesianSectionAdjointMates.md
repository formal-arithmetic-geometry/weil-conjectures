## What changed

Replaced the single hole in
`WeilConjectures.CartesianSectionAdjoint.cartesianSectionAdjointMates` by an explicit
assembly from the existing finite normalized/enriched realization, finite exceptional
comparison, and system transpose-coherence theorems. All existing declaration signatures,
public imports, definitions, and docstrings are preserved.

Added two proved private helpers. `realization_mate_evaluation` proves the requested mate
evaluation formula directly from counit compatibility, naturality, the finite Hom
bijection, and `conjugateEquiv_counit`. `realization_etale_origin` compares a transported
right adjoint with the specified `r.G` by `rightAdjointUniq`; the unit/naturality equation
and inverse comparison yield the exact `EtaleOrigin.transpose` formula.

The geometric presentation step is split into the new theorem
`WeilConjectures.CartesianSectionAdjoint.normalizedSupportEtalePresentation`, in its own
module and node. It assumes only an actual support presentation and normalized left
restriction, constructs the ambient étale adjunction, and restricts its transported
right adjoint with the prescribed Hom action. It neither assumes a normalized right
adjoint nor asserts enrichment, finite mates, transpose coherence, or inverse limits.
The proof combining this step with the existing realization is complete Lean.

Validation: the required `lcompile.py --all` check compiled both delivered modules
in import order, exit code 0, with no errors or warnings. The delivered public
signatures and definition bodies were compared against the library source and
remain identical. Both node proof dependency lists equal their proof-step uses;
the new node does not create a dependency cycle back to itself.

The derived-limit inverse equations are obtained by functoriality from the actual
`Enriched.iso` identities. The degree-zero equations are the actual adjunction Hom
formulas. No equality of system maps is inferred from equality of finite evaluations.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CartesianSectionAdjoint.cartesianSectionAdjointMates`
(node `lem-coef-cartesian-section-adjoint-mates`). Both private helpers have complete
proofs. There are zero remaining holes in the assigned module.

Added one hole:
`WeilConjectures.CartesianSectionAdjoint.normalizedSupportEtalePresentation`
(node `lem-coef-normalized-support-etale-presentation`), with its source and complete
proof plan in the declaration docstring and node. This is a decomposition: one upper
hole closed, one strictly smaller geometric presentation step split off, net zero holes
closed. The pre-existing imported theorem holes remain with their owners.

Source check: Zheng Lemmas 4.10, 5.16 and 5.22 give the ordinary evaluated
direct-image, support/free-insertion and exceptional comparisons. The stronger
levelwise finite-Tor normalized transport remains the explicitly named project
descent step, not a claim extracted from those lemmas alone.

The new statement was checked on identity morphisms, equal and first positive coefficient
indices, zero systems, and empty schemes. Its normalized domain retains separate finite
bounds at each level. Its right functor is a concrete composite and full-subcategory lift,
not an arbitrary witness used to define data. No definition contains a hole or chooses an
arbitrary object from a holed mere-existence theorem.

## No longer needed

Removed the following direct private proof imports from the assigned module:

- `Sheaf.Paper.FreeInsertionCompactSupportCoherence`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.SystemCompactSupportProjection`
- `Sheaf.Paper.SystemEnrichedProjectionAdjunction`
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`

Their construction work is already packaged by the existing realization theorem or the
new presentation step. The direct dependency on
`lem-coef-system-enriched-projection-adjunction` is replaced by
`lem-coef-finite-adjunction-diagram-realization`, which supplies exactly the required
`Enriched` structure. `lem-coef-semilinear-derived-sections` is also no longer invoked
directly. The free-insertion, normalized-descent, compact-support-projection,
internal-Hom-representability and étale-adjoint nodes remain explicit proof dependencies
of the new presentation step. The coherence node remains directly used by the parent.

The only direct importer, `Sheaf.Paper.RamifiedScalarSystemTranspose`, retains the
identical public interface; its source requires no adaptation.

No node, module or declaration is withdrawn. No whole-library pruning is claimed:
several removed direct imports remain transitively needed by the existing construction
or the new node. The source-library boundary is respected without source-tree edits.

## Where the brief, the DAG or earlier work was wrong

The original DAG does not mention that
`FiniteAdjunctionDiagram.finiteAdjunctionDiagramRealization` already supplies the required
normalized realization and enriched package. Its detailed construction need not be
repeated in this parent. That existing theorem does not provide `EtaleOrigin`, however;
its statement alone cannot discharge that clause. The separate presentation theorem
records this missing bridge rather than treating it as an implicit consequence.

The existing transpose-coherence theorem applies with the pro-étale selector. Its
coefficient sheaf and quotient transitions elaborate to the existing integral coefficient
sheaf definitions. Explicit over-category morphism-property instances are needed in the
specialization because the file disables backward transparency.

The unit `sk-prop-sf-biduality-general` has no realized step bindings to bypass. The
replacement finite realization is from the same unit; the original geometric descent
route is retained by the new node. No target statement or mathematical claim is weakened.

## New nodes

`lem-coef-normalized-support-etale-presentation` states the ordinary étale origin and
transported normalized adjunction for a given actual left restriction. Its proof uses
system internal-Hom representability, ordinary system compact-support projection,
étale-system adjoint existence, free insertion and levelwise normalized descent, followed
by natural Hom bijections. Mathlib searches found categorical restriction/uniqueness
lemmas but no geometric statement. The blueprint search found no exact duplicate.

Change record: `coord/changes/Z5-normalized-support-etale-presentation.md`.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
