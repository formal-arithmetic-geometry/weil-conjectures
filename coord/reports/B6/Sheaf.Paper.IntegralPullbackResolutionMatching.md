## What changed

Replaced the sole local hole of `WeilConjectures.integralPullbackResolutionMatching`
with a compiling Lean proof. All four original public declaration signatures and
all public imports are unchanged. The proof uses the defining choice of K-flat
resolution, the explicit inverse-image comparison formula, transport of a counit
identity along that resolution, the adjunction triangle identity, and naturality
of the whole-tower counit and finite tensor unit. Three proved private helpers
record these categorical calculations. No definition or existing statement changes.

The separate source calculation on a flat-term K-flat complex is retained in
`Sheaf.Paper.IntegralPullbackReductionCounit`, as
`WeilConjectures.integralPullbackKFlatReductionCounit`. It has no constructible
object N, first scheme map k, tower C_k, resolution q, chosen representative, or
eta. It computes the explicit Roos lift against the reduction unit on P, prior
to transporting through a resolution or composing with a second quotient-system
map. The main proof performs both of those remaining operations in Lean. This
is a decomposition, not a sorry-free proof of the source calculation.

The item's DAG proof is updated to those four steps, with a new node for the
K-flat source calculation. The new theorem has its own source and a full proof
in words; its whole Lean proof is `by sorry`. A change record documents the
new public declaration and its sole consumer.

## Proved and sorry left

Original local hole closed: `WeilConjectures.integralPullbackResolutionMatching`,
node `lem-trf-integral-pullback-resolution-matching` (1 of 1). No local hole remains
in the item module. Its three private helpers are completely proved:
`counitIdentity_transport`, `unit_map_counit`, and `chosenResolution_formula`.

One new hole remains: `WeilConjectures.integralPullbackKFlatReductionCounit`,
node `lem-trf-integral-pullback-reduction-counit`, module
`Sheaf.Paper.IntegralPullbackReductionCounit`. It is the whole-system reduction-unit
calculation on a good complex, a strict part of the original resolution-matching
argument. Thus the delivery closes one original hole and adds one hole: direct
net zero, counted as a decomposition. Existing sorried dependencies are not
claimed proved. Closure-wide ledger counts belong to the project's pinned
baseline and are not inferred from this direct count.

Both modules were compiled individually while developing the proof. The latest
individual checks compiled the item in 13.9 seconds and the auxiliary module in
3.8 seconds, with no errors or warnings. A full overlay compile also passed both
modules. Final packet validation is recorded by deliver3.py. No target file,
statement, or definition changed, and no new data is selected from an unproved
mere-existence theorem.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.TraceFormula.IntegralConeCounitRealization`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The imported APIs needed by the item's explicit choice formula are already
publicly reachable through its original public imports. The source arguments for
coefficient adjunction, strict Roos normalization, and cone-counit realization now
belong to the new reduction-unit lemma. Its statement needs only its two public
interface imports. The six private imports for that future source proof were
also removed from the new module: IntegralConeCounitRealization,
DiagramSiteRealization, PreDerivedAdjointFunctorsGeneral,
DerivedChangeOfRingsCochainModel, ProEtaleCountableProductsExact and
StrictRoosComparison (with the same full module names listed above). Their
results remain in that node's proof plan; the next proof imports what it uses.
They are not asserted mathematically unnecessary to that lemma or to the
project's global proof.

The item's direct proof edges to the original long normalization argument are
replaced by `lem-trf-integral-pullback-reduction-counit` plus the original
comparison and tensor-unit interfaces used by its Lean proof. The seven original
top-level tool approvals are withdrawn from this node: pre-derived adjunctions,
ringed strict-tower limit, levelwise abelian towers, diagram-site realization,
derived change of rings, strict Roos comparison, and exact pro-etale products.
Those generic results are still listed in the new source calculation's proof
where needed. No global pruning is claimed for them. The unit record
`sk-thm-trace-transport` has no realized nodes for its statement or proof steps;
this decomposition stays within the same unit and source route.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false intermediate claim was used.
The DAG's seven-step plan was reorganized into its independent K-flat source
calculation and the resolution/naturality assembly. The latter is now formalized;
the former remains the single explicit source hole. The existing isomorphism-derived-pullback
normalization theorem requires extra coefficient-system coherence, absent from
this statement, and gives no equality with an arbitrary recorded F.realization;
it does not directly replace the K-flat source calculation. The existing cone-counit
lemma alone does not instantiate all of the presentation, strict generator and
normalization identities in one application.

The inherited sandbox contained unfinished experiments with unresolved local
names and a separately reconstructed resolution choice. Extracting the defining
choices directly with `extract_lets` avoids a different choice proof/instance
from being compared definitionally. Explicit universe arguments for the flatness
comparison resolved its universe metavariables. No definition repair or timeout
increase was needed. Debugging traces and partial proofs were removed from the
delivery modules; scratch experiments are not delivered.

Repeated provider interruptions did not change the original sandbox or budget.
A resumed compile request with a mistyped path received no server answer; the
correct packet compile is retried through the required tool. No delivery push
had been started at that point. The tools and budget metadata were not modified. The first mandatory dry run
reported a new split-policy clock of 18 of 120 minutes despite retained search
records starting at 2026-10-19T07:00:04Z. This resumption is B6,
Sheaf.Paper.IntegralPullbackResolutionMatching; the supplied prior outcome was a
provider HTTP 429, with no other attempt identifier. Work continued after the
rejection. The next full preflight rejected the new node because its search
record omitted the LeanSearch query already run at 2026-10-19T09:23:35Z. The actual
logged query and results were added; no new search result was invented. Nothing
had been pushed. The composite-adjunction unit calculation was also proved and
compiled in scratch, including its specialization to the actual coefficient
system. It confirms that categorical step of the source plan; it does not close
the remaining strict normalization calculation and is not delivered as an unused
helper. The corrected dry run then passed all preflight checks (CODEX).
The final import-pruned packet is recompiled and checked again before pushing.

## New nodes

`lem-trf-integral-pullback-reduction-counit`: the reduction-unit counit computation
on a flat-term K-flat complex, extracted from steps 1, 3 and 5 of the item's
source argument. Its four proof steps retain simultaneous quotient presentation,
whole-diagram derived coefficient adjunction, strict generator normalization,
and K-injective-normalized cone-counit realization. The zero complex gives zero
maps on both sides; the identity scheme map gives the ordinary reduction-unit
calculation. No claim is made that unrelated levelwise equalities alone detect
the asserted whole-derived-tower equality. This is the one new source hole.

Change record: `coord/changes/B6-integral-pullback-reduction-counit.md`.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
