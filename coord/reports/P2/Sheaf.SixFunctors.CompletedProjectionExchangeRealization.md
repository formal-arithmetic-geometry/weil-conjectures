## What changed

Reduced completedProjectionExchangeRealization to three separate mathematical steps:
completedProjectionExchangeDomains (original steps 2--6),
completedProjectionExchangeSystem (steps 7--10), and
completedProjectionExchangePaths (the generator construction in step 11).
The combining proof applies rho.coherence to both canonical paths, cancels the
source comparison to identify their integral arrows, maps the system equality by
total limit, conjugates by the fixed endpoint comparisons, and applies raw
localization. The arbitrary outer-context conclusion is rho.coherence itself.

Moved all existing words/maps/predicates, verbatim, into
Sheaf.SixFunctors.CompletedProjectionExchangeData to avoid an import cycle.
The original module publicly re-exports it. Existing rational and common-stage
proofs landed by X3 during this session are preserved verbatim.
The change record is coord/changes/P2-completed-projection-exchange-interface.md.
No upstream source module, target, original statement or definition body changes.

## Proved and sorry left

Current shared source has one hole, after X3 independently proved the two field
corollaries. Closed the body of
WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeRealization
by a complete Lean reduction. This is a decomposition, not a completed proof
without assumed dependencies. The item module has zero textual holes.

Added three named holes, each the whole proof of a public theorem in its own module:

- WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeDomains
  (lem-sf-completed-projection-exchange-domains): uniform recursive domains and
  constructibility of the two completed endpoints.
- WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeSystem
  (lem-sf-completed-projection-exchange-system): the intrinsic system calculation
  and its open restrictions/proper transposes, for arbitrary system inputs.
- WeilConjectures.CompletedProjectionExchange.completedProjectionExchangePaths
  (lem-sf-completed-projection-exchange-paths): construction of canonical paths,
  with all four word domains supplied; asserts no path equality or domain closure.

The decomposition closes one original hole and adds three lower holes; net -2.
The data interface has zero holes. Each remaining theorem's docstring supplies
its source and the complete argument plan; corresponding new nodes record the
source steps and dependencies. No definition selects data from those holes.

## No longer needed

No mathematical dependency is globally pruned: the original domain/coherence
lemmas remain necessary to the new nodes. No source declaration is removed.
The original module's explicit data imports now live in the publicly re-exported
interface, except IntegralResidueTor and DirectImagesConstructible, which remain
private imports for the preserved field-stage proof. The parent directly needs
only the data interface, the three source-step modules, and the field-stage tools.
All 19 original named tool dependencies remain transitively needed; the residue-Tor
approval is retained directly for the rational corollary.

The following old direct parent proof edges/tool approvals are removed from the
parent's tool_uses because the corresponding argument is now under the new
source-step nodes (they remain dependencies there):

- lem-weil-pbc-ringed-exchange-tensor-coherence
- lem-sf-pullback-tor-amplitude
- lem-sf-tensor-ctf
- lem-sf-open-finite-constructibility-interval
- lem-cbc-compactification-geometry-fibre-bound
- lem-sf-proetale-constructible-origin
- lem-sf-comparison-tor-amplitude
- cor-sf-direct-image-ctf-etale-origin
- cor-sf-direct-image-ctf-nonproper
- lem-pur-normalized-actual-reconstruction-maps
- lem-pur-system-normalized-tensor-closure
- lem-pur-coefficient-system-derived-comparison
- lem-fix-proetale-scalar-mate-normalization
- lem-fix-proper-etale-origin-scalar-isomorphism
- lem-weil-pbc-normalized-etale-origin-witnesses
- lem-coef-compact-support-normalized-realization
- lem-sf-integral-compact-support-constructible
- lem-sf-finite-cover-ctf-locality

No branch of the unit route is bypassed. In particular Stacks 0941 reconstruction,
0GL1 open normalization and 0E48 proper tensor coherence remain in the plan.

## Where the brief, the DAG or earlier work was wrong

The brief initially described three holes, but X3 landed the rational and
common-stage proofs while this session was reviewing dependencies. This delivery
uses the current source, with one integral hole, and preserves those two proofs.
The recorded realization existence theorem gives some operations and realization;
the item is quantified over supplied o and rho. Its coherence field proves
intertwining only after a CanonicalPair is constructed. Domain closure and canonical
path membership do not follow merely by invoking that existence theorem.

Searches: LeanFinder and LeanSearch found no compact-support derived-system diamond
or canonical-path/domain theorem in Mathlib; Loogle confirms generic Functor.map
and congr_map only, and Mathlib grep found no CanonicalPair,
IsNormalizedCoefficientSequence or compactificationProjection. Existing project
realization, normalization, open and ringed coherence interfaces were read.
Blueprint searches found no separate duplicate for the three obligations.
Checked identity/empty opens, zero inputs, equal coefficient indices, and torsion
integral inputs: the new statements add no flatness, separatedness over the base,
faithfulness of evaluation, or invertibility of projection/exchange.

## New nodes

- def-sf-completed-projection-exchange-data attaches the unchanged moved definitions.
- lem-sf-completed-projection-exchange-domains records the finite-level interval,
  normalization, compatible-origin and reconstruction argument, original steps 2--6.
- lem-sf-completed-projection-exchange-system records the pre-limit normalized
  open/proper calculation and compactification pasting, original steps 7--10.
- lem-sf-completed-projection-exchange-paths records only canonical generator
  construction; it takes word domains and makes no equality claim.

Change record: coord/changes/P2-completed-projection-exchange-interface.md.

Validation: the project text parser verifies all existing signatures and new node
signatures. A byte comparison verifies the moved definitions and preserved field
proofs. All five delivered modules compiled successfully through lcompile.py --all.
The original module contains no textual sorry; the three named split modules each
contain exactly one. Delivery preflight remains the final validation before push.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
