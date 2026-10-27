## What changed

Implemented `AlgebraicGeometry.tame_trait_quotient_logEtale` without changing its
signature, public imports, or existing docstring. The proof extracts injectivity
from spectrum dominance, proves the fixed subalgebra finite and Noetherian via
its linear embedding into B, proves both canonical spectrum maps finite and
dominant, and obtains completeness from the existing finite-over-complete-local
product theorem. The Noetherian local domain equivalences convert the original
trait hypotheses to DVR instances. The proof then combines an algebraic Kummer
normal form with its canonical divisorial log realization, and derives the full
universal clause from the existing log-smooth composition theorem.

Added two public intermediate theorem modules, each with exactly one named
`sorry`, a matching DAG node, source, and complete proof in words:

- `Sheaf.RingTheory.TameTraitInvariantKummerPresentation` isolates the algebra of
  the invariant DVR and its evaluation-compatible uniformizer presentation.
- `Sheaf.AlgebraicGeometry.TraitKummerDivisorialLogEtale` turns a specified
  polynomial presentation into the canonical divisorial fs log structures and
  the log-etale morphism. It applies to general strictly henselian DVRs without
  completeness, mixed characteristic, or any group action.

Neither intermediate is the item under another name. The first has only
ring-theoretic conclusions; the second takes a concrete Kummer presentation
and has only logarithmic conclusions. The main module supplies all finite-map,
dominance, dimension, principal-ideal and completeness clauses and the actual
log-smooth composition. No definition or existing declaration interface changed.
Only the item's node and the two new nodes are delivered.

Validation: the two new modules compiled in 3.2 s and 2.7 s; the complete main
proof compiled without errors or warnings in 4.3 s. All compiles used lcompile.py
on the project server. The item signature remains verbatim unchanged, and every
Lean line is at most 100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.tame_trait_quotient_logEtale`
(node `lem-per-tame-trait-quotient-log-etale`). There are zero holes left in the
item module.

Added two holes:

- `AlgebraicGeometry.tame_trait_invariant_kummer_presentation`, node
  `lem-per-tame-trait-invariant-kummer-presentation`.
- `AlgebraicGeometry.trait_kummer_divisorial_logEtale`, node
  `lem-per-trait-kummer-divisorial-log-etale`.

This is a decomposition: one original hole closed, two strictly smaller holes
added, for net minus one hole closed. It is not a sorry-free proof of the full
mathematical theorem. All remaining holes are the exact public theorem bodies
`:= by sorry`; none occurs inside a definition or private declaration.

## No longer needed

No mathematical node or module is claimed globally pruned. The original steps
1-7 are retained under the algebraic normal form, step 8 under the general
Kummer divisorial realization, and step 9 is implemented using the existing
composition theorem. The blueprint unit route is preserved.

Removed these direct proof imports from the item because their uses are now in
the two component nodes rather than in its Lean assembly:

- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
- `Mathlib.RingTheory.Ideal.GoingUp`
- `Mathlib.RingTheory.Invariant.Basic`
- `Mathlib.FieldTheory.Galois.Basic`
- `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`
- `WeilConjectures.RingTheory.HenselianLocalRootLifting`
- `Mathlib.FieldTheory.PurelyInseparable.Basic`
- `Sheaf.NumberTheory.DvrGaloisDegreeData`
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`
- `Mathlib.AlgebraicGeometry.Pullbacks`

Kept every public import. Kept the existing direct finite-complete-local and
log-smooth composition imports. Added the DVR TFAE and dimension interfaces and
the two new theorem imports. The item's proof_deps now describe its actual
assembly; each original dependency is retained in the appropriate component.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair was needed. The original dependency
interfaces supply the component algebra and log geometry, but they do not
already construct the compatible rank-one log chart or the entire invariant
DVR normal form in a single application. Those are the two remaining genuine
arguments, now stated independently with all compatibility equations explicit.
The original stage-2 report's note that the uniformizer-presentation node had no
Lean declaration is stale: its current declaration is
`IsDiscreteValuationRing.exists_uniformizer_polynomial_presentation` in
`Sheaf.RingTheory.TotallyRamifiedUniformizerPresentation`.

Read ILO VI 2.1-2.2, printed pp.71-72, and XVI 3.7, printed pp.254-255, plus the
Stacks fixed-field, finite-complete-local, Galois degree and uniformizer-generation
passages. Searches used the prescribed msearch wrapper (LeanSearch, LeanFinder,
Loogle and Mathlib grep), and direct project/DAG searches. No matching theorem
was found. The existing `StrictlyHenselianInvariants` theorem requires a separate
inertia hypothesis and does not provide the tame Kummer normal form. Existing
Kummer local models do not provide the canonical divisorial construction from
this one-variable polynomial presentation.

Edge cases checked: trivial and nonfaithful H (n=1 is allowed), arbitrary action
kernels, imperfect separably closed residue fields, and the empty source in the
universal clause. The intermediate log statement includes n>0, unit n, genuine
uniformizers, injectivity, and evaluation compatibility, so an arbitrary algebra
isomorphism or unrelated log structure cannot substitute for the required map.

## New nodes

`lem-per-tame-trait-invariant-kummer-presentation`, at
`dag/nodes/sec-deligne-laumon-a1/lem-per-tame-trait-invariant-kummer-presentation.json`,
retains the original algebraic steps 1-7 and their declared dependencies. It
states only the invariant DVR, strict henselianity, degree, and explicit Kummer
presentation. Its module is
`Sheaf.RingTheory.TameTraitInvariantKummerPresentation`.

`lem-per-trait-kummer-divisorial-log-etale`, at
`dag/nodes/sec-deligne-laumon-a1/lem-per-trait-kummer-divisorial-log-etale.json`,
retains the rank-one chart calculation of step 8. Its module is
`Sheaf.AlgebraicGeometry.TraitKummerDivisorialLogEtale`. It accepts an explicit
presentation and constructs the canonical logarithmic morphism, without any
quotient-ring conclusions or log-smooth universal clause.

No change record is required: no existing statement, definition, public import,
attribute or other module has changed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
