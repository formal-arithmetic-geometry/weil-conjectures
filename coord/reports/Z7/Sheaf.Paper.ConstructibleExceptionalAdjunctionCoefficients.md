## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.integralTriangulated`
on the exact `finiteTorConstructibleIntegral` predicate, with its existing unrestricted
scheme argument and all signatures unchanged. The proof intersects the existing
triangulated integral constructible predicate with the uniform reduction-Tor property.
It proves isomorphism closure, the common zero interval [0,0], the common shift
interval [a-m,b-m], and extension closure using [min(a,c),max(b,d)]. Each reduction
uses the triangulated and shift witnesses of `scalarReductionDerivedExistence`.

Added the proof-only import `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
The existing proof-only import of `Sheaf.Paper.FiniteCtfTriangulated` now uses
`import all`, to reuse its proved private `tensor_functor`, `amplitude_iso`, and
`amplitude_mono` helpers. These occur only in a theorem proof; no public definition
or signature depends on private declarations. The zero object is written explicitly
inside the proof, without opening an additional global notation scope.

Updated Step 10 and the dependency union of
`lem-sf-constructible-exceptional-adjunction-coefficients` to record this direct closure
argument. The 13-step route for the still-open system existence theorem remains.
The newly explicit support nodes are
`lem-weil-integral-constructible-triangulated` and
`lem-weil-derived-scalar-extension-restriction-adjunction`; no maintainer tool approvals
were added. The quantitative finite-stage closure node was already a dependency.

The complete module compiled cleanly against the current library through
`lcompile.py` on 2026-10-19 in 18.2 seconds. A fresh check in the resumed session
also compiled cleanly in 18.9 seconds before the final proof-local notation adjustment. The saved proof was checked against
the current finite-stage closure theorem, the scalar-reduction exactness interface,
and the definition of `finiteTorConstructibleIntegral`. No definition or statement
changed, and no consumer adaptation is necessary.

## Proved and sorry left

Closed one of the module's original two holes:
`WeilConjectures.ConstructibleExceptionalCoefficients.integralTriangulated`.
Its proof uses the existing integral constructible triangulation theorem, whose
own hole remains the responsibility of its existing node. The finite-stage Tor
closure theorem and the private helpers reused here already have proofs.

One original hole remains, unchanged:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_system`, node
`lem-sf-constructible-exceptional-adjunction-coefficients`. It still requires the
coherent finite/integral adjunction construction, coefficient comparisons, rational
localization, common-stage descent, and compactification refinements specified by
its existing 13-step plan.

Holes closed: 1. Holes added: 0. Split-offs: 0. This is a proof of the integral
triangulation obligation, not a decomposition of the system-existence obligation.

## No longer needed

Removed the direct proof import `Sheaf.Paper.IntegralCtfTriangulated`, and removed
`lem-weil-integral-ctf-triangulated` from this item's Step 10, dependency union, and
old tool-use list. The local proof establishes the required unrestricted predicate
instead of transporting the separately stated finite-field/invertibility version.
This prunes that dependency from this item; other modules still use it, so this is
not a claim that the module has left the targets' entire import closure.

Retained proof-dependency imports added to the shared source during this session.
The other original proof imports describe the unchanged, still-open existence plan
and are retained. No new module or new node was created.

## Where the brief, the DAG or earlier work was wrong

The separate `integral_ctf_isTriangulated` theorem is not directly applicable to the
local `integralTriangulated`: it uses `integralCtfProperty`, binds a finite-field
datum, and assumes residue-field invertibility of the prime, while the local theorem
is on `finiteTorConstructibleIntegral` for every scheme. The finite-stage quantitative
closure theorem and the actual scalar-reduction exactness interface suffice to prove
the local theorem without adding these hypotheses.

Checked the defining Tor-amplitude condition and the common-interval argument against
Stacks `sites-cohomology.tex`, `definition-tor-amplitude` and
`lemma-cone-tor-amplitude` (2), and the existing finite-stage implementation. Zero and
empty schemes require no special hypotheses; all levels are n+1. The unit records
`sk-thm-sf-compatibility` and `sk-thm-sf-tensor-hom` were read and no unit statement or
proof step was bypassed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
