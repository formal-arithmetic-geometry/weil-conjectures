## What changed

Proved `WeilConjectures.SystemProjectionFormula.projection_change` by using the existing
single-refinement clause of `projectionSystemGeneratingEquations`, identifying its forward
comparison with the inverse of the reverse comparison defined in SystemProjectionFormulaMaps,
and pasting the two equations for the canonical graph common refinement. The inverse
identification is a complete private proof cancelling the compositor, equality transport,
proper/open gamma, and identity-push factors. Proper/open support gives all the needed
isomorphisms on arbitrary system inputs. No projection morphism is inverted.

The item gains two private proof imports: Sheaf.SixFunctors.ProjectionSystemCoherence and
Sheaf.SixFunctors.SystemProperOpenSupport. Its public signature and import remain identical. A theorem-scoped unused-section-variable
linter setting retains all its original geometric binders even though the proof needs fewer.
The existing generating-equations theorem imposed an unnecessary coefficient-characteristic
restriction. Removed only that binder in its unclaimed module and dropped that argument at
its single existing caller in ProjectionIntegralCoherenceRealization; the caller's own
signatures are unchanged. The generating theorem's existing hole is retained, with its
stronger characteristic-free domain recorded in its node and change record. The formal
projection map and its mate equalities make sense over arbitrary ringed sites (Stacks 0B56),
and this calculation uses no invertibility of the coefficient prime. Both the node's proof
and its source paragraph explicitly use only tensor naturality and adjunction identities.

Change record: coord/changes/X7-projection-generating-equations-characteristic.md.
The read-only downstream audit found exactly the generating module itself and the one
existing caller. The new proof import does not create an import or DAG cycle. The existing
generating-equations node is used as a tool for the unit's same compactification-independence
step; no unit statement or proof step is bypassed. No new public declaration is introduced.

Validation: all three changed modules compiled successfully through lcompile.py against the
sandbox dependency overlay. The final item compile took 17.6 seconds and the adapted caller
6.7 seconds, with no errors or warnings. The generating dependency also compiled successfully.

## Proved and sorry left

Closed: `WeilConjectures.SystemProjectionFormula.projection_change`
(node lem-pur-system-projection-change-compatibility), the item's sole original hole.
Added holes: zero. Split-off statements: zero.

The only direct sorry in the delivered modules remains the pre-existing
`WeilConjectures.IntegralSystemRealization.projectionSystemGeneratingEquations`
(node lem-sf-projection-system-generating-equations), with the redundant characteristic
hypothesis removed. Its four map equations and proof in words are preserved.
ProjectionIntegralCoherenceRealization has no direct sorry. Dependencies elsewhere may
still have their named holes; this delivery uses their declarations as the stage requires.

## No longer needed

No original Lean import is removed. The item's proof no longer directly needs the planned
lem-sf-projection-refinement-descent (Sheaf.SixFunctors.ProjectionRefinementDescent) or
lem-sfb-ringed-projection-tensor-composition (Sheaf.Paper.RingedProjectionTensorComposition):
the existing intrinsic generating-equations theorem already packages precisely their
single-refinement calculation. They are removed from this node's proof_deps. This does
not assert that these modules are unused by every other parent; no module is withdrawn.
No obsolete tool_uses entry exists to remove.

## Where the brief, the DAG or earlier work was wrong

The DAG planned to redo a local proper/open projection calculation already stated as the
refinement clause of projectionSystemGeneratingEquations. The latter's unused `l ≠ D.p`
binder did not fit this item's correct unrestricted signature. The equation is intrinsic
before total limit and asserts no projection invertibility, so that restriction is
unnecessary. The node's statement_change audits its sole existing DAG citer,
lem-sf-projection-integral-coherence-realization, whose use remains valid after strengthening.
Equal-characteristic coefficients, arbitrary unbounded inputs, identity refinements and
zero inputs remain allowed; the inverse construction is justified by gamma support, not
by coefficient-prime invertibility or a Tor assumption. No target statement changes.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
