## What changed

Proved `CategoryTheory.existsUnique_equivariant_coequalizer_comparison` with its
statement unchanged. Mathlib's `IsColimit.coconePointUniqueUpToIso` supplies the
underlying comparisons, their normalization, and their inverse identities. Two proved
private helpers show that a colimiting image cofork has an epic projection and that
linearity descends through a map whose tensor image is epic. Both tensor hypotheses
are used to prove the forward and inverse components linear. Cofork cancellation
proves forward naturality and uniqueness; `NatIso.ofComponents` assembles the natural
isomorphism and supplies inverse naturality.

Updated the existing node's proof steps to record the Mathlib comparison and the
inverse-naturality argument used by `NatIso.ofComponents`. All dependency nodes and
the unit route are retained. Removed the unused public `RingPresheaf` import; the
change record is `coord/changes/V3-equivariant-coequalizer-imports.md`.

The source read was Stacks `categories.tex`, definition-coequalizers and the following
uniqueness paragraph (Tag 002A). Search of the adopted source library and a fresh
LeanFinder query found comparison/tensor infrastructure, with no theorem proving the
whole natural internal-module comparison. Loogle confirmed the colimit comparison and
its normalization lemmas; Mathlib grep confirmed the existing module and cancellation APIs. The proof uses that infrastructure directly.

## Proved and sorry left

Closed 1 existing hole:
`CategoryTheory.existsUnique_equivariant_coequalizer_comparison`
(node `lem-sfb-equivariant-coequalizer-comparison`).

Added 0 holes. There are no remaining `sorry`s and no new public theorems or nodes.
The two private helpers are proved. This is a proof, not a decomposition.

Validation: `lcompile.py` recompiled the complete module cleanly in 2.0 seconds
(exit code 0), with the pruned imports. `tools/downstream.py` reported 0 downstream
modules, confirming that the public import removal requires no consumer adaptation.

## No longer needed

Removed the direct public import
`WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`: the generic statement and
proof use no construction of rings in presheaves or sheaves. This does not claim that
module is globally unused. No DAG dependency nodes or item modules are withdrawn.
Both declared proof dependencies (`def-sfb-monoidal-category` and
`sk-def-sfb-module-objects`) remain used through their Mathlib declarations.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The old import of `RingPresheaf` was
unnecessary for this generic comparison. Mathlib already packages the uniqueness
argument for coequalizers and derives inverse naturality from forward naturality,
so those steps do not need to be reimplemented component by component.

All arguments are objectwise or arrowwise. An empty indexing category is allowed,
as are arbitrary unrelated universes for the indexing and ambient categories. No
module structure on H and no colimit over J is introduced.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
