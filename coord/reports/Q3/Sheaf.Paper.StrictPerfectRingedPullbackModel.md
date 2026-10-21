## What changed

Completed all three proofs in `Sheaf.Paper.StrictPerfectRingedPullbackModel`.
The finite-free comparison is constructed from the rank-one inverse-image comparison,
sectionwise scalar extension, the sheafification counit and preservation of finite products.
Its uniqueness follows from the sheafification adjunction and extension-of-scalars hom
extensionality. The specified splitting equation is then functoriality and iso cancellation.

For the main theorem, categorical flatness of the tensor unit, closure under finite
products and retracts, and the existing tensor comparison prove site-flatness of each term.
The existing bounded-flat criterion gives source K-flatness; ringed-topos pullback gives
target K-flatness and flat terms. Private proved helpers repeat the existing resolving-class
argument at independent site universes, then identify its comparison with the supplied
`LF` and `epsilon` by uniqueness of left derived functors. Bounds and naturality follow
from additivity and the actual comparison natural transformation.

Single-file server compilation against the current sources passed without errors or warnings
(18.8 seconds, resumed session on 2026-10-21).
Source checks confirm all original theorem headers, public definitions and docstrings
are retained verbatim, all lines fit within 100 columns, and there are no remaining
`sorry` tokens or forbidden declarations.

Updated the existing DAG node's proof, proof dependencies and proof origin to match this
argument. No new public declarations, statement changes, definition changes, consumer
adaptations or changes to the adopted source tree are included.

The delivery preflight required a change record for added scoped helper commands
(`open`, `set_option`, and `omit`). Added
`coord/changes/strict-perfect-ringed-pullback-proof-context.md` with the verbatim
public theorem, the command scopes, and the consumer check: zero downstream Lean
modules, no consumer adaptations, and all existing public definitions unchanged.

## Proved and sorry left

Closed 3 of 3 original holes:

- `SheafOfModules.existsUnique_ringedPullbackFiniteFreeIso`.
- `SheafOfModules.ringedPullback_strictPerfect_splitting`.
- `SheafOfModules.strictPerfectRingedPullbackModel`.

All realize `lem-weil-pbc-strict-perfect-ringed-pullback-model`. Added holes: 0.
Remaining holes in the delivery: 0. Split off: 0. Every private helper has a complete proof.
These are proofs from existing library declarations, not a claim that all imported
mathematics is free of transitive holes.

The public definitions and their statements are preserved. The finite-free object is
still chosen from its uniqueness theorem; no arbitrary unproved existence witness is
used to define data. The proofs include rank zero, the zero ring and the zero complex.

## No longer needed

Removed the unused proof imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
`Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`.
Their node interfaces `def-pur-sheaf-tensor-product` and
`def-weil-pbc-algebraic-inverse-image` remain mathematically necessary and are realized
by the already imported tensor and original algebraic inverse-image APIs.

The proof does not apply `SheafOfModules.ringedTopoiDerivedPullback`:
its site object, site morphism and coefficient universes are identified, whereas this
item keeps them independent. Removed that node from proof dependencies, retaining it
in statement dependencies and retaining its existing public import. Its mathematical
argument is instantiated directly using existing general-universe declarations.
No module is withdrawn or claimed globally prunable.

The pulled-complex flatness and K-flatness are obtained directly from
`lem-weil-pbc-ringed-topos-kflat-pullback`, so no second bounded-flat application or
second finite-free retract flatness argument is required. All original substantive
statement dependencies remain; the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original specialized derived-pullback interface cannot be directly instantiated at
this item's independent universes. The current node now also records
`ringedTopoiDerivedPullbackIndependent`; the saved complete proof below retains its
explicit argument from lower declarations. No mathematical statement is disputed. The proved private resolving-class argument uses
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-weil-pbc-ringed-topos-kflat-pullback` and
`lem-pur-left-derived-from-kflat-class`, all existing results. No new missing lemma
or repair of another module is required.

The previous attempt stopped during delivery worktree checkout, before Lean verification.
The resumed standalone compile takes 18.8 seconds, so no expensive-definition timeout
was reproduced. The first two resumed delivery requests received no answer from the compile
server within 210 seconds; the packet was retained for retry as the brief requires.
A diagnostic copy including the exact standard axiom probe then compiled in 16.8 seconds
and printed `SHEAF-PROBED 11`, with no forbidden axiom or direct-sorry findings. Its only
warning was the standard appended probe line exceeding 100 columns, outside the
delivered source (the delivery tool filters that known probe-only warning).

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
