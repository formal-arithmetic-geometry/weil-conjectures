## What changed

Started from the assigned quarantined source at
`quarantine/Sheaf/Paper/DiagonalTracePresentationExistence.lean`, preserving its
public import, theorem name, binders and conclusion. During the session the shared
source tree restored this file and its direct dependencies byte for byte from
those archives. Added three proof-only imports.
The proof constructs comparison data, detects splitting invertibility with the
existing `p.base.calculus S` joint conservativity, and proves the two trace
normalizations by cancellation and the biproduct identities. It then applies
finite evaluation and supplies complete-object full faithfulness. Removed the two
local options disabling transparency checks; no shared definition was changed.

Validation: all three new statement modules compiled with `lcompile.py`; the
assembled item compiled successfully in 14.8 seconds with no item warnings. The
original theorem text was compared exactly with the current shared source, and
each new node records its Lean statement verbatim. Delivery preflight performs
the declaration/axiom checks.

The remaining geometric work is separated into three independent statements:
comparison-presentation construction; finite splitting and pre-inverse component
identification; and full faithfulness on the complete trace objects. The second
statement describes the two components before inversion and does not assume or
restate trace normalization. In particular the main proof performs the inverse
cancellation and proves the normalization equations in the whole derived category
of systems, then applies evaluation. No general derived equality is inferred
from separate finite evaluations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTracePresentation` by a
complete proof from the three named intermediate theorems and the existing
semilinear joint-conservativity theorem. This is a decomposition, not a complete
proof of the geometric existence assertion: one original hole is replaced by
three strictly smaller geometric obligations (net two additional holes).

The item module has zero holes. The three holes added are:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceComparisonPresentation`
  (`lem-sfb-diagonal-trace-comparison-presentation`).
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_twistedSplitting_components`
  (`lem-sfb-diagonal-trace-twisted-splitting-components`).
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_completedHom_bijective`
  (`lem-sfb-diagonal-trace-completed-hom-bijection`).

Every new hole is the entire proof of a public theorem in its own module, with
its source, full proof in words, and matching DAG node. No definition chooses
an arbitrary witness from any of these existence theorems.

## No longer needed

No existing import is removed. No existing module or node is withdrawn or
claimed globally unnecessary. The original public comparison-presentation
interface remains necessary, including its quarantined attachment.

`det-sp-tower-classes` is unnecessary for this argument: its record also contains
supported diagonal data that the trace comparison construction does not use. Its
module and declarations are preserved, and no global withdrawal is claimed.

The parent node no longer directly needs `sk-lem-geo-p1-cohomology`, `lem-pur-coefficient-system-derived-comparison`,
`det-sp-coefficient-towers-abelian`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-weil-ringed-tower-pushforward-limit-comparison`, `det-pe-milnor-epimorphic`,
`lem-pur-twist-sheaf-locally-free`, `prop-weil-pbc-direct-image-limits`, or
`lem-weil-pbc-constant-completion-equivalence` as direct proof dependencies.
Those facts remain needed in the appropriate new geometric steps and are
recorded there. None of their existing public imports or declarations is removed.
The parent now directly uses `lem-coef-semilinear-derived-sections` for joint
conservativity and the three new nodes. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

At session start the assigned module and its direct public import were absent
from `lean/`, but preserved at their quarantine paths in the rework rows. The
session used that archived source. The shared source tree subsequently restored
the item, Models, Coefficients, and Presentations byte for byte; all four were
compared against their archives. No module is withdrawn, and absence of an
importer is never used as a pruning argument.

`det-sp-tower-classes` records a structure, not a theorem asserting that the
structure has an inhabitant. The trace Presentation and Model declarations also
package data without asserting existence. Thus these records do not directly
solve the original existence goal. The new construction theorem makes that
remaining task explicit rather than assuming inhabitance or selecting hollow data.

The completeness step retains the hypothesis that l is invertible on S, so the
compatible-root trivialization used in its proof applies on both S and X after
pulling the unit back along f. Edge cases include n=0 (the positive exponent is
n+1), empty schemes (the categorical cancellation remains valid), and an arbitrary
specified projective-line model (its equality is retained by the construction).

Delivery-tool failure: the required command
`python3 /home/ubuntu/weil-launcher/deliver3.py N1 Sheaf.Paper.DiagonalTracePresentationExistence`
was run twice. Both runs report all four packet modules as compiled, then refuse
with `COMPILES WITH WARNINGS (local), nothing pushed`. The only warnings are three
cached unused-simp diagnostics from the private overlay of
`Sheaf.AlgebraicGeometry.SfP1ChartExchange`: `ordinaryFinitePullback`,
`ordinaryFiniteLine`, and `ordinaryFiniteDegreeZero` at lines 565--566. The
current shared source at those lines already removes all three arguments.
The second delivery returns the identical cached output immediately. The broad
warning check in `deliver3.py` includes these dependency diagnostics rather than
only warnings from packet modules. The item itself separately compiled without
warnings in 14.8 seconds. The dependency's current claim holder is B2; no interface
change in this packet forces an adaptation of that module. No launcher file,
cache, warning gate, or B2 module was edited, and no warning was suppressed.
Nothing was pushed. The complete compiling packet is retained in this sandbox
for delivery after the tool's cached-diagnostic issue is resolved.

Resumed-session verification (2026-10-26T16:20:42+00:00): the required initial delivery check again
returned exit 1 at the local warning gate, before pushing. It reported all four
packet modules as compiled and replayed the same three dependency warnings from
private-overlay revision `8a59854e60a5d95469ddb3c91fa8ea3a531046b5`.
The current shared `SfP1ChartExchange.lean` has already removed these three
arguments from the `simp only` list after its `dsimp only` step. The delivery
script's line 313 rejects any warning in the combined output, including cached
dependency diagnostics. The compile client provides no supported refresh option.
The launcher scripts and their caches were left untouched. This is a delivery-tool
failure; the proof packet is preserved unchanged for retry after its repair.


## New nodes

`lem-sfb-diagonal-trace-comparison-presentation` constructs only the normalized
geometric and limit comparisons, preserving the specified model. Its source is
paragraph (1) of the latest diagonal trace proof and the limit construction in
the same blueprint unit. It asserts no invertible splitting or Hom bijection.

`lem-sfb-diagonal-trace-twisted-splitting-components` states finite invertibility
and the unit/Chern component equations for positive twisting and shifting,
before inverting the splitting. Its source is the same paragraph's finite
decomposition and tensor/dual cancellation. The main proof supplies the trace
normalization from these component equations.

`lem-sfb-diagonal-trace-completed-hom-bijection` specializes the completed-object
restriction equivalence to the two complete trace objects, independently of the
splitting. Its source is the same paragraph's completeness argument, Stacks
099I and 099L. Searches by LeanSearch, LeanFinder, Loogle and grep/rg found the categorical
building blocks and the general completeness equivalence, but no exact geometric
presentation-existence or specialized comparison theorem. All three nodes record
the searches. No shared interface changes or forced adaptations are made.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
