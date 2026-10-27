## What changed

Replaced the sole hole in `Sheaf.Paper.RationalP1KernelContractions` by two
pointwise ambient calculations. The proof exposes each full-subcategory composite as
an ambient composite. It specializes the existing unit/counit normalization at M and
push(M) for the first calculation, and at exceptional(K) and K for the second. It
then applies the corresponding ambient lemma, with explicit ambient endomorphism
types so the restricted-functor objects reduce to their underlying objects.

Added `Sheaf.Paper.RationalP1FirstAmbientContraction` and
`Sheaf.Paper.RationalP1SecondAmbientContraction`, each stating one kernel calculation
at one raw derived object. Each takes two ambient arrows and their existing pointwise
normalization predicates, which fix all map data by the canonical formulas. Neither
takes a pair of natural transformations or an adjunction. They omit the completed-limit
and cycle-system assumptions: trace normalization and naturality in the class suffice
for these calculations before integration. Each module has one public named remaining
theorem with its source and full natural-language proof. The item imports both privately.
Its existing declaration signature and public imports are unchanged.

All three files explicitly enable respectTransparency locally. The new statements keep
the derived functors, twist and projection aliases folded during elaboration. Profiling
showed that writing out unitComponent and counitComponent applications inside the
composite incurred expensive kernel conversions. Using the already existing pointwise
normalization interface avoids those conversions without changing the maps prescribed
by the hypotheses. No shared definition or global option is changed.

Validation: lcompile.py accepted both new modules and the main module against the
sandbox dependencies. The final main proof compiled in 11.3 seconds. All development
profiling, diagnostics and printing options have been removed.

Read the current rework row before copying the item. The current source is present; its
original Lean attachment, class, traces, and dependent constructions have been preserved.
No quarantined source was withdrawn or listed for deletion.

## Proved and sorry left

This is a decomposition, not a completed geometric proof: one old hole was closed and two
strictly smaller holes were added (net change: one additional hole).

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_kernel_contractions`
(node `lem-rational-p1-kernel-contractions`). Its restriction and assembly proof contains
no sorry. It is proved from the following two new remaining theorems:

- `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_ambient_contraction`
  (`lem-sfb-rational-p1-first-ambient-contraction`): one sorry, only the first contraction.
- `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_second_ambient_contraction`
  (`lem-sfb-rational-p1-second-ambient-contraction`): one sorry, only the second contraction.

There are zero sorries left in the item and two in this delivery's new modules. No other
existing theorem or definition was changed. Neither new theorem restates both contractions
or quantifies over a normalized unit/counit pair. The first uses the two Kunneth
factorizations; the second instead uses exchange/tensor coherence on q*K(1)[2].

Edge cases checked in the statements: zero M and K give zero composites, an empty base adds
no nonemptiness requirement, both finite-extension and algebraic-closure coefficient
branches are retained, and existential normalization witnesses choose only proofs of
invertibility of fixed arrows. No arbitrary data are extracted from an existence theorem.
No integration equation, twisted adjunction, or triangle identity is used by the assembly
proof or assumed in the geometric proof plans.

## No longer needed

No modules are withdrawn or globally pruned. No original Lean import is removed. The unit's
route and both of its kernel calculations are preserved.

The item's immediate proof dependencies are now its unit/counit normalization interface,
the ambient-component interface, and the two new ambient lemmas. Its earlier geometric
proof dependencies are retained where needed in those new nodes: the module/ringed-topos
comparison, properness, localizing projection formula, derived pushforward composition,
exchange/tensor coherence, coefficient trace compatibility, Kunneth factorizations, and
projection/section coherence. These are delegated obligations, not pruned mathematics.
The Kunneth factorization is needed only in the first new node. The generic
`def-weil-pbc-composite-adjunction` and `def-weil-pbc-adjunction-mate` are no longer separate
immediate citations of this item: the already-stated Kunneth/exchange lemmas incorporate
their adjunction machinery. This does not claim those notions or their other consumers
are globally unused.
The former immediate citations `sk-def-sfb-module-objects` and
`sk-def-sfb-module-pushforward-pullback` describe the objects and functors already
present in the ambient-component interface. They need no independent proof step here;
the definitions themselves remain part of that interface and are not withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error or counterexample was found. The existing plan describes the geometric
calculations but does not itself give their specialization as equations between the
literal ambient maps. The new nodes isolate those two distinct calculations; the real
Lean proof above them specializes normalization and handles the full-subcategory interfaces.
The new trace-square proof plans explain why completed-limit assumptions are unnecessary:
pullback preserves the normalized unit/Chern splitting, hence its inverse and constant
projection defining the trace, and the reference/scalar squares transport that equality.

## New nodes

`lem-sfb-rational-p1-first-ambient-contraction`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-rational-p1-first-ambient-contraction.json`,
records the single-object first ambient calculation. Its source is the current blueprint
triangle proof, First identity before integration. Its proof retains the two Kunneth
factorizations, normalized trace base change, and projection/section source normalization.

`lem-sfb-rational-p1-second-ambient-contraction`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-rational-p1-second-ambient-contraction.json`,
records the single-object second ambient calculation. Its source is the same proof's Second
identity before integration. Its proof retains the exchange/tensor square, Cartesian Tate
comparisons, the even shift sign, and the second projection's source normalization.

Both nodes record LeanSearch, LeanFinder/Loogle, grep, and the blueprint duplicate search.
No existing statement or definition changed, so no change record or consumer adaptation
is required.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
