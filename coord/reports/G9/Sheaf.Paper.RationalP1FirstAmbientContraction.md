## What changed

Preserved the full signature of `rationalP1_first_ambient_contraction`. Its proof obtains the native
invertibility witnesses together with the normalized unit factorization, transports the normalized
counit's terminal functional, and combines these with supported-kernel evaluation using
`Functor.map_comp`, associativity and substitution. No integration identity is used.

The three new modules isolate different parts of the source calculation:

- `RationalP1UnitFactorization` factors the normalized unit before applying `Rq_*`. It contains
  no counit, trace functional, completed reference or localizing hypothesis on M.
- `RationalP1FirstTraceTransport` changes the terminal functional on
  `Rq_*Rp₂*(p₁*M ⊗ T_W)` to the first projection path. It normalizes the supplied counit
  internally and never inserts a diagonal class or uses a proposed unit.
- `RationalP1SectionEvaluation` evaluates an arbitrary supported-kernel arrow against an
  arbitrary functional at the selected coefficient. It needs no Tate pullback comparison,
  trace compatibility, proposed unit or counit, or integration equation.

The section module also constructs `firstPathComparison` by conjugating the published
pullback comparison, realizes a diagram functional by `firstNativeFunctional`, and constructs
the actual composites `firstKernelInsertion` and `firstTerminalFunctional`. These are real
constructions, with their endpoints fixed before direct image; none chooses an unspecified
object from an existence theorem. The only existential data selected or eliminated by the item proof
are invertibility proofs of fixed arrows. Terminal projection invertibility is selected with
Classical.choose; its type is a proposition, so no object data is chosen.

Existing public interfaces and all global attributes are unchanged. Only private proof imports
were added to the item. The item node records the actual functoriality assembly, and each new
node records its source argument and existing declared dependencies.

Validation: all four modules compiled through lcompile.py. The final assembly kernel check
took about 1.5 seconds after using the native witness interface. Development profiling options
and temporary probes were removed before delivery.

## Proved and sorry left

Closed the direct sorry of
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_ambient_contraction`
(node `lem-sfb-rational-p1-first-ambient-contraction`). This is a decomposition into three
strict subcalculations, not a net hole reduction.

Added three named holes, each in its own module:

- `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_unit_factorization`
  (`lem-sfb-rational-p1-unit-factorization`).
- `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_trace_transport`
  (`lem-sfb-rational-p1-first-trace-transport`).
- `AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation`
  (`lem-sfb-rational-p1-section-evaluation`).

The item has zero direct holes; each new module has one. The four constructed definitions
have zero holes. No axiom or sorry in a definition was introduced.

## No longer needed

None. No existing imports, nodes or modules were pruned. The old general proof dependencies
remain needed by the new subcalculations and moved to their nodes. In particular the
Kunneth, trace compatibility, ringed/module comparison and section coherence arguments
were retained. The blueprint unit's prescribed diagonal and trace route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original plan describes the correct calculation,
but its general ringed-category declarations do not directly instantiate the diagram's
native full-unit normalizations. Those identifications remain in the section and trace items.

A generic coefficient assembly and unit factorization were written and compiled in isolation.
Specializing that entire proof to the bundled coefficient repeatedly exceeded the per-file
limit during kernel conversion. The profiler and expression comparison exposed distinct
`Sheaf.monoidalCategory` and Grothendieck-topology monoidal instance expressions. The final
route fixes the selected coefficient in the new statements and keeps the item assembly as
literal functoriality, avoiding that generic specialization. The normalized unit factorization
is therefore a separate, strictly smaller obligation, with its full algebraic proof in words.
No compile limit was raised and no shared definition or instance was changed.

Searched Mathlib with LeanSearch, LeanFinder, Loogle and source grep, and read both library
roots and the current blueprint. Relevant existing declarations include
`ringedKunnethFactorizations`, `ringedProjectionTensorComposition`,
`ringedProjectionSectionSpecialization`, and `projection_section_normalization`.
`trace_base_change_first` is integral and assumes its trace square;
`SfP1Transport.projectionTraceTransport` concerns ordinary finite etale coefficients.
Neither supplies this rational terminal functional equation. `Functor.map_comp` supplies
the final assembly, but no existing declaration states the entire normalized native unit
factorization.

Edge-case checks covered zero objects, zero kernel arrows and functionals, and coefficient-unit
kernels. The section statement does not fix a diagonal class or trace; terminal transport
never inserts a diagonal class; unit factorization contains no trace or counit. None asserts
that an integral equals identity or assumes the desired adjunction.

## New nodes

`lem-sfb-rational-p1-unit-factorization`: the normalized unit, before direct image, is the
supported-kernel insertion followed by the native tensor-shift and inverse projection/exchange
tail. Its source is the literal ambient unit clause and the First identity's unit calculation.

`lem-sfb-rational-p1-first-trace-transport`: the terminal functional identity and invertibility
of the first projection, with a normalized counit and without unit or diagonal insertion.
The completed reference supplies trace compatibility; its class field is not used.

`lem-sfb-rational-p1-section-evaluation`: supported-kernel evaluation after changing the second
direct-image path to the first, for arbitrary kernel and functional at the selected coefficient.
It also realizes the four genuine comparison and composite constructions described above.

No change records are needed: no other existing module or node was changed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
