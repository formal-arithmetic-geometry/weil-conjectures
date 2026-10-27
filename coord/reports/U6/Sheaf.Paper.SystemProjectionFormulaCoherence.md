## What changed

The assigned module proves `system_projection_formula_coherence` by assembling two
strictly smaller concrete-word obligations: compatibility with change of a single
compactification and compatibility on a single supplied triangle. The assembly uses
naturality to transport inputs, the triangle identity, and output transport. Evaluation
and total-limit clauses are functor images of the system equality.

The compositor's isomorphism clause is proved directly from
`systemProperOpenGammaIsIso`, inverse refinement and the open/proper compositors.
The proof also establishes naturality of graph-refinement change, without new holes.
Existing joint naturality and every public signature are preserved.

Nine definitions move to `SystemProjectionFormulaMaps` and remain publicly
reexported by the assigned module, so the split obligations can refer to the words
without an import cycle. See `coord/changes/U6-system-projection-word-extraction.md`.
Verification: all four modules compile in dependency order; the final proof debug
compile completed its goals in 31.5 seconds, reporting only the subsequently removed
profiling options, redundant rfl, and unused simp argument. The delivery command will
check the cleaned packet again.

The explicit-triangle helper prevents the algebraic calculation from unfolding the
large canonical compactification construction during type checking. The original
module proves its word identity with the triangle kept as a parameter and then
specializes to the same canonical triangle. No consumer or adopted-source module changes. Text comparison confirms that all three
existing public theorem signatures and all nine existing definition signatures are unchanged. Eight bodies are unchanged;
compositor factors its same four-factor word through the new explicit-triangle
helper compositorAlong, recovering the old body by unfolding that helper.

## Proved and sorry left

Original holes: 2. One upper hole is closed by decomposition, not by an independent
complete proof: `WeilConjectures.SystemProjectionFormula.system_projection_formula_coherence`.
Two lower holes are added, so the packet has 3 holes rather than 2.

- Unchanged: `WeilConjectures.SystemProjectionFormula.projection_evaluation`, node
  `lem-pur-system-level-projection-formula-coherence`.
- Added: `WeilConjectures.SystemProjectionFormula.projection_change`, node
  `lem-pur-system-projection-change-compatibility`.
- Added: `WeilConjectures.SystemProjectionFormula.projection_triangle`, node
  `lem-pur-system-projection-triangle-compatibility`.

The last two statements are strictly parts of the argument. The first involves only
two compactifications of one morphism. The second involves one compatible triangle,
without graph changes, invertibility, finite evaluation or inverse limit. The main
proof combines them with proved naturality and invertibility; neither restates the
original theorem with repackaged hypotheses.

Edge cases: the transport equation does not invert the projection and applies when
its inputs vanish; identity refinements reduce to naturality and compositor units.
The triangle equation also does not assert a projection is invertible. It is the
counit-defined composition identity on arbitrary systems. The geometric hypotheses
ensure the open immersions used in proper/open support are quasi-compact.

## No longer needed

No existing module is withdrawn. No original public import is removed from the
assigned module. The extracted maps module imports only its actual statement
interfaces (`IntegralCompactificationRealizationData` and compactification triangles).
The extracted module does not need the old imports
`Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`,
`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`,
`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
`Sheaf.Paper.FiniteTorAmplitudeSites`, `Mathlib.Algebra.CharP.CharAndCard` or
`Mathlib.Algebra.CharP.Algebra`. The original public import interface is retained by
the assigned module. No removed module is asserted globally unreachable.

The following old parent proof dependencies are no longer used directly by the
assembly proof (this is not a claim that their modules have no other users):
- `lem-coef-derived-system-evaluation-calculus`
- `lem-coef-finite-adjunction-diagram-realization`
- `lem-pur-system-compactification-pf-substitution`
- `lem-pur-system-compatible-compositor-normalization`
- `lem-pur-system-compositor-refinement-square`
- `lem-pur-system-normalized-tensor-closure`
- `lem-pur-system-proper-open-invertibility`
- `lem-pur-system-ringed-sequence-site`
- `lem-sf-composition-projection-mate`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-pullback-tor-amplitude`
- `lem-sf-tensor-ctf`
- `lem-sfb-ringed-projection-tensor-composition`
- `lem-trf-open-ctf`
- `lem-weil-finite-compact-projection-formula`

Dependency-cycle audit of all four packet nodes found no return path through their
statement or proof dependencies.

The new change and triangle obligations retain the general projection/mate theory
that they require through their own DAG dependencies. No unit statement or realized
unit proof step is removed. Finite-Tor preservation and etale-origin lemmas are
unnecessary in the assembly because its concrete-word identities hold for arbitrary
system inputs; the original domain hypotheses remain in the public theorem.

Removed parent `tool_uses` entries:

- `lem-trf-open-ctf`
- `lem-coef-finite-adjunction-diagram-realization`
- `lem-coef-derived-system-evaluation-calculus`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-pullback-tor-amplitude`
- `lem-sf-tensor-ctf`
- `lem-weil-finite-compact-projection-formula`
- `lem-pur-system-compactification-pf-substitution`
- `lem-pur-system-normalized-tensor-closure`
- `lem-pur-system-ringed-sequence-site`
- `lem-sf-composition-projection-mate`
- `lem-sfb-ringed-projection-tensor-composition`

## Where the brief, the DAG or earlier work was wrong

The existing general substitution and compatible-compositor statements use a
different semilinear presentation; they cannot be applied definitionally to the
concrete `Operations` words. The two split obligations expose exactly these missing
concrete-word specializations. The existing proper/open support theorem already
proves the isomorphism needed here, so a separate normalized-domain invertibility
obligation is unnecessary for this clause. Finite evaluation is not inferred from
faithfulness of evaluations; its separate existing hole is retained.

## New nodes

`def-pur-system-projection-formula-maps`: the existing explicit words, extracted
without mathematical change to make the proof dependency graph acyclic; the
compositorAlong helper factors the identical word for efficient type checking. Change
record: `coord/changes/U6-system-projection-word-extraction.md`.

`lem-pur-system-projection-change-compatibility`: the concrete refinement transport
square, with a sourced proof through proper/open mates, proper-composition projection
and inversion of refinement comparisons.

`lem-pur-system-projection-triangle-compatibility`: specialization of the existing
system composition-projection mate to the supplied scheme compactification triangle,
including the actual equality transports and pullback compositor.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
