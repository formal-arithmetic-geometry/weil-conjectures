## What changed

Proved `WeilConjectures.PurityFiniteSetting.divisorScalarRealization_existsUnique`
in `Sheaf.Paper.FramedScalarRealization`. Added the proof-only import
`Sheaf.AlgebraicGeometry.ScalarUnitExt`; retained the supported integral derived-unit
import. Public imports, both declaration signatures, and the uniquely characterized
`divisorScalarRealization` definition are unchanged.

The proof applies `supported_integral_derived_unit` at the positive exponent
`P.diagonalExponent`, uses `scalar_unit_ext_bijective` in degree two with target
`P.frameTwistEtale T 1`, identifies its map by unfolding the two realization wrappers,
and applies `Function.Bijective.existsUnique` to `P.divisorIntegralSplice a i β`.
The node records these three steps and their actual dependencies. A proved private
helper `realizeExact_bijective` identifies the generic realization wrapper with the
existing Ext bijection before specializing to concrete sheaves. Local irreducibility
settings keep the large derived-category and Ext constructions from unfolding during
this identification; they change no public declaration or definition.

Searches: LeanFinder returned the generic Ext exact-functor APIs, Loogle returned
`Function.Bijective.existsUnique`, and project `rg` found the existing
`ScalarUnitExt` theorem and its use in `CartierReductionData`. The launcher grep
query for `scalar_unit_ext_bijective` returned zero Mathlib hits; the matching theorem
is in the project. No intermediate theorem is duplicated.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.PurityFiniteSetting.divisorScalarRealization_existsUnique`
(node `def-pur-framed-scalar-realization`). No holes remain in the item; zero holes
were added and zero were split off. This is a proof from existing declarations.
The imported coefficient annihilation theorem remains an existing dependency;
this delivery does not claim to close its proof.

## No longer needed

None. No import was removed, no node or module was withdrawn, and no unit step was
bypassed. Both original public imports are required by the statements and the
unique-choice definition. Both private imports are used directly by the proof.
The previously empty node proof dependency list is populated with the actual route.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps or proof dependencies, although the theorem's
docstring already described the supported derived-unit argument. The delivery records
that argument precisely using the existing APIs. The rework table lists a historical
quarantine path; the current source module is present and is preserved with its Lean
attachment and dependencies. No definition, statement, or consumer adaptation is needed.

The two categorical theorems are used as generic tools from another unit, exactly as
the existing docstring prescribes; no step of `sk-prop-a1-kummer` is replaced. The
maintainer may record tool approvals if required. The current blueprint's relative-class
and coefficient-extension paragraphs were read in `literature/blueprint/latest/`.

Validation: the initial item compiled in 47.1 seconds, but a subsequent delivery
compile timed out at 60 seconds. After moving the generic wrapper identification
into the proved private helper and controlling local unfolding, the complete item
compiled cleanly through `lcompile.py` in 48.3 seconds (exit code 0). No limit was
raised and no file or proof was split. All Lean lines are at most 100 characters.
Only the node's `proof`, `proof_deps` and `proof_origin` fields changed.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
