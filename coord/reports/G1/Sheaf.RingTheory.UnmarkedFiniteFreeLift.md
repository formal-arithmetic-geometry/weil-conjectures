## What changed

Proved `DerivedCategory.exists_unmarked_finiteFree_lift_of_nilpotent` with its signature,
universes, hypotheses and conclusion unchanged. Pseudo-coherence supplies the finite-free
representative. The already proved private helper
`CochainComplex.projective_reduction_comparison`, accessed by
`import all Sheaf.RingTheory.NilpotentProjectiveComplexLift`, computes its derived
reduction in the independent universes of this statement. The existing proved
`DerivedCategory.exists_stablyFree_lift_mod_ideal` then supplies the desired complex,
its two isomorphisms and finite free terms. A zero-endomorphism application of
`ModuleCat.surjective_of_extendScalars_mod_ideal` proves the precise bound b.

The two finite stably-free/Nakayama nodes are used as generic algebra tools from
`sk-prop-av-cube`; neither replaces a realized step of the proper-base-change unit.
The comparison helper is already fully proved in the module of the existing
nilpotent-projective-lift node; this delivery does not invoke that module's public
lifting theorem or add an unproved sublemma.

Preserved every original public import. Replaced the two proof imports with the actual
comparison and Nakayama imports. Added a declaration-local unused-variable linter option:
the nilpotence hypothesis is unnecessary for this stronger argument, and the original
existential beta/theta binder names have no occurrences in the proposition's body. No
mathematical options, definitions, statement signatures or public visibility changed.
Updated the node's proof, proof dependencies and proof origin to the implemented route.

Validation: remote single-file compilation succeeded; an axiom probe reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The proof also covers zero rings and
zero terms: the zero-endomorphism argument uses no nontriviality or positive-rank hypothesis.
The failed preliminary run hit the 60-second limit; a traced run completed in 8 seconds,
and a clean axiom-probe run in 4 seconds. No limit was changed and no file was split.

## Proved and sorry left

Closed 1 of 1 holes:
`DerivedCategory.exists_unmarked_finiteFree_lift_of_nilpotent`
(node `lem-weil-pbc-nilpotent-marked-free-complex-lift-unmarked`).
Added zero holes; zero holes remain in the delivered module. No decomposition or new lemma.
The axiom probe confirms that no imported sorry is used in this proof either.

## No longer needed

Removed proof imports:
- `WeilConjectures.RingTheory.RingPseudoCoherent`: already exposed by the existing public
  stably-free lifting import; its definition is still used.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: no sheaf-level construction
  is used directly; the proved ordinary-module comparison handles the required computation.

Removed the direct proof dependency on `lem-pur-derived-change-of-rings` and the redundant
`def-weil-abstract-derived-category` proof edge. Both statement dependencies stay unchanged.
The former module and node may remain reached transitively, so no entire module is claimed
unreachable. All other old proof dependencies remain in the implemented argument. The
unit's realized statement and proof steps are unchanged; this is a below-unit tool route.

## Where the brief, the DAG or earlier work was wrong

The old single proof step did not identify the available lifting theorem or the
independent-universe comparison needed to apply it. Both are already proved in the library.
The exact bound requires a termwise argument beyond the existential bound provided by
Tag 0BCB; finite-module Nakayama supplies it without using nilpotence. There is no false
statement or required interface repair. The private comparison helper is reused through
Lean's `import all` mechanism, rather than duplicated or promoted to a new public API.

Change record: `coord/changes/g1-unmarked-finite-free-lift-proof-context.md`.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
