## What changed

Replaced the proof hole in the assigned module by a complete Lean assembly of the
node's two planned constructions. No existing statement or definition changed.

The monoidal part installs core monoidal structures on the standard localization
equivalences, uses Mathlib's inverseMonoidal for the inverse equivalence, takes the
existing standard derivedPullbackMonoidalModel, and composes the three structures.

The adjunction part applies RingedSpace.derivedModulePullback_adjunction, obtains
the transported functor's left-derived comparison for that same underived functor,
uses Functor.leftDerivedUnique, and transports the adjunction along the resulting
isomorphism. This identifies its right functor with schemeDerivedDirectImage by
its existing definition; no right-derived transport lemma is needed.

Proof-only imports added: SchemeDerivedStandardEquivalenceMonoidal,
DerivedPullbackAcrossUniversesLeftDerived, DerivedPullbackMonoidalModel, and
RingedSpaceDerivedAdjunctionGeneral. The existing unused existential binder warning
is suppressed by a command scoped to the assigned theorem; its signature remains identical.

## Proved and sorry left

Closed in the assigned module:
`AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_monoidal_adjunction`.
No sorry remains in that module.

Added and still sorry:
`AlgebraicGeometry.exists_schemeDerivedStandardEquivalence_monoidal`
(node `lem-sc-standard-derived-equivalence-monoidal`), and
`AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_leftDerived`
(node `lem-sc-derived-pullback-across-universes-left-derived`).

This is a decomposition: one upper hole closed and two strictly smaller holes added,
not a complete proof without new holes. The first hole is about one scheme and its
localization equivalence, independent of any pullback morphism or adjunction. The
second is a left-derived universal property, independent of tensor structures and
direct image. Their existence witnesses are used only inside theorem proofs.

The target assembly and both new interfaces were compiled through lcompile.py.
The new statements cover arbitrary independent universes, identity morphisms,
empty schemes and zero complexes. No flatness or finiteness hypothesis was added.

## No longer needed

No original imports removed. None of the original node's dependencies is pruned:
they remain needed directly or within the two strictly smaller transport interfaces.
The original plan's separate right-derived uniqueness transport is unnecessary:
the existing ringed-space adjunction is used in the chosen universes, and uniqueness
identifies its left functor with the transported pullback instead.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original node described localization transport in
words but supplied no Lean interface for monoidality of the standard equivalence
or for the transported left-derived counit. The new nodes isolate those two gaps.
Mathlib's ordinary monoidal localization transport requires a strong monoidal
localization functor; Qh for K-flat derived tensor is only lax monoidal, so it does
not directly close the first gap.

## New nodes

`lem-sc-standard-derived-equivalence-monoidal`: a core monoidal structure on the
functor of schemeDerivedStandardEquivalence, for the two fixed derived tensor
structures. Source: Stacks 079U for K-flat tensor comparison (identity morphism)
and 05RU for localization. The coherence argument is recorded in its docstring.

`lem-sc-derived-pullback-across-universes-left-derived`: a left-derived counit and
universal property for the already constructed transported pullback, relative to
any additive functor with the concrete module pullback object and morphism formulas.
Source: [Stacks 06YJ](https://stacks.math.columbia.edu/tag/06YJ) and
[05RU](https://stacks.math.columbia.edu/tag/05RU). Its docstring describes transport of the counit,
factorization and uniqueness. Neither node restates the assigned conjunction.

Change record: `coord/changes/derived-pullback-across-universes-proof-linter.md`.

## Second reading by E2

1. **Diff and interfaces.** Compared the assigned module with the repository version. The
   theorem signature and all existing declarations are unchanged; the two added modules
   contain only the split interfaces named above.
2. **Compilation and trust.** Compiled all three delivered modules with `lcompile.py --all`.
   The assigned theorem has no `sorry`; the two remaining `sorry`s are named public theorems
   with source docstrings and matching DAG nodes. No axiom, unsafe, opaque, extern, or hollow
   definition was added. The proof uses only the existing constructions and the two stated
   transport interfaces.
3. **Split statements.** Checked the edge cases recorded in both docstrings (identity maps,
   empty schemes, and zero complexes). The monoidal equivalence statement concerns only the
   standard localization functor; the left-derived statement concerns only the transported
   universal property. Neither restates the assigned conjunction, and neither adds hypotheses.
4. **Pruning and route.** Searched the relevant derived and monoidal namespaces for an existing
   localization-transport theorem. The available results provide uniqueness and inverse
   monoidal transport but no theorem for these fixed derived localizations, so both splits are
   needed. The target proof keeps the standard derived pullback monoidal model and the ringed
   space adjunction route. No removable import was found.
5. **DAG and unit.** The target and both new node records match their Lean declarations,
   proof dependencies, source, and `status: split`. The unit route remains the target's two
   localization-transport steps; no unit statement or realized field was changed.

Changed only the target proof, its proof-only imports, the two documented split modules and
nodes, the scoped linter change record, and this second-reading report.
