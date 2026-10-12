## What changed

Reduced `AlgebraicGeometry.strictPerfectClosedPushforward_stalkResolution` without changing
its signature or any existing public import. Its proof now obtains a bounded projective
stalk complex, removes the positive tail, transports homology, and invokes the proved
private helper `AlgebraicGeometry.nonpositiveProjective_resolution`.

The helper constructs the natural-number chain complex by restriction along n ↦ -n,
constructs its augmentation through the degree-zero opcycle quotient, proves that the
augmentation is a quasi-isomorphism, supplies termwise projectivity, and proves the
bound `a.natAbs`. It contains no sorry. Its proof uses Mathlib's restriction opcycle and
homology comparisons, cokernel exactness and the quasi-isomorphism criteria.

Added two new modules, each with one public intermediate theorem, and proof-only imports
of them and `Mathlib.Algebra.Homology.Embedding.RestrictionHomology` to the assigned module.
The generic tail-removal theorem is also completely proved. Its private helper
`CochainComplex.projective_cycles` uses downward induction and explicit retractions to
prove projectivity of cycles in nonnegative degrees. The public proof then constructs
Mathlib's good truncation at zero, transports its termwise projectivity and lower bound,
and proves its inclusion is a quasi-isomorphism.

The geometric module retains the existing closed-pushforward and exact-stalk declarations
as proof imports; they remain the intended dependencies for that item. Updated the
assigned DAG node's proof, proof_deps and proof_origin to match the actual reduction.

All three files compile cleanly with lcompile.py --all. Repeated single-file compiles
resolved the restriction indices, the dependent augmentation identity, and the exactness
transport. No definitions, existing statement signatures, existing public visibility, unit route
or target statements changed. No forced adaptations or change records are needed.

## Proved and sorry left

Closed the assigned module's single hole:
`AlgebraicGeometry.strictPerfectClosedPushforward_stalkResolution`
(node `lem-sc-strict-perfect-closed-pushforward-stalk-resolution`). There are no sorries
left in that module. The private resolution-construction helper is completely proved.

One hole is added, as the whole proof of the public theorem:
`AlgebraicGeometry.strictPerfectClosedPushforward_stalkModel`, in
`Sheaf.AlgebraicGeometry.StrictPerfectClosedPushforwardStalkModel`, node
`lem-sc-strict-perfect-closed-pushforward-stalk-model`. This isolates original steps 1-2:
the bounded projective stalk complex and its homology, with no nonpositive model or
augmented resolution in the conclusion.

`CochainComplex.boundedProjective_nonpositiveModel`, in
`Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel`, node
`lem-sc-bounded-projective-nonpositive-model`, is completely proved, as is its private
helper `CochainComplex.projective_cycles`. No sorry remains in this algebraic module.
It assumes only positive homology vanishing and does not mention schemes, stalks or a
degree-zero target module.

This is a decomposition with a proved algebraic step: one original upper hole closed,
one strictly smaller geometric hole added; net holes closed minus added is 0 before
shared downstream-closure effects. It is not claimed as a complete axiom-free proof of
the geometric theorem. No hole occurs in a private declaration, definition or partial
proof. The remaining theorem has a complete natural-language proof and source.

## No longer needed

No imports or modules are pruned. The old direct proof dependencies
`lem-weil-pbc-closed-pushforward-stalks`, `lem-weil-pbc-module-stalk-exact`, and
`def-pc-perfect-complex` are replaced in the resolution node's `proof_deps` by the
stalk-model and nonpositive-model nodes. The first two remain transitive proof
dependencies through the stalk-model node; the perfect-complex definition remains
both a statement dependency and a transitive proof dependency. None is globally
no longer needed. The unit record has no realized node in this module to bypass.

## Where the brief, the DAG or earlier work was wrong

The original plan's step 3 had no named dependency for the nontrivial positive-tail
splitting argument. The two new modules make the missing intermediate interfaces explicit;
no mathematical statement is disputed. The closed-pushforward and module-stalk-exact
interfaces were read, and neither directly states the bounded projective model required
here. The existing perfect-complex definition gives bounds and retractions, but requires
stalk transport and derived-category glue before it can be used in the algebraic argument.

The local literature files are absent on this machine. I read the primary Stacks pages
for [066Q](https://stacks.math.columbia.edu/tag/066Q),
[08C4](https://stacks.math.columbia.edu/tag/08C4),
[08CM](https://stacks.math.columbia.edu/tag/08CM), and
[00AE](https://stacks.math.columbia.edu/tag/00AE). The successive split-epimorphism proof refines the explicit
argument already in the assigned node, rather than the different finite-free-resolution
argument in the published proof of 066Q; the new node's proof_origin records agent work.

New statement edge cases checked mathematically: an empty support interval and an acyclic
strictly perfect model give zero homology, and are allowed; an upper bound ≤0 requires no
tail removal; a zero top term can still be split; for an arbitrary lower bound a the
inequality j > a.natAbs implies -j < a. The generic tail-removal statement does not require
finite generation or enough projectives. Projectivity suffices to split each epic map to
an already projective term. The assigned theorem has a source point, so an empty source
scheme supplies no inputs; hx excludes the empty open neighbourhood.

## New nodes

`lem-sc-strict-perfect-closed-pushforward-stalk-model` formalizes the original plan's first
two steps, with the same sheaf and restricted source stalk. Its four conclusions are a
bounded projective complex, degree-zero homology identification and other homology
vanishing. The proof uses the existing perfect-complex definition, exactness of module
stalks and the existing closed-pushforward stalk theorem. It does not construct a
projective resolution and hence does not restate the assigned conclusion.

`lem-sc-bounded-projective-nonpositive-model` formalizes only positive-tail splitting. It
is independent of the geometric item and degree-zero module. Its conclusion preserves
homology and bounded projectivity while removing positive terms. Augmentation, reversal
of indices, quasi-isomorphism and the natural-number bound are separately proved in the
assigned module. Its complete Lean proof uses descending induction to split
successive epimorphisms onto projective cycle objects, constructs retractions, and
then takes good truncation. This is the planned tail-splitting argument expressed through
Mathlib's existing canonical truncation; it does not bypass the unit route. No change records were created.

For both nodes, LeanSearch was attempted and returned Internal Server Error; LeanFinder
returned K-projectivity, derived vanishing and projective-resolution extension components,
not either required statement. Mathlib/source-library/DAG grep found no matching theorem;
blueprint_refs.py searches for bounded projective nonpositive and strictly perfect stalk
found no matching imported blueprint node. The three search kinds are recorded in each
node. Both new nodes retain the assigned chapter, unit and nearest blueprint ancestor.
The long induction and resolution construction are marked non-elementary in the DAG;
they are completely implemented in Lean directly from Mathlib, not additional unstated
holes or assumed lemmas.

## Second reading by T3

1. **Existing interface — PASS.** Read the repository/sandbox module diff and compared
   the existing theorem signature byte for byte. Its hypotheses, conclusion, universe
   parameters and visibility are unchanged. All original public imports stay; added
   imports in the assigned module are proof-only. No existing definition or target
   statement changes. There are no forced adaptations or change records.
2. **Proof and axioms — PASS as a decomposition.** Independently compiled all three
   delivered modules in import order, cleanly (1.9, 4.1 and 4.3 seconds). Read the
   cycle-retraction induction, good truncation, opcycle augmentation, quasi-isomorphism
   proof and numerical bound. Scratch copies with `#print axioms` confirm only
   `propext`, `Classical.choice`, `Quot.sound` for `CochainComplex.projective_cycles`,
   `CochainComplex.boundedProjective_nonpositiveModel` and
   `AlgebraicGeometry.nonpositiveProjective_resolution`. The stalk-model and assigned
   theorems additionally use `sorryAx`, as reported. The sole delivered sorry is the
   whole proof of the named public stalk-model theorem. No hollow definition or
   forbidden declaration occurs. Existential elimination stays inside theorem proofs;
   no definition chooses an arbitrary witness from the open theorem.
3. **Intermediate statements — PASS.** The geometric hole asserts only the bounded
   projective stalk complex and its homology, with a node and a complete sourced
   docstring proof. Stalk exactness, finite-free stalks, neighbourhood restriction and
   closed-pushforward stalk identification justify its four clauses. Checked zero and
   acyclic complexes, empty support intervals, upper bounds below zero, and a complex
   in degree zero alone. The algebraic intermediate is fully proved, works in any
   abelian category without enough projectives, and splits maps onto projective cycles.
   Independent LeanFinder search for exact stalks and bounded locally free complexes
   returned only K-projectivity, localization and generic resolution components.
   Loogle did not resolve `Projective`. Source `rg` searches for perfect stalks,
   projective cycles and projective truncation found no matching alternative in Mathlib
   or the project. This is an algebraic reduction, not a renamed resolution statement.
4. **Route and pruning — PASS after report clarification.** The original first two
   geometric steps stay in the stalk-model node. Descending retractions and good
   truncation implement the planned tail splitting; augmentation and index reversal
   are proved separately. The unit `dag/units/sk-thm-picard-duality.json` has empty
   `realized` lists; no unit step is bypassed. Imports supply signatures or proof
   components; the geometric hole retains its intended proof-dependency imports.
   The three old direct dependencies are now explicitly accounted for under No longer
   needed. All remain needed transitively or in the signature; no module is pruned.
5. **DAG agreement — PASS.** Read all three nodes and the existing node diff: only
   `proof`, `proof_deps`, `proof_origin` change. Programmatically checked each node's
   Lean statement against its delivered signature and each `proof_deps` against the
   union of the proof steps' uses. New nodes carry source, searches, creation,
   blueprint, chapter, unit and Lean records. Their descriptions follow the actual
   induction, truncation, homology transport, augmentation and index bound. Checked
   primary Stacks pages [066Q](https://stacks.math.columbia.edu/tag/066Q),
   [08C4](https://stacks.math.columbia.edu/tag/08C4),
   [01AG](https://stacks.math.columbia.edu/tag/01AG) and
   [00AE](https://stacks.math.columbia.edu/tag/00AE). The proof origin distinguishes
   the agent's tail-splitting refinement from the published 066Q proof.

Second reading changed only this review record and the dependency accounting in
No longer needed. No Lean proof or statement needed repair. One original hole closed,
one strictly smaller geometric hole added: net zero, with the algebraic step proved.
The remaining geometric transport requires substantial development and stays explicitly
open; this delivery is not claimed as a complete proof of the geometric theorem.
