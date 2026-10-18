## What changed

Proved `CochainComplex.exists_projective_lift_of_nilpotent` in
`Sheaf.RingTheory.NilpotentProjectiveComplexLift`, with its entire signature unchanged.
The proof follows the node's five steps and Stacks Tags 09AR and 0BCA:

- Take all projective modules as the class. Prove closure under sums and summands.
- Identify scalar extension with quotient by the ideal. A map surjective after reduction
  has cokernel T with T = IT, hence T = I^N T = 0. No finiteness is used.
- Lift each prescribed projective quotient module by the existing projective-module theorem.
- Detect the upper cohomological bound, then use the existing bounded-above projective model.
- Compute derived scalar extension on that model and apply the proved class-lifting theorem.

The public upper-bound theorem is stated for sheaves on the one-object site, while this item
uses ordinary modules. Its module already proves the required ordinary-module filtration
lemma privately. `import all` reuses that proved lemma. The existing K-flat scalar-extension
module likewise supplies its proved quasi-isomorphism lemma, and the ring-equivalence module
supplies its proved generic Kan-extension helpers. Local private lemmas combine those APIs;
no dependency module, existing definition, public statement, or target is changed.

Mathlib's monoidal module API and the source K-flat API require equal ring and module
universes. The local proof transports through `ULift A ≃+* A` and the induced exact
module-category equivalence. Universal Kan-extension uniqueness also handles the independent
source and target derived-category morphism universes. The nilpotent filtration and the
comparison on bounded projective complexes are both completely proved.

Validation: repeated single-file compilation through `lcompile.py` (final proof about six
seconds), no errors or warnings. `#print axioms` for the delivered theorem reports exactly
`propext`, `Classical.choice`, `Quot.sound`. All new import directions were checked to avoid
cycles. The source statements and their signatures were read; the prescribed unit route is
unchanged. No new modules or nodes, and no changes to consumers.

## Proved and sorry left

Closed 1 of 1 original holes:
`CochainComplex.exists_projective_lift_of_nilpotent`
(node `lem-weil-pbc-nilpotent-projective-complex-lift`).

Holes added: 0. Sorries left in the delivered module: 0. Every local helper is proved.
The complete theorem has only the three permitted axioms; this is a proof, not a decomposition.

## No longer needed

None. All four original proof-dependency modules are used, and all five steps of the existing
DAG plan remain. The existing public import interface is preserved. The added proof imports
supply the quotient comparison, projectivity instances, K-flat computations, exact-functor
homology comparison, and universal Kan-extension transport used by the proof.

## Where the brief, the DAG or earlier work was wrong

The node's mathematical argument is correct. Its Lean interfaces required glue: the public
nilpotent upper-bound declaration uses ring-site sheaves, the item uses ordinary modules,
and the available monoidal tensor API ties the ring and module universes together. The proof
uses the existing ordinary-module helper and ring-universe transport rather than changing
any existing signature. The class-lifting theorem's hK also explicitly asks for the derived
reduction of the chosen projective model; the counit comparison supplies it.

The dry run conservatively flags the added open and universe commands as an interface
change. Their module-local scope and the unchanged signatures/import interface are recorded
in `coord/changes/a2-nilpotent-projective-complex-proof-context.md`, including every downstream
consumer. No adaptation is needed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
