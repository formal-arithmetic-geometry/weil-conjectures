## What changed

Repaired the carrier universe in
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings` from independent `w` to
`max u v w`, matching the already stated and proved general topological-group
embedding theorem. Specialized that theorem, paired its monicity and injectivity
proofs objectwise, and constructed an `InjectivePresentation` for each object to
obtain `EnoughInjectives`. The node's Lean attachment and proof steps now match
this proof. All imports are retained and used; none is added.

Change record: coord/changes/G3-discrete-continuous-injectives-universes.md.
No definitions or target signatures change. No consumer application exists, and
the sole direct importer compiles unchanged against the repaired module.

## Proved and sorry left

The corrected declaration
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings` has a complete proof from
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup`
and Mathlib's `InjectivePresentation` and `EnoughInjectives` constructors.
Actual item hole count: 1 before, 0 after. Holes added: 0. Split-offs: 0.
No declaration in the delivered module remains sorry.

Because the signature needed a size repair, this is a repaired statement with a
complete proof, not a proof of the stronger original independent-universe claim.
Do not credit the original hole as an unchanged-statement proof: 0 of the original
1 claims proved unchanged, 1 corrected declaration proved, 0 holes left.
The proof follows both existing DAG steps and uses no new theorem or node.

Validation: the repaired module compiles cleanly on the prescribed server compiler
(1.9 seconds). The unchanged direct importer compiles against the sandbox overlay.
The delivery tool runs its own compile and axiom/sorry probe during the dry run.

## No longer needed

None. No import, proof dependency, node, module, or unit step is pruned.
Both declared proof dependencies are used: the general embedding theorem supplies
J and j; the Mathlib injective-object/presentation definitions give the consequence.
The unit route is unchanged. No unused proof import is present.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original Lean signature asserted enough injectives even
when the carrier universe is smaller than the profinite group. This is false in
general. For G a product of F_p indexed by an oversized set K, an injective object
containing a nonzero invariant x must contain distinct vectors y_i with
`(g - 1)y_i = chi_i(g)x` for all coordinate characters chi_i. These vectors come
from extending the trivial line into the finite two-dimensional upper-triangular
representations. Thus K injects into the carrier, contradicting its small size.
The change record gives the argument and exact old and corrected signatures.

The general dependency's earlier independent reading had already made the same
universe repair (coord/reports/C1/lem-exc-rg-discrete-modules-functorial-injective-embeddings.md).
This specialization had not been updated to match it. The mathematical DAG
statement remains correct with the source's common-universe convention.
The parent `CategoryTheory.discreteModules_abelian` still states its enough-
injectives clause with independent carrier universe and needs the analogous
repair when it is proved. Its current proof is sorry, so this delivery forces
no source adaptation. Its unrelated abelian-category and exactness clauses do
not have this injective-size obstruction.

Source read: Stacks injectives.tex, Tag 04JF, label lemma-G-modules.
The intended two-step plan is otherwise correct and now implemented in Lean.
Searches actually run via msearch: LeanFinder for functorial embeddings implying
enough injectives; Loogle for CategoryTheory.EnoughInjectives; grep for
functorialInjectiveEmbeddings|EnoughInjectives. The useful exact constructors are
EnoughInjectives.mk and InjectivePresentation.mk, read in the pinned Mathlib.
Library rg also found the same packaging in DiscreteIntegerInvariantsInfrastructure.
Edge cases checked: the zero ring and trivial group are allowed; there is no
nontriviality or characteristic restriction. The carrier maximum supports the
group-ring construction for arbitrary ring/group sizes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
