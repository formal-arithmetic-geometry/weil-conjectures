## What changed

The only changed Lean module is `Sheaf.Paper.ConstantCompletionEquivalence`. All existing
public signatures, definitions and public imports are preserved.

The coefficient equivalence now follows from the existing general flat ringed-ideal
complete equivalence. The proof identifies the extended kernel and quotient, and
constructs a finite-type presentation from Noetherian generators, including the empty
family. The ordinary finite tensor comparison is the unique isomorphism between the
two left adjoints of scalar restriction. Its normalization is proved on pure tensors.
Tensor-adjunction lifts provide the reduction transitions, and tensor generation proves
that the finite comparisons assemble into the prescribed strict tower isomorphism.

Derived limits commute with restriction by a natural extension-tensor comparison,
flat exact extension, the levelwise adjunction, preservation of K-injectives and the
existing generic derived tower-limit comparison. The proof verifies the normalization
on every complex, using the specified limit projections and restriction factors.
Abstract coefficient parameters keep the derived-limit proof from unfolding completion.
The private comparison constructions become irreducible after their section APIs are
proved. The existing Kan-extension transport now uses an abstract cochain-counit lemma;
`as_aux_lemma` isolates its factorization and uniqueness proofs. The existing
`pull_additive` argument is factored through a private additive algebraic-lift lemma.
The scalar-insertion uniqueness proof now specializes a generic sheaf-map extensionality
lemma, which avoids rechecking its concrete tensor construction. These mathematical
arguments and their public statements are unchanged. The module-scoped
`backward.isDefEq.respectTransparency.types` option avoids costly normalization while
checking the remaining representative formulas.

New proof imports: `Mathlib.RingTheory.Ideal.Span`,
`Mathlib.RingTheory.Finiteness.Defs`, `Sheaf.Paper.RingedTopoiTensorSections`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`,
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` (including its proved
private generic comparison), and `Mathlib.CategoryTheory.Adjunction.Whiskering`.
The existing DAG node records these implementations and their additional dependencies.
No statement/definition repair, forced adaptation or source-library change is included.
The static command-change gate is documented in
`coord/changes/K3-constant-completion-private-proof-interfaces.md`: only new private
comparison attributes and section-local commands are added; the public interface stays
unchanged. The record lists all direct consumers and their current holders.

Validation: the complete module compiles cleanly through `lcompile.py` (52.0 seconds).
Scratch experiments are outside the delivered `lean/` tree. The generic finite-comparison
helpers were separately checked with `#print axioms`: only `propext`,
`Classical.choice` and `Quot.sound` occur.

## Proved and sorry left

Closed 5 of the original 20 holes, with 0 holes added and 0 split off:

- `CategoryTheory.ConstantCompletion.equivalence`
- `CategoryTheory.ConstantCompletion.finiteComparison_existsUnique`
- `CategoryTheory.ConstantCompletion.reductionStep_existsUnique`
- `CategoryTheory.ConstantCompletion.reductionTowerComparison_existsUnique`
- `CategoryTheory.ConstantCompletion.derivedLimitRestriction`

These are complete Lean proofs from existing declarations. In particular the coefficient
flatness/quotient theorem remains an existing dependency; this is not an assertion that
the entire transitive axiom closure is finished.

The following 15 existing holes remain unchanged. Every declaration below belongs to
`lem-weil-pbc-constant-completion-equivalence` and retains its existing source and proof
docstring:

- `CategoryTheory.ConstantCompletion.flat_and_quotients`
- `CategoryTheory.ConstantCompletion.finiteDerivedComparison`
- `CategoryTheory.ConstantCompletion.quotientPresentation_exists`
- `CategoryTheory.ConstantCompletion.koszul_quotient_reflector`
- `CategoryTheory.ConstantCompletion.completion_restriction`
- `CategoryTheory.ConstantCompletion.derivedReductionTowerComparison`
- `CategoryTheory.ConstantCompletion.inverseImageData_exists`
- `CategoryTheory.ConstantCompletion.ordinaryPullComparison_existsUnique`
- `CategoryTheory.ConstantCompletion.derivedPullComparison_existsUnique`
- `CategoryTheory.ConstantCompletion.ordinaryFinitePull_existsUnique`
- `CategoryTheory.ConstantCompletion.finitePull_existsUnique`
- `CategoryTheory.ConstantCompletion.completedFinitePull_existsUnique`
- `CategoryTheory.ConstantCompletion.pullbackTowerComparison_existsUnique`
- `CategoryTheory.ConstantCompletion.pullback_composition`
- `CategoryTheory.ConstantCompletion.pullback_identity`

## No longer needed

None. No existing import, module or node is withdrawn. The pending parts of the node
still require their declared dependencies. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error or repair was found. The finite ordinary comparison admits a shorter
adjunction-uniqueness argument than constructing both balancing maps separately.
The first integrated derived-limit proof exceeded the compile limit; profiling led to
an abstract-ring helper and private section APIs that avoid unfolding comparison
constructions in the same argument. No compile limit was changed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
