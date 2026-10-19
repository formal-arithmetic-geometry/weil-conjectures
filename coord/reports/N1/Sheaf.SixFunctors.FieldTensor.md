## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.tensorClosureRational` with its original signature and public imports. Bounded closure uses the existing `isMonoidal_boundedConstructible` declaration after clause (4) of `finiteCoefficientDescentTwoColimit` identifies the two constructibility predicates. A fully proved strong monoidal coefficient-presentation equivalence handles the arbitrary ring-object isomorphisms in `hΛ`. Two actual localizing-minimality arguments prove closure of the localizing category, using exactness, tensor-Hom adjunction, braiding and preservation of coproducts.

Added `Sheaf.SixFunctors.ConstructibleCoefficientTransport`, containing only proved theorems and private helpers. Its public theorem constructs a strong monoidal derived equivalence and proves preservation and reflection of finite-constant-model bounded constructibility. No existing definition or statement was changed. The proof-context commands are recorded in `coord/changes/N1-field-tensor-proof-context.md`, with all eight transitive consumers checked and no adaptations required. The zero module, empty scheme, arbitrary shifts and both rational coefficient choices are included.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.ProEtale.CondensedRing.tensorClosureRational`.

Added 0 holes. `AlgebraicGeometry.ProEtale.CondensedRing.constructibleCoefficientTransport` and all private helpers are fully proved. No `sorry` remains in either delivered Lean module. `lcompile.py --all` compiled the coefficient transport module cleanly and the item in 27.8 seconds, with no warnings. This proves the item from existing library declarations; in particular the upstream `isMonoidal_boundedConstructible` instance remains an existing dependency, not a new assertion in this delivery.

## No longer needed

Removed direct proof imports:

- `Sheaf.Topology.ProfiniteCondensedRing`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.Bifunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `Sheaf.SixFunctors.IntTensorProjection`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Paper.CoefficientHeart`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CoefficientHeartGeneration`

The proof no longer directly needs `det-cor-coefficient-heart-ii-generation`, `det-cor-coefficient-heart-ii-triangulated`, `det-lem-int-tensor-projection`, `det-sf-open-closed-sequence-ring-sheaf`, `lem-sfb-locally-closed-extension-coherence`, `sk-prop-sfb-cartesian-coefficients`, `sk-lem-coefficient-heart`, or the explicit five-piece generator calculation: bounded tensor closure is already a declared library result, and the rational predicate comparison is proved in the library. Some remain transitive dependencies of the existing results; no global unreachability is asserted. Obsolete `tool_uses` approvals are removed, preserving the order of surviving entries. No unit statement or unit proof step is bypassed: the item still proves tensor closure in clause (1), followed by the two localizing arguments in clause (2).

The earlier sandbox-only modules `RationalConstructibleInduction`, `RationalGeneratorTensor`, and `LisseExtensionTensorNormalForm`, and their three proposed nodes, are unnecessary and are omitted from this delivery. They were never repository files. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The two constructibility predicates are not definitionally equal. The proved clause (4) of `finiteCoefficientDescentTwoColimit` supplies exactly their equality under the standing scheme and canonical rational coefficient hypotheses. This makes the existing bounded-constructible tensor theorem usable and eliminates the previous attempt's geometric split. Coefficient transport must preserve the ring-object structure and be strong monoidal; equality of underlying abelian sheaves would not suffice. The library tensor-preservation node `lem-sfb-dc-tensor-preserves` and the comparison clause of `sk-thm-sfb-qlbar-two-colimit` are used as existing tools for the bounded-closure substep; they do not replace the unit’s localizing arguments. The resumed dry run required a change record for the added namespace opening and local irreducibility attributes; that record now inventories all eight consumers and explains the local scope. The original declaration and its docstring are preserved; the updated DAG records the shorter proof actually used.

## New nodes

`lem-sf-constructible-coefficient-transport`: an arbitrary coefficient-ring isomorphism induces a strong monoidal derived equivalence preserving and reflecting bounded finite-constant-model constructibility. The proof transports finite presentations, constant local models, stratifications, affine restrictions and cohomology, then derives the existing strong monoidal scalar equivalence. The node records its source, searches, complete proof and exact Lean signature. There is no arbitrary object chosen from an unproved existence statement, no additional axiom, and no existing mathematical interface is changed. The conservative command-scope change record is `coord/changes/N1-field-tensor-proof-context.md`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
