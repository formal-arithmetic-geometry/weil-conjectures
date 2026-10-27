## What changed

The original theorem `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixCompactSupport`
now proves its isomorphism/Dctf clause and composition clause from existing declarations,
and obtains its refinement clause from one new strictly smaller lemma. Its signature and
the bodies of `scalarCompactSupportMap`, `scalarCompactSupportOpenComp`, and
`scalarCompactSupportModelComp` are unchanged.

For the first clause, open extension preserves Dctf and the proper scalar comparison
is invertible; its target properties transport across the open scalar isomorphism.
For composition, the proved normalized-interchange uniqueness and natural-family
construction turn the pointwise inputs into the inputs of `scalarCompositeModelPasting`.
A proved adjunction identity identifies the two definitions of the open compositor.
Componentwise adjunction extensionality, local irreducibility and explicit congruence
equalities prevent repeated unfolding
of the large derived adjunction terms. All diagnostic profiler and trace commands
have been removed.
The parent DAG proof and proof dependencies follow this assembly.

## Proved and sorry left

Original holes closed by assembly: `scalarSixCompactSupport` (one).
New holes: `scalarDenseRefinementSquare` (one), the square for a dense refinement
mapping to a potentially non-dense boundary compactification. It is only the second
of the original theorem's three independent clauses. Its source, complete schematic-
closure factorization and square-pasting argument, edge cases, and DAG attachment are
in its new module and node. No `sorry` occurs in a definition or private helper.

This is a decomposition, not a net hole reduction: one original hole replaced by one
strictly smaller hole. The isomorphism and composition clauses introduce no new holes.
The assembly uses existing theorems even where those theorems still contain `sorry`.

## No longer needed

Removed private imports from the item:
`Sheaf.SixFunctors.ScalarSixCtf`, `Sheaf.Paper.CompactificationLocalizing`,
`Sheaf.AlgebraicGeometry.ProperOpenSection`, and
`WeilConjectures.Compactification.CategoryBaseChange`.

Also removed the redundant public imports `Sheaf.Paper.ExceptionalInverseImageExistence`,
`Sheaf.Paper.FiniteConstantRingedLocalModel`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The latter three are already public transitive dependencies of the retained imports;
exceptional-image existence is unused by the statements and proof. The new split lemma
uses `sfbScalarCompactComparison` from the existing compositor module, avoiding an
otherwise unnecessary import of the entire closure-square proof during assembly.

The parent no longer directly needs these old proof dependencies:
`det-prop-scalar-six-ctf`, `det-prop-scalar-six-pullback`,
`det-sf-comp-coherence-cocycle`, `det-sf-comp-coherence-refinement`,
`det-sf-comp-coherence-single`, `lem-sfb-scalar-proper-open-interchange-square`,
`lem-sfb-scalar-refinement-closure-square`, `lem-weil-pbc-proper-open-section`,
`prop-compactification-refinement`, `sk-def-nagata-sketch-data`,
`sk-def-sfb-dc-setting`, `sk-lem-nagata-density-normalization`, and `sk-thm-existence`.
The new refinement lemma retains the normalization/refinement dependencies it needs;
the compositor lemma retains its own interchange dependency. These are changes of the
parent's direct proof dependencies, not claims that those modules can be withdrawn
from the whole library. Statement dependencies remain unchanged.
No module or declaration is withdrawn, and no source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

`scalarRefinementClosureSquare` has a narrower interface than the parent's second
clause: it assumes a dense pair or an actual closure inclusion and uses a separately
defined derived pushforward compositor. Thus direct application does not cover an
arbitrary non-dense receiving compactification. The new node isolates exactly the
schematic-closure factorization, identification of the two compositors, and pasting
needed to bridge that gap. The parent also takes arbitrary normalized pointwise
interchange maps whereas `scalarCompositeModelPasting` takes natural families. The
existing proved uniqueness/naturality helpers bridge this gap without a new hole.

## New nodes

`lem-sfb-scalar-dense-refinement-square`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-scalar-dense-refinement-square.json`,
records the dense-source/arbitrary-target square. Its statement is strictly one
clause of the original argument; it neither repackages nor implies the isomorphism
or composition clauses. No definition or statement changed, so no change record
is required.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
