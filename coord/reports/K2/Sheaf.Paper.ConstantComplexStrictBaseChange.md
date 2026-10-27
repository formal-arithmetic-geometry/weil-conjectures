## What changed

The original strict base-change theorem is proved by assembling normalized scalar
reductions, finite geometric pullback, completed geometric pullback, and an explicit
signed Roos augmentation. Its signature is unchanged. The comparison interfaces
were moved verbatim into `Sheaf.Paper.ConstantComplexStrictBaseChangeData`, publicly
re-exported by the original module; the change record lists the declarations and users.
No existing coefficient functor is changed. The reduction tower exposes its
object function in a reducible wrapper while retaining the original sequence maps
and laws. The original normalization predicate is unchanged. The change record
contains the old and new tower definitions and the consumer audit.

The Roos augmentation is constructed as the mapping-cocone lift of the compatible
product of the reduction maps, with zero shifted component. The product kernel
identity, both projection equations, and scalar-chain-map naturality are proved.
Naturality uses the existing signed mapping-cocone API. Finite pullback exactness
uses the existing additive, finite-limit, and finite-colimit instances.

The geometric realization construction from the previous attempt is retained in
`scratch/`, not delivered. The three pending statements use the existing scalar
adjunction and tensor-comparison declarations in their proof plans. The explicit
Roos proof is independent of that unfinished geometric construction.

The quotient model and all three split statements compile, and the main theorem
compiled with profiling in 50.3 seconds. The final delivery compilation passed
for all six modules; its first preflight requested a metadata signature correction,
which is repaired in the node attachment. Profiling led to
the tower object-wrapper repair recorded above; all profiling options are
removed from the submitted Lean sources.

## Proved and sorry left

The original item has one hole:
`AlgebraicGeometry.ConstantComplexBaseChange.strict_constant_complex_base_change`.
Its proof now compiles without a local hole, using three split-off statements below.
This is a decomposition, not a net reduction in the number of holes: one original
hole is closed and three smaller holes are added.

The complete list of remaining holes in the delivery is:

- `AlgebraicGeometry.ConstantComplexBaseChange.normalized_reductions_exist`
  (`lem-a1-constant-complex-normalized-reductions`): scalar quotient transitions,
  compatible completed coefficients, balanced reductions and quotient-unit identities.
- `AlgebraicGeometry.ConstantComplexBaseChange.normalized_finite_pullback_exists`
  (`lem-a1-constant-complex-finite-pullback`): finite geometric comparison and its
  strict tower compatibility for supplied normalized towers.
- `AlgebraicGeometry.ConstantComplexBaseChange.normalized_completed_pullback_exists`
  (`lem-a1-constant-complex-completed-pullback`): completed coefficient map and
  geometric reduction square for supplied normalized reductions and finite comparison.

Each statement is a strict part of the original argument, has its own module and
DAG node, and has its source and complete mathematical proof in its docstring.
None includes the Roos augmentation or the entire original conclusion. No
postponed proof occurs inside a definition. All private helpers contain no `sorry`.
The relocated interface block was checked verbatim. The tower object-wrapper
change preserves the normalization proposition and all original tower maps.

## No longer needed

No module is withdrawn and no original public import is pruned: the relocated
interfaces are publicly re-exported. No existing source-library declaration changes. The Sheaf quotient-model
tower wrapper is adapted as recorded above.
The old proof dependencies remain either in the split arguments or in the unchanged
interfaces. In particular, a dependency used by a pending split is not claimed pruned.

The finite-pullback lemma takes the two normalized towers as inputs, so its proof
plan does not need the existence theorem `normalized_reductions_exist` a second
time. That incidental proof dependency was removed from its new node.

No geometric comparison dependency is claimed pruned from the pending finite and
completed arguments. The attempted realized-pullback module is not delivered and
has no import in the packet. Its experimental node is likewise not delivered.

The source proof's explicit exact-derived-factorization step is supplied already by
`FiniteComparison.derived`; the assembly needs no new private import of
`lem-weil-pbc-exact-functor-derived-factorization`. The exactness assertion is supplied
by existing instances, so the assembly also needs no private import of
`lem-pe-constant-left-module-inverse-image`. These declarations remain in the library;
their statement dependencies and consumers are preserved.

The attempted reducibility changes to coefficient functors are not delivered.
The original coefficient wrappers are preserved; the reduction tower exposes its object function. Unfinished
construction attempts and diagnostic probes are retained under `scratch/` and are
outside the delivery packet.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly suggested that writing the constructions without
literal holes amounted to a completed proof. Those constructions had not compiled.
The resumed work retains the attempts in scratch files, states their three distinct
mathematical conclusions explicitly, and delivers a compiling assembly and Roos proof.

The previous server storage failure no longer prevents compilation. No launcher
script was changed. The original statement, its scalar differentials, the completed
coefficient limit, and all generator normalization requirements are preserved.

The DAG records the three split arguments, the interface relocation, the tower
object-wrapper repair, and the signed-cocone dependency used by the Roos proof. It does not claim the three pending arguments proved.

## New nodes

- `def-a1-constant-complex-base-change-data`: the unchanged relocated comparison
  interfaces, including their existing inverse-image section owner dependency.
- `lem-a1-constant-complex-normalized-reductions`: pending scalar reduction argument.
- `lem-a1-constant-complex-finite-pullback`: pending finite geometric argument.
- `lem-a1-constant-complex-completed-pullback`: pending completed geometric argument.

Change records: `coord/changes/constant-complex-comparison-interfaces.md` and
`coord/changes/constant-complex-reduction-tower-objects.md`.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
