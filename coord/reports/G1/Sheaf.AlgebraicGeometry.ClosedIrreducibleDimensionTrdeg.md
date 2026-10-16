## What changed

Proved `AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg` in
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`, preserving its signature and all
public imports. The proof follows all six original DAG steps. A fully proved private helper
`integral_dimension_trdeg` carries the integral affine-chart argument. It uses the existing
finite-type domain dimension theorem and Mathlib's fraction-field API. The proof explicitly
checks both base-field compatibility diagrams, including the canonical algebra structure in
the conclusion. Added the proof-only import `WeilConjectures.PointCount` for
`Scheme.Hom.residueFieldAlgebraMap_comp`.

Updated the existing node's proof text to identify the Lean constructions and the naturality
identities used; its proof dependencies and source route are unchanged. No definitions,
public statements, other modules, or target signatures changed.

Validation: local single-file compilation passes without errors or warnings after removing
redundant imports. The required `deliver3.py --no-push` dry run is recorded by the tool.
Sources checked: the official Stacks pages for [0A21](https://stacks.math.columbia.edu/tag/0A21)
and [0B1C](https://stacks.math.columbia.edu/tag/0B1C), especially reduction to an affine open
in the proof of part (6). The local `literature/stacks-project` texts are absent on this machine.
Mathlib, the existing dimension theorem, and the DAG statements were read locally. Fresh
LeanFinder, Loogle, and grep searches found no direct theorem for the whole statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg`
(node `lem-sc-closed-irreducible-dimension-trdeg`).

The new private helper `integral_dimension_trdeg` is completely proved. No `sorry` remains
in the item, and no hole or new public statement was added elsewhere. This is a proof from
existing declarations, not a decomposition into new admitted statements. The imported
`topologicalKrullDim_opens_eq` and `finiteType_domain_ringKrullDim_eq_trdeg` are the planned
existing dependencies; the delivery makes no claim to close their transitive dependencies.

## No longer needed

Removed these redundant direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.RingTheory.KrullDimension.Basic`

Their relevant declarations remain available from the imports that the proof actually uses.
No original DAG proof dependency is pruned: the argument follows the original six steps,
including the generic Mathlib tools for closed immersions, finite type, dimension invariance,
and the function field. No claim is made that any of the five removed direct import modules
leaves the targets' transitive import closure. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction was needed. The prescribed hypotheses suffice.
The quasi-compactness hypothesis and the explicit membership proof `hηC` are stronger than
this argument needs, but their signatures were preserved. Irreducibility supplies nonemptiness;
closedness is used to obtain the concrete reduced subscheme and in identifying its generic
point with the given point. The reducedness instance is supplied explicitly by
`reduced_induced_closed_subscheme`; it is not assumed for an arbitrary ideal subscheme.

The unit `sk-prop-sf-cbc` has no realized statement or steps in its record. The existing
support-dimension tool route is unchanged. There are no new nodes or forced adaptations.

## Second reading by G1

1. Compared the delivered module with the repository version. The target theorem signature
and every existing declaration are byte-for-byte unchanged. The only Lean changes are its
proof, a private helper, and proof-only imports; the DAG changes only proof prose. Verdict:
pass.

2. Compiled the item with `lcompile.py` and compiled a scratch copy with `#print axioms`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations
in the delivered module. The target depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Verdict: pass.

3. The target statement is unchanged and its hypotheses are sufficient: the reduced induced
closed subscheme is integral, the affine chart is a finite-type domain, and the residue-field
algebra equivalences preserve transcendence degree. No split-off statement or new node was
added, so there is no additional statement to validate. Verdict: pass.

4. Traced the proof from the reduced induced subscheme through the affine fraction-ring
calculation and the closed-immersion residue-field equivalence. The unit route and all six
original DAG steps remain represented. Removed direct imports are redundant; `PointCount` is
retained as a proof-only import for `residueFieldAlgebraMap_comp`. Verdict: pass.

5. The node's proof text now records the concrete Lean constructions and identities used;
its `proof_deps`, source route, chapter, unit, and Lean declaration still agree with the
module. No new nodes or change records are required. Verdict: pass.

Second reading changed only this report section. No Lean repair, statement change, or DAG
dependency change was necessary.
