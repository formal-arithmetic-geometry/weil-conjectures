## What changed

Proved the two original theorem holes in
`Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`, preserving every existing public signature,
visibility, definition and docstring. Added proved private helpers
`postnikovStep_quotient` and `eventually_constant_kernel`.

The quotient compatibility follows from good-truncation naturality and cancellation.
For convergence, prove the stabilization of truncation cohomology using Mathlib, apply
`ProEtale.milnor_epimorphic` to its epimorphic transition maps, and transfer that epimorphism
through the projection-compatible product comparison in `products_derived`. The concrete
mapping-cocone long exact sequence makes its first projection monic and a kernel. The
quotient family is another kernel, proved by the universal property of an eventually
constant tower. The specified comparison is their unique isomorphism on cohomology.

Added proof imports of `ProEtaleMilnorEpimorphic` and Mathlib's product-preservation API.
Updated the existing node's proof, proof dependencies and proof origin to match this route.
No public imports changed, no definition repairs, no consumer adaptations, and no new nodes.
The stage-3 interface checker conservatively reports the proof-only imports and private
section helpers as a context change; this is documented in
`coord/changes/proetale-left-complete-proof-context.md`.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Scheme.ProEt.postnikovComparison_condition`.
- `AlgebraicGeometry.Scheme.ProEt.left_complete_quasiIso`.

Both belong to `det-pe-left-complete-iso`. No direct `sorry` remains in the module;
zero holes were added and zero were split off. The proof uses the existing stated
`products_derived` and `ProEtale.milnor_epimorphic` theorems. In the current sources,
`products_derived` is proved and `ProEtale.milnor_epimorphic` remains a separate work item.
This is a proof from the project's declared dependencies, not a claim that their transitive
axiom closures are already sorry-free. The retained proof compiled through `lcompile.py`
on 2026-10-19 in 16.4 seconds with exit code 0 and no warnings, after checking
the retained delivery against the current shared sources.

## No longer needed

No existing imports removed: the public imports supply the existing constructions and
preserve the interface; the two original proof imports are used by the completed proof.

The convergence proof does not need `det-pe-left-complete-truncation-tower`, module
`Sheaf.AlgebraicGeometry.ProEtaleLeftCompleteTruncationTower`: its required stabilization
and limit universal property are proved directly from Mathlib and the concrete quotient
maps, so no cyclic import is needed. No claim is made that this module has no other users.

The theorem `milnor_sequence` of `det-pe-milnor-sequence` is not needed as a proof premise:
the concrete cone exact sequence and `det-pe-milnor-epimorphic` supply precisely the maps
and vanishing needed here. Its module stays publicly imported for the existing Milnor/Roos
constructions used in signatures. The corresponding proof dependency was removed from the
node; its statement dependency stays.

## Where the brief, the DAG or earlier work was wrong

The proposed use of `truncation_tower_cohomology` would close an import cycle: that module
already imports this one for the Postnikov construction. Also, `milnor_sequence` only
existentially quantifies its short-exact-sequence maps, without the projection formula
needed for the last identification. The implemented proof avoids both interface problems
by using the concrete mapping-cocone triangle and proving the eventual-constant kernel
property. Its tail begins at `(-q).toNat`, including q >= 0 and the zero/empty-site cases.
The unit's route through stabilization, vanishing of the Milnor obstruction, and the
canonical comparison is preserved.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
