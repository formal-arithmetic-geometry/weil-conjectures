## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal` by a complete Lean combination
of two source steps: existence of a local morphism with prescribed numerator pullback,
and rigidity of local morphisms with equal numerator pullbacks. Each step is a new
public theorem in its own new module, with a complete proof in words and a DAG node.
The private proved helper `affinePullback_comp` establishes source naturality for all
sheafed-space morphisms, without locality assumptions. From existence and rigidity the
main proof establishes bijectivity, constructs the unique spectrum map for a monoid
homomorphism, and proves target naturality by functoriality and associativity. The
hypothesis that Q is fine is retained verbatim, although this final assembly does not
need it. No target, shared definition, or existing declaration signature changes.

Converted the assigned file to module syntax and added proof-only imports for the new
modules. Import changes are recorded in
`coord/changes/V2-affine-monoscheme-hom-universal-imports.md`. No other existing module
is delivered. There are no existing direct Lean importers of the assigned module.

Read ILO Exposé VIII, printed pp.98--99 (PDF pp.104--105), the original seven-step
node, its declared dependencies and signatures, the current blueprint unit, and the
current claims/returns/rework records. Mathlib searches returned ring-spectrum
adjunctions and elementary monoid-localization lift/ext results; these do not supply
local morphisms of the ordinary monoid sheaves. No shorter noncircular route was found.

## Proved and sorry left

This is a decomposition, not a completed proof of the universal property: one upper
hole is closed and two strictly smaller holes are added, net minus one hole. There
were 1 and are now 0 direct sorries in the assigned module. The two new modules each
have 1 sorry. `affinePullback_comp` is completely proved without the new lemmas.
`AlgebraicGeometry.Monoscheme.affine_hom_universal` is completely proved FROM them;
its transitive proof still depends on their sorries.

Holes closed:
- `AlgebraicGeometry.Monoscheme.affine_hom_universal`, node
  `lem-trf-affine-monoscheme-hom-universal`.

Holes added and left, each as the entire proof of one public theorem:
- `AlgebraicGeometry.Monoscheme.exists_local_affine_hom`, node
  `lem-trf-affine-monoscheme-hom-existence`, module
  `Sheaf.AlgebraicGeometry.AffineMonoschemeHomExistence`.
- `AlgebraicGeometry.Monoscheme.local_affine_hom_ext`, node
  `lem-trf-affine-monoscheme-hom-ext`, module
  `Sheaf.AlgebraicGeometry.AffineMonoschemeHomExt`.

The existence lemma is the construction/locality/pullback part of original steps
1--4 and 6, and says nothing about uniqueness or naturality. The rigidity lemma is
original step 5 and asserts no existence. Neither imports the parent or the downstream
spectrum_hom_universal restatement. Their combination and both naturality proofs are
real Lean proof terms in the assigned file. The split introduces no chosen data or
hollow definition.

Edge cases checked mathematically: empty source (the unique empty-space sheaf map),
trivial P and P a group (one-point spectrum and units), P the free monoid on one
generator (unit versus nonunit germ), an empty unit-germ locus, torsion units, and
nonintegral target stalks. The inverse-uniqueness argument does not cancel in the
source stalks and imposes no sharpness assumption. All universes and hypotheses stay
those of the original theorem. Single-file remote compilation validates the complete
combining proof and the two separate statement modules; delivery also runs its axiom
and mechanical checks.

## No longer needed

Removed the direct imports of `Sheaf.AlgebraicGeometry.FineFanBlowup` (redundant
through the public MonoschemeToricRealization import) and
`Mathlib.Topology.Sheaves.SheafCondition.Sites` (unused in the completed assembly).
The latter's basis-extension theorem and
`lem-trf-monoid-prime-minimal-neighborhood` are no longer DIRECT proof dependencies of
the assigned theorem; both remain needed in the two new source-step nodes. They are
not claimed as globally pruned. No existing module or node is withdrawn, and no unit
statement or unit proof route is bypassed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The assigned file still had a legacy header; its sandbox version now uses the required
module header. The original plan correctly describes the mathematical argument, but
the declared definitions and minimal-neighborhood result alone do not formally supply
the needed existence and rigidity of sheafed-space maps, so these are now independent
proof items. In particular, passing from the localization description to the actual
sheafification and stalk maps remains in these source steps, rather than being hidden
in the combining proof.

The base contains the stronger `MonoidSpectrumHomUniversal.spectrum_hom_universal`
restatement (in namespace AlgebraicGeometry.Monoscheme), but its DAG proof depends
on this item. An initial sandbox probe considered projecting its clauses; that route
was discarded on reading its current node. The delivered imports and proof contain
no such dependency. The two new nodes cannot cite this parent and do not do so.
The original unit and its current blueprint text are preserved.

## New nodes

`lem-trf-affine-monoscheme-hom-existence` realizes original steps 1--4 and the numerator
pullback check of step 6 of ILO VIII 3.1.8(i). Its public theorem is in the new module
AffineMonoschemeHomExistence. It asserts only existence for a prescribed section map,
not a bijection or an equivalence. Its source proof records construction of the prime
map, gluing inverse sections, extension on the basis, locality, and the D(1) check.

`lem-trf-affine-monoscheme-hom-ext` realizes original step 5 of the same proof. Its
public theorem is in the new module AffineMonoschemeHomExt. It recovers the point map
by locality, then the maps on fractions by inverse uniqueness, then the sheaf map by
basis extensionality. It is a uniqueness assertion and asserts no existence.

Both nodes inherit the chapter, unit, and historical blueprint ancestor of the parent.
Each records LeanSearch, LeanFinder, and grep searches, all read for exact hypotheses.
The parent node now records the proof actually written, with these two proof
dependencies. Change record:
`coord/changes/V2-affine-monoscheme-hom-universal-imports.md`.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
