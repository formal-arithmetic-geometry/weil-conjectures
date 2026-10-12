## What changed

Replaced the sorry in `AlgebraicGeometry.affine_structure_algebra_full_faithful` with a
compiling proof, preserving its complete signature and existing docstring. Added the
proof-only import `Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps`. Updated the original
node's proof, proof dependencies, and proof origin to describe this reduction.

Faithfulness is proved directly from Mathlib: restrict to inverse images of affine opens,
use `ext_of_isAffine` and the section formula for `resLE`, and then use
`Scheme.hom_ext_of_forall`. This proof uses only affineness of the target over S.
Fullness transports the supplied algebra morphism along hobj, uses the new local theorem,
glues with `Scheme.Cover.glueMorphisms`, proves the over-S condition by cover uniqueness,
and computes the section maps using `comp_appLE` and the top-section isomorphisms.
Equality on the affine basis and hmap identify the result with the supplied F-morphism.
The object transports and opposite-category morphisms are handled explicitly in Lean.

The new theorem isolates construction of local maps and their overlap compatibility;
it does not assert fullness, faithfulness, or existence of a global scheme morphism.
The original module performs the global assembly and proves all of faithfulness.
No target, definition, existing public interface, or unit route changed.

Validation: both modules compile cleanly through lcompile.py in dependency order.
The searches found the absolute Gamma-Spec correspondence, affine-target extensionality,
and scheme gluing, but no exact relative local-family theorem. LeanSearch returned an
Internal Server Error; this was recorded as unavailable, not as evidence of absence.
Read Stacks 01SA and 01LT on the Stacks website, since the literature source files are
not present in this clone. The new docstring and node spell out the local argument.

## Proved and sorry left

Proved/reduced `AlgebraicGeometry.affine_structure_algebra_full_faithful`
(node `lem-weil-pbc-affine-structure-algebra-fully-faithful`): no sorry remains in its
module. Its faithfulness argument is entirely proved from Mathlib. Its fullness
argument has a complete Lean proof from the new local construction theorem.

The delivery leaves exactly one sorry:
`AlgebraicGeometry.affine_algebra_local_maps` in
`Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps`
(node `lem-weil-pbc-affine-algebra-local-maps`). Its whole proof is `by sorry`.
Its docstring and DAG node contain the source and complete proof in words.
The three private helpers in the original module are completely proved.

## No longer needed

None. No original import was removed. Second reading removed the redundant new-module import
`Mathlib.AlgebraicGeometry.Gluing`: the remaining public imports already provide the
pullback notation and gluing declarations. This prunes no dependency node. All four original proof-dependency nodes remain
used: affine-morphism affineness, morphisms into affine schemes, scheme-morphism gluing,
and sheaf-morphism equality on a basis. The new local theorem is added to them.
No original node or module is proposed for pruning; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original proof dependencies are Mathlib leaves, rather
than additional Sheaf modules to import. Their actual Mathlib signatures were inspected.
The local construction requires no affineness of the source X; the new theorem states
this useful generality without changing the original theorem's hypotheses.

The overlap argument explicitly covers an intersection by smaller affine opens;
it never assumes the intersection is affine. The affine basis covers even the empty
scheme, so the Lean global assembly and uniqueness also handle empty schemes. The new
local statement was checked on the empty source/base, on identity algebra maps, and on
an affine base: these respectively give the empty map, restricted identity maps, and
the ordinary Gamma-Spec construction. No quasi-coherence hypothesis is needed for this
local morphism-construction step, since the algebra sheaves are already pushforwards
of structure sheaves and g is affine.

## New nodes

`lem-weil-pbc-affine-algebra-local-maps` states the local scheme maps associated to an
algebra morphism, the over-base condition, the prescribed section maps, and agreement
on pullback overlaps. It occupies the local construction and compatibility part of
original relative-spectrum step 6. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineAlgebraLocalMaps.lean`. Its proof uses the existing
nodes for affine morphisms, the Gamma-Spec correspondence, and scheme-morphism gluing.
The blueprint search for structure algebras, relative spectrum, and affine statements
found no separate blueprint statement of this compatible local-family assertion;
the new node records its provenance through the original node's blueprint ancestor.
There are no change records, because no existing statement or definition changed.


## Second reading by C1

1. Interface comparison: PASS. Read the full diff against the repository module.
The existing public theorem signature, hypotheses hobj/hmap, conclusion, notation,
and docstring are byte-for-byte unchanged. The added helpers are private theorems;
there are no changed definitions, target interfaces, or change records. The new
local theorem is the only added public declaration, in its own module.

2. Proof and compilation: PASS as a partial proof delivery. Compiled both files
in import order with lcompile.py, cleanly. Scratch copies with `#print axioms`
show only propext, Classical.choice, and Quot.sound for sheaf_eqToHom_app and
affine_over_ext; exists_over_map_of_algebra and the public theorem additionally
use sorryAx through the single named local theorem. The local theorem itself
also has precisely those four axioms. No forbidden declarations or hollow
definitions occur. The remaining sorry is exactly the whole proof of
AlgebraicGeometry.affine_algebra_local_maps, as listed above. This does not
claim an axiom-free proof of fullness.

3. Split statement: PASS. Its hypotheses are arbitrary schemes S/X/Y, arbitrary
f, affine g, and an O_S-algebra morphism alpha; its clauses give local maps over S,
equality on pullback overlaps, and the section formula with the topIso inverse.
These are true by the Gamma-Spec correspondence, the Under commutativity equation,
and naturality on smaller affine opens. Checked the arrow direction and both
top-section transports. For nested affine opens the comparison takes place in
Y_U, which is affine; arbitrary intersections are covered by smaller affine W,
so no separatedness hypothesis is hidden. Empty X, empty S, and empty inverse
images give the empty maps; identity alpha gives the restricted identity; for
affine S this is the ordinary relative Gamma-Spec construction. The e argument
is a proof of containment and adds no mathematical hypothesis: the over-S clause
implies it. The theorem is only local construction/compatibility, not the whole
full-faithfulness assertion. Its docstring contains a complete mathematical
argument, with the matching node and source. Independently reread Stacks
[01SA](https://stacks.math.columbia.edu/tag/01SA) and
[01LT](https://stacks.math.columbia.edu/tag/01LT). New LeanFinder query about a
ring homomorphism giving a scheme map compatible with the base, and Loogle query
`AlgebraicGeometry.Scheme, CommRingCat, (_ ⟶ _) ≃ (_ ⟶ _)`, found absolute
Gamma-Spec results, not this relative compatible-family statement. Independent
rg search for relativeSpec, relative_spec, and structure-algebra full faithfulness
found no replacement in lean/Sheaf or lean/WeilConjectures. Read
RelativeSpecMorphismChart: it assumes an already constructed equivalence and
imports this item, so it cannot replace the local construction. Closing the
remaining theorem requires the section-transport and overlap formalization,
not an immediate application of any of the search results.

4. Route and pruning: PASS after import repair. Read the affine_over_ext proof,
the cover-gluing helper, and both branches of the public proof. Faithfulness is
independent of the new sorry. Fullness constructs the global map, proves its
Over condition, computes the section maps, and proves equality on the affine
basis. All four old proof_deps remain used; No longer needed is complete. Read
sk-thm-p1.json realized: the reduction is below its unit steps, and removes or
bypasses none of its statement/step realizations. Removed the redundant public
Gluing import from AffineAlgebraLocalMaps and recompiled both modules successfully.
The original three public imports are needed by its signature; the local theorem
is imported only for its proof.

5. DAG agreement: PASS. Parsed the old and new item nodes: only proof,
proof_deps, and proof_origin differ. The original node describes the actual
faithfulness and global-assembly proofs; its dependencies are exactly the four
old nodes plus the local-map node. The local node has matching Lean signature,
source, word proof, dependency union, three search records (the unavailable
LeanSearch is explicitly recorded), creation/provenance, and chapter/unit fields.
Its statement includes no affineness of X, matching Lean and the mathematical
argument. Inspected all four original dependencies' Mathlib matches.

Second reading changed only the redundant new-module Gluing import and this
report (including its import-pruning account); no proof repair was needed.
