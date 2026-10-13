## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_map_basicOpen`
without changing its signature, public imports, or definitions. Added proof-only imports
of `FiniteFlatAffineBasis` and the new `TraceDiscriminantSectionGermGenerator` module.
Three private, fully proved helpers localize a finite basis, refine a free chart inside
an arbitrary affine chart, and identify the section ideal at a stalk with the local
principal discriminant ideal. The target then follows from affine stalkwise ideal
extensionality and the restriction/germ composition law.

The sandbox copies of `FiniteFlatAffineBasis` and `TraceDiscriminantSectionIdeal` are
byte-for-byte identical to the repository, retained only to compile the dependency
cache locally. They introduce no delivery changes.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_map_basicOpen`
(node `lem-sbc-trace-discriminant-section-localization`), one of one holes in the item.

Hole added: `AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_germ_generator_mem`
(node `lem-sbc-trace-discriminant-section-germ-generator`) in the new module
`Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionGermGenerator`.
This is the sole remaining sorry in these delivered modules and their proof closure.
The delivery is a decomposition: one upper hole closed, one strictly local reverse
membership hole added, net zero holes removed. The target is not yet sorry-free.
The new helper asserts only that a supplied local generator belongs to a stalk
extension; it does not assert the localization equality proved by the item.
No definitions, arbitrary witness choices, or private helpers contain sorry.

## No longer needed

No imports or modules are pruned. The old direct proof dependency
`lem-sbc-trace-discriminant-affine-restriction` is replaced in the localization node
by `lem-sbc-trace-discriminant-section-germ-generator`; affine restriction remains
a dependency of the new helper's finite-cover argument, so is not globally pruned.
`lem-sbc-finite-flat-affine-basis` remains used. The section ideal definition is
explicitly recorded among the proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly treated the new germ-generator module as an existing
helper with an existing node. The repository has neither that module nor its node.
It also called the result proved without distinguishing decomposition from net
progress, and left the localization node describing an unused denominator-clearing
proof. The second reading repairs the metadata and accounting. The basis and ideal
source copies merely repair this sandbox's local dependency cache; their source is
unchanged. An unused-variable warning in the private basis helper blocked delivery.

## New nodes

`lem-sbc-trace-discriminant-section-germ-generator` records the remaining local
membership statement, its complete finite-cover and denominator-clearing argument,
source, LeanSearch (unavailable), Loogle/LeanFinder and grep search records, and verbatim Lean signature. Source construction checked
against https://stacks.math.columbia.edu/tag/0BVH. No change records are needed:
no existing statement or definition changes.

## Second reading by N1

1. Compared every sandbox module with the repository. The target's existing
signature is byte-for-byte unchanged. The basis and ideal files are identical.
Only proof bodies, private helpers, and proof-only imports change in the existing
item. The germ-generator module is new and has its own node. Verdict: pass.

2. Compiled the four modules through lcompile.py. Fixed the private helper's
unused binder warning by spelling its quantified binder `_b`; the proof still uses
the introduced basis. Explicit #print axioms in a scratch copy shows only propext,
Classical.choice, Quot.sound and sorryAx for the target and its new helper; the
finite-flat basis theorem uses only the three standard axioms. Checked all source
for prohibited declarations/attributes and hollow definitions. Verdict: pass with
one explicitly recorded open theorem, not a completed sorry-free target.

3. Read the new statement and its full proof docstring. Compatible local
principal ideals on a finite principal free cover define an affine ideal;
localization preserves the finite intersection and agreement on overlaps gives
its local values. Comparing any free subchart identifies this ideal with the
explicit intersection. This yields the claimed generator membership without
assuming the item's localization theorem. Rank zero gives discriminant one and
the unit ideal; discriminant zero gives automatic membership; y in V excludes an
empty V; r = 0 in the item is handled by vacuous stalk extensionality. Searched
lean/Sheaf and lean/WeilConjectures and used leanfinder, loogle and grep, plus attempted LeanSearch (service unavailable), with new
queries. Existing IdealSheafData localization requires compatibility already and
would be circular here. No duplicate found. The helper is strictly the reverse
local membership step, not a renamed equality. Closing it requires formalizing
the finite-cover construction and was not a few-minute repair. Verdict: pass.

4. Read from the target through the stalk comparison and basis refinement.
The reduction uses Mathlib ideal_ext_iff, germ_res and localizationLocalization
and the proved existing finite-flat basis theorem before the one open helper.
The imports are needed for signatures or proofs; new proof imports are plain
imports. Listed the replacement of the old direct affine-restriction dependency
above; it remains needed indirectly. Checked sk-prop-input-spreading's statement,
steps and realized fields: this lower-level discriminant reduction bypasses no
unit step and changes no unit route or realized field. Verdict: pass.

5. Updated the localization node's proof, proof_deps and proof_origin to the
actual stalkwise route. Added the missing helper node with its source, dependencies,
searches, creation and blueprint provenance, and Lean record. Existing node
statements, signatures and unit associations stay unchanged. Verdict: pass.

Second reading changed the warning, added the missing DAG node, updated the
localization DAG route, corrected the new-node and hole accounting, and completed
this review report. The first preflight requested the distinct LeanSearch kind;
recorded its service failure explicitly and kept the successful other searches. No mathematical proof body was rewritten beyond the binder.
