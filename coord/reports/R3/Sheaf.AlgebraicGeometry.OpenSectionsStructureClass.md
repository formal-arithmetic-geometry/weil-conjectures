## What changed

Proved `AlgebraicGeometry.openComparison_structure_class` from one strictly ordinary
cycle-class equality in the new proof-only import
`Sheaf.AlgebraicGeometry.OpenSectionsOrdinaryStructureClass`.
The original statement and the existing structure-complex isomorphism are unchanged.

The private, proved `exact_single_iso` identifies the explicit derived restriction
isomorphism with the quotient of the ordinary complex isomorphism followed by the
inverse exact-functor factorization. The private, proved
`complexUnit_homology_naturality` combines naturality of homologyFunctorFactors with
naturality of the ordinary-to-derived complex unit. The theorem applies those two
identities, substitutes the ordinary cycle equality, and unfolds the canonical class
of one and restricted unit. No comparison equivalence or evaluation bijectivity is used.

Updated the existing node's proof, proof_deps, and proof_origin to match this reduction.
The new lemma has no derived-category assumptions and concerns only ordinary homology.
All original public imports are retained; the new import is not public.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.openComparison_structure_class`
(node `lem-sc-open-sections-structure-class`). No sorry remains in the item's module.
Both private transport helpers are completely proved.

Added one named hole: `AlgebraicGeometry.openComparison_ordinary_structure_class`
(node `lem-sc-open-sections-ordinary-structure-class`), in its own new module.
Its docstring gives the degree-zero cycle calculation and its source.
This is a decomposition: one upper hole closed, one strictly ordinary lower hole added,
net zero holes. It is not reported as a complete proof of the ordinary calculation.

The empty open and the zero ring are allowed: all unit sections are zero there and
all named maps still exist. The helper does not assume an affine open, a nonzero ring,
or any derived category. No data is chosen from an unproved existence theorem.

## No longer needed

No module imports removed; no modules pruned. The four original public imports are
needed by the unchanged statement and structure-complex definition.

The proof does not use `exists_openComparison_cohomology_model_iso` or
`derivedStructure_evaluation_one_bijective`. Their modules remain necessary for the
explicit ordinary/derived unit definitions and `derivedStructureGlobalOne`, respectively.
The direct dependency `def-sc-principal-open-alternating-total` moved to the ordinary
helper's argument; its definitions still occur in the original statement and helper.
None of these observations claims the corresponding module has left target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction or changed interface was needed. The original DAG's ordinary
cycle calculation was not supplied by its existing proof-dependency declarations;
it is now exposed as the strictly ordinary helper. The unit record
`sk-thm-picard-duality` has no realized route entries bypassed by this reduction.

The initially missing compiled OpenSectionsCohomologyModel dependency became available
on refresh. A transient import_direction.py read failure disappeared on retry.
Compilation used only the launcher; the repository was not edited and nothing pushed.

## New nodes

`lem-sc-open-sections-ordinary-structure-class` states the ordinary equality between
restriction of the structure unit cycle and the tilde/sections unit cycle, before any
derived unit is applied. This is step 2 of the existing node's proof, strictly smaller
than the original derived equality. Its module is
`Sheaf.AlgebraicGeometry.OpenSectionsOrdinaryStructureClass`; its source is the
ordinary tilde/sections unit underlying Stacks Tag 06Z0. Searches used LeanFinder,
Loogle and grep (LeanSearch was also attempted and returned Internal Server Error), followed by local searches of both roots and Mathlib. They found the
section-one and extension/single-homology ingredients but no complete equality.
No change records or forced adaptations are needed.

## Second reading by R3

1. Compared both delivered modules with the repository versions. Existing public declarations and definitions retain byte-for-byte signatures; only the main theorem proof, a proof-only import, and the new split theorem/module are added. Verdict: pass.
2. Compiled the delivered modules with `lcompile.py`; the delivery dry run also passed preflight. The main theorem has no `sorry`; the intentionally split ordinary theorem is the sole named `sorry`, with its docstring and DAG node. A scratch copy with `#print axioms` confirmed only `propext`, `Classical.choice`, and `Quot.sound` for `openComparisonStructureComplexIso`, and those plus `sorryAx` for both class theorems. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statement against the ordinary degree-zero cycle calculation and searched the project/Mathlib ingredients. It is strictly smaller than the derived target, true for empty opens and the zero ring, and has the required source, proof plan, and declaration metadata. Verdict: pass.
4. Checked the proof route and pruning. The proof uses the ordinary helper, exact-single transport, and naturality; no shorter imported route was found. The unit `sk-thm-picard-duality` route is preserved, and the report records that no imports or target-closure modules were pruned. Verdict: pass.
5. Checked that the DAG proof, proof dependencies, and proof origin match the Lean proof, including the new ordinary node and its module. Verdict: pass.

Changed after second reading: restored the original signature whitespace at the main theorem proof separator; appended this review section. No mathematical or interface changes.
