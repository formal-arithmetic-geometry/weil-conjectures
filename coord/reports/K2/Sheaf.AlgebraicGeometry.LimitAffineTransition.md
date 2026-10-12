## What changed

Proved `AlgebraicGeometry.exists_limit_affine_transition_core` from the relative-spectrum
anti-equivalence, the existing quasi-coherent algebra colimit theorem, and one new geometric
preservation lemma. The private, completely proved `hasLimit_affineOver` constructs a limit
in the full category of schemes affine over a fixed base: it builds the algebra colimit,
creates it in the quasi-coherent full subcategory, transfers it through the anti-equivalence,
and takes opposites. The core proof constructs a directed upper tail and its initial opposite
inclusion, lifts the diagram over the chosen stage, applies the preservation lemma, uses
Mathlib's preservation of connected limits by `Over.forget`, and transfers the limit back
along the initial inclusion. Existing public signatures, definitions, and docstrings are
unchanged. The already proved affine comparison and final theorem are unchanged.

Added proof-only imports `Mathlib.CategoryTheory.Limits.FullSubcategory`,
`Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`,
`Mathlib.CategoryTheory.Adjunction.Limits`, and
`Sheaf.AlgebraicGeometry.AffineOverLimitInclusion`. Each is used in the proof. The new split module privately imports
`AffineMorphismRelativeSpec` and `QuasiCoherentAlgebraColimit`, the declared plan
dependencies needed for its remaining proof.
Updated the core node's proof and dependencies to follow this Lean argument.

## Proved and sorry left

The item's sole original sorry, `AlgebraicGeometry.exists_limit_affine_transition_core`
(node `lem-weil-pbc-limit-affine-transition-core`), is closed by a complete Lean proof.
`hasLimit_affineOver` is also proved. All three public theorems of the item have complete
proof bodies. They still depend transitively on unfinished library declarations.

The delivery adds exactly one sorry:
`AlgebraicGeometry.isLimit_affineOver_inclusion`, in
`Sheaf.AlgebraicGeometry.AffineOverLimitInclusion`, node
`lem-weil-pbc-affine-over-limit-inclusion`. It says that an EXISTING limit cone among
schemes affine over S is limiting among all schemes over S. It neither asserts nor
constructs existence. Its full proof in words uses relative-spectrum charts, sectionwise
colimits over affine base opens, spectrum limits, and gluing; arbitrary intersections are
covered by affine opens, never assumed affine. Nonempty directed indices are essential.
For a singleton index the claim is immediate; for empty S all schemes over S are empty;
non-quasi-separated bases and non-affine test schemes are explicitly allowed in the gluing
argument. The new theorem's statement has no affine-transition hypothesis: maps between
schemes affine over S are affine, as checked on each affine base open.

Both delivered modules compile with lcompile in import order, without warnings.

## No longer needed

None: no existing import was removed, and both original proof imports are now actually used.
The core no longer cites `lem-weil-pbc-spec-colimit-limit` and
`lem-weil-pbc-scheme-morphism-gluing` directly; these are still needed by the new preservation
lemma and are not pruned from the target closure. No unit statement or realized step is
bypassed, and the relative-spectrum route of Stacks 01YX is retained.

## Where the brief, the DAG or earlier work was wrong

The core node supplied only the prose 'full relative-spectrum construction', despite having
all four planned dependencies. The delivered proof makes the actual categorical construction,
upper-tail cofinality, and transfers explicit; the remaining geometric gluing argument now
has its own precise preservation statement. No existing statement was found false.

LeanSearch was unavailable (HTTP internal server error); the search record says unavailable.
LeanFinder, Loogle, Mathlib source search, project source search, and blueprint search found
no exact preservation theorem. Mathlib's generic full-subcategory limit results require
an ambient limit and cannot prove this inclusion preserves the constructed limit.

WANTED: `literature/stacks-project/limits.tex`, Tags 01YX and 01YW, for the new node.
The literature file is absent in this checkout; the second reader checked the official
web versions at https://stacks.math.columbia.edu/tag/01YX and
https://stacks.math.columbia.edu/tag/01YW. The natural-language argument is recorded
with agent proof origin, using the source locations supplied by the existing nodes.

## New nodes

`lem-weil-pbc-affine-over-limit-inclusion`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-over-limit-inclusion.json`, realized by
`lean/Sheaf/AlgebraicGeometry/AffineOverLimitInclusion.lean` and
`AlgebraicGeometry.isLimit_affineOver_inclusion`. This isolates the ambient universal
property from the completely proved fixed-base limit construction. Its dependencies are
the existing relative-spectrum, algebra-colimit, spectrum-limit, and morphism-gluing nodes.
There are no changed public interfaces of existing modules and no change records.

## Second reading by K2

1. Compared the entire item with the repository using diff. All three existing public
   declaration signatures, definitions and docstrings are byte for byte unchanged.
   Changes are a proved private helper, the core proof, and private proof imports.
   No change record is required. Verdict: pass.
2. Compiled both modules locally in import order. Scanned all delivered Lean for forbidden
   declarations and for sorry: exactly the named inclusion theorem remains sorry, no
   definition is hollow. Scratch-copy axiom checks and the delivery's whole-file probe
   verify only propext, Classical.choice, Quot.sound and transitive sorryAx. Verdict: pass.
3. Read the split-off inclusion theorem and its full docstring argument. It asserts
   preservation for an already existing limit, not existence, so is strictly one part
   of the construction. Singleton J and empty base cause no exception; arbitrary,
   non-quasi-separated bases and non-affine tests are covered by the local argument.
   Nonemptiness ensures each local factorization is over the base by composing one
   projection. Checked Stacks 01YX and 01YW online. Independent LeanFinder, Loogle,
   Mathlib and project searches found no exact theorem. The upstream finite-approximation
   limit theorems require a special system and qcqs base. Verdict: pass; no quick
   formal proof of the geometric preservation step was found.
4. Read the proof from the core downward: construct the quasi-coherent algebra colimit,
   transfer through the anti-equivalence, prove upper-tail initiality and functoriality,
   then use inclusion preservation and connected Over.forget preservation. All item
   imports serve this route; private imports in the new module now name its planned
   Sheaf proof dependencies. Both old dependencies removed from the core's proof_deps
   are listed under No longer needed, and remain dependencies of the inclusion lemma.
   Read dag/units/sk-thm-p1.json realized: no realized statement or step is bypassed.
   Verdict: pass.
5. Checked both delivered JSON nodes against the Lean signatures and proof. The core's
   dependency union matches its proof. The new node has source, full proof, searches,
   provenance, creation, blueprint, chapter, unit and Lean fields. Verdict: pass.

Changes made: added private imports of AffineMorphismRelativeSpec and
QuasiCoherentAlgebraColimit to the split module, made explicit in its docstring and node
why local factorizations are over the base and restrict to overlaps, recorded independent
searches and online source verification. No Lean proof or statement was changed.
