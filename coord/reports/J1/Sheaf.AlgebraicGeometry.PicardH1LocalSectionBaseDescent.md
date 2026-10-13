## What changed

Repaired reviewer X-3e89d C1 (review point 6): added the missing existing-theorem node
`lem-sc-generates-at-of-generates-at-sum` and appended it to both the reflection node
first proof step uses and proof_deps, preserving all previous entries. No Lean theorem
was duplicated and no Lean source, signature, import, or hole changed in this repair.

Repaired D2 by replacing the entire unresolved generator auxiliary with a compiled proof
combining fibre-generator existence, local lifting of a prescribed fibre section, and
reflection of generation along tensor pullback. The reflection theorem is fully proved
using adjunction uniqueness and the singleton case of the source library's
`exists_generatesAt_of_generatesAt_sum`. The two geometric steps are separate new modules
with named, source-backed sorries. The item's signature is unchanged.

Repaired D by deleting the three specified unused proof imports. Repaired C1 by recording
`invertible_pullback_tensor` in the item's second proof step and `proof_deps`. Repaired B2
by spelling out every object, hypothesis and local-free-generation conclusion in the
generator node, citing both definition nodes. Updated the generator route and all new
nodes to match the Lean proof. No existing statement or definition changed.

## Proved and sorry left

Closed the item's original hole in `picard_h1_local_section_of_base_descent` (1 of 1).
Also closed the returned auxiliary hole in
`picard_h1_local_section_of_base_descent_generator`, which is now a complete combination
proof. Proved `AlgebraicGeometry.Scheme.Modules.tensorPullback_generatesAt_reflects`.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.picard_h1_base_descent_fibre_generator`, node
  `lem-sc-picard-h1-base-descent-fibre-generator`. This only constructs a section on the
  residue fibre; it has no target-family or H1 hypotheses and no base neighbourhood.
- `AlgebraicGeometry.Scheme.picard_h1_base_descent_section_lifting`, node
  `lem-sc-picard-h1-base-descent-section-lifting`. This lifts any prescribed fibre section
  after shrinking, with no generating-section conclusion. Its neighbourhood may depend
  on the section, so residue-field denominators can be inverted.

No other delivered declaration contains `sorry`. This is a decomposition: against the
original item one hole is closed and two are added, not a net proof gain. Against the
returned delivery, its equivalent generator hole is replaced by these two strictly
separate geometric steps. The local generation of the lifted section is proved in Lean.
All five delivered modules compiled cleanly with `lcompile.py --all`.

## No longer needed

Removed BaseChangeConventions, TensorPullback, WeilConjectures.AlgebraicGeometry.Modules.Invertible, WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree, PerfectDirectImageBaseChange, PerfectFiniteFreeResidueModel, and FiniteFreeMapResidueLocalization from the item's module because its proof does not use them directly. The perfect-complex dependencies remain in the generator module.

After the D2 repair those perfect-complex dependencies are reached through the generator's
`PicardH1BaseDescentSectionLifting` import; their three direct proof imports are in that
new module. They remain needed for the lifting step and are not globally pruned.
The four imports removed before this repair and the three deleted in this repair are
all seven imports listed above. Removed the generator's unused direct
`NonvanishingGeneratingLocus` import; the equivalence is applied only in the item's module.
Removed unused `Ample` public imports from the three new geometric modules and the unused
`StructureSheafCohomologyPullback` import from the fibre-generator module.

The parent node now uses only the generator node,
`lem-weil-pbc-invertible-pullback-tensor`, and `lem-sc-nonvanishing-iff-generates-at` directly.
The old perfect-complex nodes `lem-pc-rf-perfect-base-change`,
`lem-sc-perfect-finite-free-residue-model`, and
`lem-pc-finite-free-map-residue-localization` remain needed by the lifting node.
No previously needed mathematical node is claimed globally unnecessary.

Every old parent proof dependency is no longer a direct dependency: `def-pc-base-change`,
`def-pc-module-pullback`, `def-weil-residue-field`, `def-sc-invertible-module`,
`def-amb-finite-locally-free-module`, `lem-pc-rf-perfect-base-change`,
`lem-sc-perfect-finite-free-residue-model`, `lem-pc-finite-free-map-residue-localization`,
and `def-weil-pbc-ample-invertible-module`. The geometric definitions and perfect-complex
lemmas remain in the split statements or their planned proofs; the ample/nonvanishing
definition remains in the parent signature. These are direct-edge changes, not global pruning.

## Where the brief, the DAG or earlier work was wrong

C1 dependency rereading: with the reflection module, corrected reflection node, new
finite-sum node and source theorem open, I checked the exact application at lines 81-83.
It specializes g to j, X to Y, Y to Z, the index to Unit, s to {()}, every coefficient
to 1 and every section to sigma; hp is converted to the singleton-sum hypothesis by
simp. The source SheafOfModules invertibility instance is explicitly supplied. The
conclusion is precisely GeneratesAt sigma (j y). Both corrected dependency arrays
retain all five original entries followed by the new node. The new node records the
full theorem rather than only its singleton specialization. The empty-set case is
impossible by the coefficient/basic-open proof, and no field or finiteness-of-scheme
assumption is added. The unit route stays unchanged. This is the repair author’s
repeat dependency reading; the earlier independent second-reading claim that all
non-elementary dependencies were recorded was incomplete and must be rechecked by
the second reader before delivery.

The returned generator statement was equivalent to the original statement by
`mem_nonvanishingLocus_iff_generatesAt`; changing the conclusion predicate was not a
strict reduction. Its earlier report and second-reading point 3 were incorrect.
The repair proves that auxiliary from distinct fibre triviality and section-lifting
statements, and a proved general generation-reflection theorem.

The parent DAG omitted the explicitly used pullback-invertibility theorem; it now records
it before applying the nonvanishing equivalence. The generator node previously referred
back to the parent's hypotheses; its statement now gives them in full.

Edge cases checked: an empty comparison family uses degree-one rank zero; the restriction
statement allows shrinking to depend on the given fibre section (a single affine ring
need not surject onto the residue field at a nonclosed point); universal structure
pushforward excludes an empty marked fibre. Generation reflection holds for every scheme
morphism and uses only invertibility, its section equation, and generation at one point.
The earlier false arbitrary-section fibre proposal and vacuous section-existence proposal
remain excluded from the delivery. The unit's route is unchanged.

## New nodes

`lem-sc-generates-at-of-generates-at-sum` records the complete finite-sum theorem
`AlgebraicGeometry.Scheme.Modules.exists_generatesAt_of_generatesAt_sum` from
`WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange` (line 77). Its record includes
the ambient schemes, morphism and module, invertibility, arbitrary finite index set,
coefficients, sections, marked point, generation hypothesis and existential conclusion.
It attaches to that existing proved declaration and adds no module or sorry. Searches
found no Mathlib or DAG duplicate; LeanSearch was unavailable.

`lem-sc-picard-h1-local-section-base-descent-generator` remains the now-proved combination
node. Its statement is self-contained and its proof dependencies are the two new geometric
steps, pullback invertibility, and generation reflection.

`lem-sc-picard-h1-base-descent-fibre-generator` is the fibre-triviality step in
`Sheaf.AlgebraicGeometry.PicardH1BaseDescentFibreGenerator`; its theorem remains sorry.

`lem-sc-picard-h1-base-descent-section-lifting` is the arbitrary-section lifting step in
`Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting`; its theorem remains sorry.

`lem-sc-tensor-pullback-generator-reflection` is the proved general reflection theorem in
`Sheaf.AlgebraicGeometry.TensorPullbackGeneratorReflection`.

Change record: `coord/changes/picard-h1-local-section-base-descent-generator.md`.

## Earlier second reading (a previous round; superseded)

The previous round's second reading is superseded by the maintainer's return. A fresh
second reader must inspect the repaired modules and nodes before delivering.

3. Correction to the previous point 3: the old generator predicate was equivalent to
nonvanishing and was not a strict intermediate statement. The generator is now proved
from fibre-generator existence and lifting of a prescribed fibre section, using the
proved tensor-pullback generation-reflection theorem. Neither unresolved statement
asserts the original generating-section existence over a base neighbourhood. This is
an author's repair note, not a new independent-reader verdict.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module with the repository version. The target declaration
   and every existing signature are unchanged; the only item change is its proof and proof-only
   imports. Verdict: pass.
2. I compiled all five delivered modules with `lcompile.py --all`. The item proof has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the two explicitly
   split geometric declarations are the only remaining sorries and each has a source-backed
   docstring and matching node. Verdict: pass.
3. I checked the split statements against their Lean types and edge cases, including an empty
   comparison family and a neighbourhood depending on the prescribed fibre section. They are
   strictly smaller than the original generator assertion, and the reflection lemma is proved
   from the existing singleton generation theorem. No duplicate library theorem was found.
   Verdict: pass.
4. I checked the proof from the top downward and the import pruning. The generator route keeps
   the unit's fibre-generator and lifting steps, while the parent uses the proved reflection
   lemma and pullback invertibility. Removed imports are listed above and the retained perfect-
   complex imports are still used by section lifting. Verdict: pass.
5. I compared each node's Lean declaration, proof steps, dependencies, origin, and unit against
   the delivered source. The generator node records the two geometric steps, invertibility, and
   reflection; the parent records the generator and its two direct lemmas. Verdict: pass.

I added this second-reading record only; no Lean source, statement, definition, or DAG node was
changed during the reading.

## Second reading by J1

1. I compared the delivered item module with the repository module. The theorem signature and all
existing declarations are byte-for-byte unchanged; only the proof and proof-only imports differ.
Verdict: pass.

2. I compiled all five delivered modules with `lcompile.py --all`. The item and generator and
reflection proofs contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The only remaining sorries are the two named geometric split theorems, each with a source-backed
docstring and matching DAG node. Explicit #print axioms checks show only propext, Classical.choice,
and Quot.sound for reflection, and those three plus sorryAx for the other four declarations.
Verdict: pass.

3. I checked the new declarations and their edge cases. The fibre-generator theorem is restricted
to constructing a generator on the marked residue fibre; section lifting only asserts lifting of an
arbitrary prescribed section and allows its neighbourhood to depend on that section. The reflection
theorem is proved from invertibility and the singleton finite-sum generation theorem. None restates
the item, and no duplicate existing theorem was found. Independent LeanFinder searches for
residue-fibre restriction surjectivity and a descended vector-space basis returned only general
affine, stalk and sheaf-generator tools; Loogle did not recognize GeneratesAt. A Mathlib grep
for residue sections and invertible descent found no matching theorem. Repository searches
confirmed the adjacent Picard local-descent theorem uses the item downstream, so cannot replace
its proof. I checked the geometric argument against Stacks Tag 0BF2 directly. Verdict: pass.

4. I checked the proof route from the target downward. The generator auxiliary uses the fibre
construction and section-lifting steps, then tensor-pullback generation reflection; the parent uses
that auxiliary, pullback invertibility, and the nonvanishing/generation equivalence. The unit route
is preserved, and imports removed from the parent and generator are listed above. The unit
record currently has empty realized arrays; this delivery leaves them unchanged and makes no
claim to complete that project-level record. Verdict: pass.

5. I checked each changed and new DAG node against the Lean declarations, including proof steps,
proof dependencies, proof origin, unit, and the existing finite-sum theorem dependency. The target
statement and definition interfaces are unchanged. Verdict: pass.

I changed this report only by adding this independent second-reading record; no Lean declaration,
statement, definition, or proof was altered during the second reading.
