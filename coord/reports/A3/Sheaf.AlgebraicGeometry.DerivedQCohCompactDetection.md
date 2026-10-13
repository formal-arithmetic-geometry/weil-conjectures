## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.derivedQCoh_compact_detection` with a complete Lean proof,
without changing its statement, universes, visibility or public imports.
Added the proved private helper `AlgebraicGeometry.compact_shift`, adapted from
`CategoryTheory`'s private shift-compactness calculation in BrownTelescopeAssembly;
this has no hole and introduces no public API.

The proof imports `Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration` and
`Mathlib.CategoryTheory.Adjunction.Additive`. Compact generation supplies the
triangulated structure and a compact generating family directly in the chosen
model. The hypothesis transports to every target shift by the shift adjunction.
In a cone triangle, injectivity at shift 1 and surjectivity at shift 0 make every
map from a compact object to the cone zero. Shift adjunction and coproduct
extensionality let the weak generating family force the cone to be zero;
Mathlib's `Triangle.isZero₃_iff_isIso₁` finishes.

Updated only `proof`, `proof_deps` and `proof_origin` of node
`lem-sc-derived-qcoh-compact-detection` to describe this route.
No definitions or other modules were changed. The unit
`sk-thm-picard-duality` has empty realized statement and step lists; no fixed
unit realization is bypassed. The perfect-generation argument remains in the
reused compact-generation theorem.

Source checks: read [Tag 09IS](https://stacks.math.columbia.edu/tag/09IS),
[Tag 09M1](https://stacks.math.columbia.edu/tag/09M1), and the detection paragraph of
[Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R).
The local literature files are absent on this remote machine; the source tags
were read online. Read the compact-generation theorem and its node, the
compact-object and weak-generator definitions, and the Mathlib triangle exactness
and zero-cone signatures. LeanFinder found no direct detection theorem; Loogle
found `isIso_of_yoneda_map_bijective` (unnecessary because Mathlib has the zero-cone
criterion); grep located the same criterion and the existing generation proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.derivedQCoh_compact_detection`
(node `lem-sc-derived-qcoh-compact-detection`), 1 of 1 original holes.
Added holes: none. Sorries left in the item's module: none.
`AlgebraicGeometry.compact_shift` is fully proved.
This is a proof from existing library statements, not a decomposition into new
holed statements. Existing transitive dependencies of compact generation can
still contain `sorry`; this delivery does not claim that the target import
closure is axiom-free.

The final module compiles without errors or warnings with the mandated
`lcompile.py` (approximately five seconds). The shift-compactness helper works
for arbitrary integer shifts and universe-u indexing types without requiring
small Hom types. The cone argument makes no choice of a generator index, so
an empty generating family and an empty scheme are included. All coproduct
instance changes are between proofs of the same proposition.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration`
- `Sheaf.AlgebraicGeometry.PerfectObjectCompact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`

The original direct proof edges to
`lem-pc-derived-qcoh-perfect-generation`, `lem-pc-perfect-object-compact`,
`prop-pur-kinjective-resolutions-exist` and
`lem-pc-derived-category-locally-small` are replaced by compact generation and
formal triangle/shift reasoning. Perfect generation and perfect compactness
remain needed transitively by the compact-generation theorem. Local smallness
and K-injective resolutions are not used directly by this proof; their modules
may remain reachable through other dependencies, so no whole-closure pruning
count is asserted. All three original public imports remain necessary for the
unchanged statement. An exploratory import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` was also removed;
the needed sigma-comparison facts are already available.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan demanded a separate
small-Hom-model transport and an explicit localizing-closure argument here.
Those steps are unnecessary: the existing compact-generation theorem handles
the arbitrary ambient Hom universe and encapsulates perfect generation.
The existing theorem docstring preserves the original valid mathematical plan;
the updated DAG and the Lean proof use its compact-generator consequence.
The exactness used is covariant `Hom(P,-)`, represented by
`lem-weil-pbc-hom-into-triangle-exact`, with rotation for exactness at the cone.

## Second reading by A3

1. PASS: compared the sole delivered Lean module against the repository with
   `diff -u` and compared the existing theorem signature as bytes. The signature,
   universes, public visibility, public imports and all definitions are unchanged.
   Only the proof, private proved helper and plain proof imports differ. There
   are no interface change records or forced adaptations to review.
2. PASS: independently compiled the module using `lcompile.py`, with no errors
   or warnings. The module contains no holes, axioms, unsafe declarations, opaque
   declarations or foreign implementations, and adds no definition. A scratch
   copy with `#print axioms` reports only `propext`, `Classical.choice` and
   `Quot.sound` for `compact_shift`; the main theorem additionally reports
   `sorryAx` from existing open dependencies, as permitted for this reduction.
   Reviewed the additive comparison square, shift-adjunction conjugation,
   injectivity at the connecting map, covariant cone exactness, surjectivity
   lifting and coproduct extensionality. No arbitrary object is selected from
   an unproved existence theorem in the delivered code: existential witnesses
   are eliminated within the proof of a proposition.
3. PASS: no statement or hole was split off and no new node was added. The
   private compactness helper is fully proved for arbitrary integer shifts and
   separate coproduct/Hom universes. Empty coproducts, an empty generator family,
   the zero category and shift zero introduce no missing hypotheses. Independent
   Loogle search for `IsCompactObject`, LeanFinder search for preservation by
   additive equivalences, and ripgrep searches of Mathlib and both library roots
   found no public direct replacement. BrownTelescopeAssembly has the same
   private helper; CompactGeneratorTelescopeIso has a related cone argument but
   additionally requires telescope data and larger-universe coproducts, so it
   cannot shorten this proof in the stated generality.
4. PASS: compact generation is reused in the original derived model, followed
   by the formal cone criterion. Re-read the compactness and generating-family
   definitions, compact-generation theorem and the source statements at
   [Tag 09IS](https://stacks.math.columbia.edu/tag/09IS),
   [Tag 09M1](https://stacks.math.columbia.edu/tag/09M1) and
   [Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R).
   Both added imports are proof-only. Removing Adjunction.Additive in a scratch
   copy fails at `homAddEquiv` and `homAddEquiv_symm_zero`; compact generation is
   used explicitly. The three retained public imports supply the unchanged
   statement. Every old proof dependency removed is listed under No longer
   needed. Re-read the unit record: its realized statement and sole realized
   step are empty, and this subsidiary node does not bypass the unit's curve
   duality route. No whole-closure pruning claim is made.
5. PASS: compared the node JSONs; exactly `proof`, `proof_deps` and
   `proof_origin` differ. The union of step dependencies equals `proof_deps`.
   The shift, compact-generator and triangle-exactness dependencies agree with
   the code (cone exactness is the rotated covariant Mathlib lemma). The Lean
   record and natural-language statement are unchanged; no new nodes need
   field validation.

Second reading changed only this report by adding the independent checks and
explicit axiom results. No repair to the Lean proof or node was needed.
