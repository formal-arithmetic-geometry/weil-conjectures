## What changed

Proved `CategoryTheory.cohomologicalGeneratorDetection` in
`lean/Sheaf/CategoryTheory/CohomologicalGeneratorDetection.lean`, with its signature and
public imports unchanged. Added proof-only imports of
`Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four` and
`Mathlib.CategoryTheory.Preadditive.Yoneda.Limits`.

Three fully proved local helpers assemble the five-term exact rows, apply Mathlib's
five lemma, and identify the component on a coproduct with the isomorphism of limiting
vertices. The main proof checks stability under shifts and isomorphisms, establishes
coproduct and triangle closure, and performs the induction and telescope step of
`compactGenerators_buildObjects`. These helpers implement steps 1 and 2 of the existing
node; they introduce no independent postponed statements.

Updated the existing node's proof text to describe these Lean constructions. The route,
proof dependencies, source, unit, statement, and public interface are unchanged. The
unit's `realized` lists contain no statement or step assigned to this node; its original
Brown-representability route is preserved. Checked the cited source paragraphs online:
[Stacks 0A8F](https://stacks.math.columbia.edu/tag/0A8F), final paragraph, and
[Stacks 09SN](https://stacks.math.columbia.edu/tag/09SN), telescope construction.

## Proved and sorry left

Closed: `CategoryTheory.cohomologicalGeneratorDetection`
(node `lem-pc-cohomological-generator-detection`), the only original hole in this module.
No holes remain in the delivered module, and no holes were added or split off.
The three local helpers are fully proved.

The theorem is proved from the existing
`CategoryTheory.compactGenerators_buildObjects`
(node `lem-pc-compact-generators-build-objects`), whose own proof is still `sorry` in the
current library. That is an existing stage-3 dependency, not a hole introduced by this
work. This delivery proves the assigned node from its planned dependencies; it does
not claim the transitive proof is free of `sorryAx`.

Local single-file compilation passed without warnings. The delivery dry run also
checks every declaration's axioms and the module's interface.

## No longer needed

None. All original imports are needed for the unchanged statements or the proof.
Both added proof-only imports are used. All planned dependencies are retained:
representable exactness (`lem-weil-pbc-hom-out-of-triangle-exact`) is supplied through
Mathlib's homological preadditive Yoneda instance, general homological exactness by
`Functor.map_distinguished_op_exact`, the five lemma by its recorded Mathlib match,
and generator construction by `compactGenerators_buildObjects`. No node or module is
removed from the planned route. No new import is needed for a separate theorem about
homotopy-colimit closure: the existing telescope triangle and triangle closure suffice.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was necessary. The source file
`literature/stacks-project/derived.tex` is absent from this machine's read-only clone;
the cited Stacks pages were read online instead. The proof uses rotated transition
and telescope triangles to place the unknown object at the middle vertex, where the
five lemma applies. This is precisely the original argument, with the rotation made
explicit in Lean. Empty indexing families and zero objects require no extra hypothesis:
the coproduct proof uses only its universal property and the supplied limit-preservation
hypothesis, and the generator construction already covers those cases.

## Second reading by W2

1. PASS — Compared the complete module and node with the read-only repository using
   `diff -u`. The existing theorem signature, section assumptions, docstring, visibility,
   and public imports are byte-for-byte unchanged. The only Lean changes are the theorem
   proof and two ordinary proof-only imports. No definition or interface change is present;
   no change record or forced adaptation is needed.
2. PASS — Compiled the delivered module through `lcompile.py`: exit 0, no warnings
   (3.6 seconds). Scanned for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and
   `extern`: none occur. A scratch copy with `#print axioms
   CategoryTheory.cohomologicalGeneratorDetection` compiled and reported exactly
   `[propext, sorryAx, Classical.choice, Quot.sound]`. The existing open dependency
   `compactGenerators_buildObjects` explains `sorryAx`; the delivery adds no hole.
   The existential construction is eliminated inside a theorem proof, never used to
   define arbitrary data from an unproved existence statement.
3. PASS — No statement was split off and no new declaration or node was introduced.
   Read all three locally proved helpers: the exact row has vertices X[1], Z, Y, X,
   Z[-1]; naturality gives its commuting squares; the five lemma supplies its middle
   isomorphism. The coproduct fan uses the actual coproduct universal property and
   identifies its induced limiting-vertex isomorphism with the requested component.
   Empty families and zero objects introduce no missing assumptions. Independently
   searched Lean Finder with an isomorphism-locus/closure query and searched the
   library and Mathlib triangulated files with alternative terms. No direct generator
   detection or natural-transformation closure theorem was found; the available
   homological-kernel lemmas concern functor values or maps, not this transformation.
4. PASS — Read the proof from the requested component down through shift-zero
   transport, the rotated telescope, induction on the transition triangles, and the
   coproduct/triangle helpers. Mathlib supplies the exactness, five lemma and limit
   comparison; the sole open construction is the existing planned generator theorem.
   Both added ordinary imports provide declarations/instances used by the proof;
   original public imports supply the unchanged signature. No old proof dependency
   is bypassed: representable exactness is supplied by Mathlib's Yoneda instance,
   whose source proof invokes `Triangle.yoneda_exact₂`; the five lemma is the node's
   recorded Mathlib match. Thus `## No longer needed` is complete with none removed.
   Read `dag/units/sk-thm-picard-duality.json`: its `realized` lists are empty and this
   delivery changes no unit realization or unit route. Checked the final closure
   argument in [Stacks 0A8F](https://stacks.math.columbia.edu/tag/0A8F) and the
   construction in [Stacks 09SN](https://stacks.math.columbia.edu/tag/09SN).
5. PASS — The existing node changes only the three proof-step descriptions. Each
   matches the corresponding Lean helper or construction step. Its `proof_deps`
   remain the union of the steps' `uses`, and `proof_origin` remains the cited
   document. Statement, source, unit, chapter and Lean declaration record are unchanged.

Second reading changed only this report: added the independent checks and their
verdicts. No Lean repair or node repair was necessary. Closed one original hole,
`CategoryTheory.cohomologicalGeneratorDetection`; added zero holes, split off zero
statements, and pruned no module. This is a proof relative to the existing open
construction dependency, not a claim that the transitive closure is axiom-clean.
