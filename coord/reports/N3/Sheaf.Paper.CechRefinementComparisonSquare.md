## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cechRefinement_comparison_square` from the
new resolution-level diagram theorem in `Sheaf.Paper.CechRefinementResolutionDiagram`.
The original theorem's signature and existing public imports are unchanged. Added
only a proof import of the new module and the proved private helper
`resolution_map_postcompose` for cancellation in the existing resolution formula.

The proof obtains both total-homology squares from the diagram, evaluates the two
`IsModuleCechComparison` equations, and substitutes them by equality congruence and
transitivity. It cancels the target resolution identification and `H(alpha)` using
`moduleCechAlpha_isIso`, then cancels the inverse resolution identification in
`ModuleCohomologyFMapData.map`. Neither Cech comparison is assumed invertible.

The remaining lemma has no canonical Cech comparison hypotheses or conclusion.
It concerns the augmentation and global-section squares for concrete resolution data,
with the sections morphism explicitly calculated from beta and lambda. It does not
assume that the target family covers. The source covering and the alpha square
uniquely determine its existential map; no data definition chooses that witness.

Both files compile locally without errors or warnings. A long initial transport
calculation was replaced with equality congruence and a private algebraic lemma;
the last individual compile of the original module took 26.2 seconds. No heartbeat
or time limits were raised in the delivered files.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.cechRefinement_comparison_square`
(node `lem-sc-cech-refinement-comparison-square`). Its module has no remaining sorry.
The private `resolution_map_postcompose` is also fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_cechRefinement_resolution_diagram`
(node `lem-sc-cech-refinement-resolution-diagram`), in its own new module. Its entire
proof is `by sorry`, with the resolution-diagram proof in its docstring and node.
This is a decomposition: one hole closed, one added, net zero. The substantive
remaining work is construction of the refinement resolution diagram, not the
canonical comparison substitution or resolution-transport cancellation.

## No longer needed

No original imports were removed: `CechRefinementCochainMap` and
`ModuleCechComparison` are needed by the original signature.

The old planned dependency `lem-sc-cech-comparison-map-naturality`, module
`Sheaf.Paper.CechComparisonMapNaturality`, is not used by this proof. Its theorem
provides naturality for coefficients on one scheme and one fixed cover; it does
not supply the cross-scheme refinement diagram. The parent node's proof dependencies
now name the actual resolution diagram and comparison/cohomology definitions.
This is local DAG pruning, not a claim that the module is unreachable from every
other project target. No other node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The node's sole proof dependency, `cechComparisonMapNaturality`, does not state the
refinement or cross-scheme compatibility required by the node's prose. Its signature
has one scheme, one cover and a coefficient morphism. The missing part is now the
resolution diagram lemma; the original statement was not changed.

Checked Stacks Tag 01FD at https://stacks.math.columbia.edu/tag/01FD, including the
four-double-complex diagram and the augmentation pentagon. The local literature
checkout contains citation lists but not `literature/stacks-project/cohomology.tex`.
The new lemma follows that same diagram, specialized to the tensor-pullback unit.
The source-cover condition suffices for the inverse total comparison; the target
cover is needed only when the final theorem cancels its alpha map.

Mathlib searches were run with leanfinder, loogle, grep and leansearch, recorded in
`searches.jsonl`: leanfinder returned restriction/naturality/sheaf-condition lemmas;
loogle returned no hits; grep found only unrelated Stone-Cech refinements;
leansearch returned an internal server error, recorded as unavailable. Local searches
in both library roots found no applicable existing resolution diagram. Blueprint
search for refinement found 44 entries, none stating this module-level diagram.

Edge cases checked mathematically: p = 0 uses the same augmentation equation;
zero modules give zero maps; an empty source cover forces X empty; an empty target
family is allowed by the new lemma, whose target Cech total is then zero. No cover
is required to be affine, finite or acyclic. The fixed unit route is retained;
the generic total-column comparison and pushforward-injective acyclicity are tools
for its existing Cech-resolution argument.

## New nodes

`lem-sc-cech-refinement-resolution-diagram` states the two resolution-level
squares with an explicitly specified sections map calculated from the existing
`ModuleCohomologyFMapData`. Its new module is
`lean/Sheaf/Paper/CechRefinementResolutionDiagram.lean`. It removes both canonical
comparison maps from the hypotheses, and the main theorem proves their transport
and cancellation. Source: Stacks Tag 01FD, the resolution double-complex diagram.
No existing statement, definition or public import changed; no change record or
forced adaptation is required.

## Second reading by N3

1. **Visible interface: PASS.** Read both delivered modules and the repository diff.
   Compared the original theorem signature byte for byte, including all hypotheses,
   typeclass parameters, and conclusion: identical. The existing docstring, options,
   and public imports are unchanged. No existing definition is changed. The only
   added import in the original module is a plain proof import. The existing node
   differs only in `proof`, `proof_deps`, and `proof_origin`.

2. **Proof and axioms: PASS, conditional decomposition.** Independently compiled
   both modules through lcompile.py in import order (34.8 and 24.3 seconds), with
   no errors or warnings. Scratch copies with explicit `#print axioms` also compiled.
   `cechRefinement_comparison_square` and
   `exists_cechRefinement_resolution_diagram` use exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the private
   `resolution_map_postcompose` uses only the three permitted axioms.
   The sole textual hole is the complete proof of the named public diagram theorem.
   No forbidden declaration, hollow definition, or new data choice occurs. The
   intermediate map is unpacked only in a proof, not installed as a data definition.
   One original hole closes and one lower hole is added: net zero, not an axiom-free
   proof of the item.

3. **Split statement: PASS.** Checked the two resolution-level equations, scalar
   forgetting identifications, inverse orientations, and augmentation against the
   actual fields of ModuleCohomologyFMapData and Stacks Tag 01FD. The lemma omits
   both canonical comparison maps and proves the resolution-level portion of the
   argument; the original module independently performs comparison substitution
   and cancellation. It is not the original statement renamed. Its source and
   complete diagram proof are in its docstring and new node. In the column argument,
   restriction to each source intersection is exact, restrictions of injectives
   remain section-acyclic, and products of the section quasi-isomorphisms are exact
   in module/abelian-group categories. Thus the total comparison applies also to
   infinite covers. Checked p = 0, zero modules, identity refinement, empty source
   cover (forcing X empty), and empty target family (zero target Cech total). A
   non-covering target family needs no invertible target alpha: only the source
   alpha is inverted to determine t. The remaining diagram construction is not a
   hole that can be closed by a short categorical simplification.

   Independent searches used different queries: leanfinder for chain maps between
   Cech injective-resolution double complexes (eight generic injective-resolution
   lift results); loogle for `"homologyMap", "total"` (zero hits); and grep for
   `Cech.*(map|natur)|cech.*(map|natur)` (two Cech-nerve hits). The launcher recorded
   them in searches.jsonl. Also searched both source roots and read
   ModuleCechLiftSquares, ModuleCechComparison, CechComparisonMapNaturality,
   PushforwardInjectivesSectionsQuasiIso, and FirstQuadrantTotalComparison.
   The existing lift squares require one scheme and one fixed family of opens;
   they do not supply the cross-scheme refinement diagram. No exact duplicate found.

4. **Route and pruning: PASS.** The top proof first uses the existing alpha
   isomorphism and resolution formula, leaving only the missing diagram portion.
   Its imports serve the unchanged signature or the actual proof. The sole old
   planned dependency, `lem-sc-cech-comparison-map-naturality`, is fully listed under
   No longer needed; no removed public import or globally unreachable module is
   claimed. Read dag/units/sk-prop-av-cube.json, including its realized fields.
   This below-unit refinement reduction preserves the existing general-cube route
   and does not bypass any realized unit statement or step.

5. **Nodes: PASS after formatting repair.** The parent node's proof describes the
   equations and cancellation actually used and its dependency union agrees.
   The new node contains its source, self-contained statement, proof steps and
   dependency union, search records, split status, creation/blueprint/unit/chapter
   fields, and Lean record. All dependencies have existing declarations. Replaced
   its single-line normalized lean.statement with the multiline theorem signature
   verbatim from the delivered file. This changes no mathematical statement.

Second reading changed only this review report and the new node's signature
formatting. The Lean proof and split statement required no repair. No additional
holes were closed or introduced during the second reading.
