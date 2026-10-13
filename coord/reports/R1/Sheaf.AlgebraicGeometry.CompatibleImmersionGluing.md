## What changed

Proved `AlgebraicGeometry.Scheme.exists_gluedCompatibleImmersionCharts` in
`Sheaf.AlgebraicGeometry.CompatibleImmersionGluing`, preserving its full signature and
original public imports. Added the proof-only import `Mathlib.AlgebraicGeometry.Gluing`.
Two private, fully proved helpers implement the existing node's first two steps:
`compatibleImmersion_openOverlap` identifies the overlap with an open restriction, and
`exists_gluedMonoOpenAtlas` constructs actual `Scheme.GlueData`, including its triple maps
and cocycle identity. The main proof establishes chart saturation and explicitly constructs
the Cartesian universal property. Updated the existing node's proof to describe the Lean.
No definitions, public signatures, other library modules, or unit routes change.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_gluedCompatibleImmersionCharts`
(node `lem-sc-compatible-immersion-gluing`). Both private helpers are fully proved.
No `sorry` remains and no holes were added or split off. This is a proof, not a decomposition.
The module compiles cleanly through `lcompile.py`; the delivery dry run checks the axioms.
The proof accommodates empty S, empty patches, and an empty gluing index type.
It needs no pointwise covering hypothesis to construct these particular Cartesian charts;
the original `hU` binder is preserved unchanged.

## No longer needed

None. No original imports were removed. The existing dependencies
`lem-weil-pbc-glue-schemes` and `lem-weil-pbc-scheme-morphism-gluing` remain realized by
Mathlib scheme gluing and its multicoequalizer mapping property. No nodes or modules are
pruned, and neither temporary intermediate module is delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's route is implementable with Mathlib's gluing API;
no additional unresolved theory is needed. Tag 0BDL omits the gluing details; the proof here
supplies them using Tags 01JB and 01JC. These three source pages were read.
The unit record has no bound realized statement or step for this auxiliary node, and its
existing route is retained. LeanSearch was unavailable; LeanFinder, Loogle, and source
searches were run. They located the gluing APIs but no exact compatibility-interface theorem.

## Second reading by R1

1. Compared the complete delivered Lean file and node with the repository using `diff`.
   The only existing declaration, `exists_gluedCompatibleImmersionCharts`, has a
   byte-for-byte identical signature, including `hU`, all quantified test schemes,
   the factorization equivalence, and the Cartesian conclusion. No existing
   definition or public import changed; the added gluing import is proof-only.
   The node differs only in `proof` and `proof_origin`. Verdict: pass.
2. Independently compiled the module with `lcompile.py` (2.6 seconds, no warnings).
   A scratch copy with `#print axioms` for both private helpers and the main theorem
   compiled and reported exactly `propext`, `Classical.choice`, and `Quot.sound`
   for each. Read every construction and proof: compatibility is applied to the
   actual open restriction, the pullback inverse uses cancellation of the monic
   structure map, the triple maps satisfy the stated cyclic cocycle, and the final
   cone lift has both triangles and uniqueness. There is no unresolved proof or
   data chosen from an unproved existence theorem. Verdict: pass.
3. No statements were split off and no holes were added. The two private proved
   helpers are strictly intermediate parts of the original node's argument.
   Checked empty base, empty index type, empty patches, diagonal overlaps, and
   disjoint patches: neither helper assumes a point exists, and the glued empty
   atlas has no points by joint surjectivity. The unused covering hypothesis is
   harmless: the conclusion only asks for Cartesian charts, not coverage of S.
   Verdict: pass.
4. Read [Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL), final paragraph,
   and the constructions and mapping property in
   [Tag 01JB](https://stacks.math.columbia.edu/tag/01JB) and
   [Tag 01JC](https://stacks.math.columbia.edu/tag/01JC).
   Independently searched LeanFinder for gluing monomorphisms with open pullback
   projections, Loogle for gluing data, and Mathlib and both local library roots
   for compatible immersions and gluing. LeanFinder found local representability,
   pullback-cover gluing and locally directed gluing; these require additional
   interfaces and give no shorter direct replacement here. Loogle's unqualified
   `Scheme.GlueData` query was not recognized. Read Mathlib's GlueData fields,
   chart lemmas and the upstream Gluing module. Both imports are used: Immersion
   in the signature and monicity, Gluing in the construction. Neither old
   proof dependency is obsolete: scheme gluing constructs the atlas, and its
   multicoequalizer mapping property glues the morphism. No pruning is warranted.
   `sk-prop-av-cube.realized` contains no binding to this auxiliary node; the
   unit route and records remain unchanged. Verdict: pass.
5. Checked the node's three steps against the two helpers and final proof.
   The overlap range formula feeds chart saturation, and saturation feeds the
   open-immersion lift establishing the Cartesian square. The two `proof_deps`
   are exactly the union of step `uses`, and their Mathlib leaf records supply
   scheme gluing and morphism gluing. `proof_origin` accurately describes the
   implemented argument. There are no new nodes or change records. Verdict: pass.

Changes by the second reader: added this independent review only. The Lean proof,
imports and node needed no repair. Confirmed one original hole closed and zero
holes added; no decomposition and no pruned modules.
