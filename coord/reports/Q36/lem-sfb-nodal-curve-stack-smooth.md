# Stage-1 delivery: lem-sfb-nodal-curve-stack-smooth

Q36, 2026-10-22. Direct delivery. No Lean was written and no compiler or build tool was run.

## Files written

All node paths are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-nodal-curve-stack-smooth.json`: item, eight proof steps.
- `lem-sfb-artin-representable-diagonal-criterion.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-descent-isom-spaces.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-limit-preservation.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-infinitesimal-pushout.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-tangent-finiteness.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-formal-effectivity.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-curve-openness-versality.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-space-nodal-locus-base-change.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-isolated-lci-curve-smooth-open.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-separated-space-dimension-one-scheme.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-flat-lfp-space-universally-open.json`: statement, unsplit, no Mathlib match.

`citations.json` supplies all 22 step citations as verbatim statement quotations. `searches.jsonl` is the unedited search-command log; `research/` retains the actual query outputs. Eleven new nodes, zero Mathlib leaves.

## Attachments

None. Searches of the read-only project `lean/WeilConjectures/` by the blueprint tag and nodal-curve/stack, curveStack, Artin criterion and versality terms found no declaration of this item. Scheme-only results and sorried declarations are not attachments.

## WANTED

None. Every mathematical source used is present under `literature/stacks-project/`. No SGA source is cited.

## Corrections and scope

The imported assertion is true. No target is changed and no STATEMENT-DISPUTED is needed. A final wording check explicitly makes atlas representability mean representability by algebraic spaces, consistently with the source. I clarified its definition references: `def-trf-nodal-geometric-fibres` imposes CONNECTED fibres, which this item does not. The statement now cites the actual completion/power-series definitions and explicitly permits disconnected curves. Its reference to stable-pointed moduli groupoids is replaced by the algebraic-space definition and explicit stack/atlas conventions. Algebraic-space properness and chartwise flatness/presentation are specified inline, rather than applying scheme-only definitions silently to spaces. None of this adds stability, markings, a genus condition or connectedness.

Stacks 0DSY permits empty fibres; the item excludes them. Step 5 therefore intersects the usual nodal open with the open nonempty-fibre image of the flat locally finitely presented family. This is necessary to prove exactly the imported assertion. The ambient isolated-lci locus also permits empty and disconnected curves.

There was no earlier split or sandbox report. The item's original provenance, source, searches and long blueprint from/via chain are preserved. `blueprint_refs.py ancestor` gives no imported ancestor for this chain; new nodes retain its null `from.node`, prepend this item to its via list and specify the exact input place. No chapter or unit is edited: this is a prerequisite below an existing item, not the unit's key theorem. Whole-blueprint searches have no matching imported algebraic-stack result.

## Not duplicates

No existing unmerged node has the new source tags 07Y4, 0D52, 0D53, 0D55, 0D56, 0D57, 0D58, 0D59, 0DSH, 0DZX, 0ADD or 042S (`research/same-tags.json`). I also searched all DAG statements by concept and the whole blueprint (`research/blueprint-searches.json`).

lem-sfb-space-nodal-locus-base-change vs lem-trf-nodal-open-locus: the existing theorem is about schemes whose nonempty geometric fibres are already pure of dimension one; the new theorem is for algebraic spaces with arbitrary fibre dimensions. It must also remove smooth zero-dimensional components. The existing theorem does not apply to all of C.

lem-sfb-flat-lfp-space-universally-open vs lem-weil-pbc-flat-lfp-open: the existing Mathlib leaf is `AlgebraicGeometry.UniversallyOpen.of_flat` for SCHEMES; its recorded match and source were read. The new theorem 042S is for algebraic spaces and requires passage through etale presentations, not one-line specialization.

lem-sfb-isolated-lci-curve-smooth-open vs lem-sfb-nodal-curve-stack-smooth: the new result assumes algebraicity of the ambient stack and concerns the strictly larger isolated-lci locus. A proper cuspidal curve belongs to that locus but is not nodal. It proves neither ambient algebraicity nor nodal openness. Steps 4–7 supply the omitted constructions and inclusion.

lem-sfb-separated-space-dimension-one-scheme vs lem-sfb-stable-and-smooth-family-open-loci: the latter only supplies schemeness on a stable genus-g open; the new result works for every separated locally finite-type space over a field of dimension at most one, without stability or properness.

The separate Artin inputs assert descent/Isom spaces, limits, infinitesimal gluing, tangent finiteness, formal effectivity, and open versality. None asserts the algebraicity conclusion or repeats an item clause. Elementary open intersections, atlas restrictions and the image-of-complement argument remain steps, not new nodes.

## Mathlib research

For every new node and the item I executed the required msearch command with two distinct LeanFinder phrasings, Loogle, grep, and LeanSearch. All services returned successfully. Each node records exactly its executed queries and complete returned output, also retained under `research/`. The official log was not edited. Searches were made before writing the new node files, and the source-tag audit was repeated against the current read clone.

I read the returned signatures. Artinian-scheme results do not give Artin's algebraicity criterion; ordinary scheme gluing and pushout-section comparisons do not glue proper algebraic-space families across thickenings. `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` descends morphisms of schemes, not curve-space groupoids. Ring formal smoothness and cotangent vanishing do not state finite-dimensional deformation/automorphism spaces of a proper curve. Hits for “universal” do not mean openness of versality. `Lagrange.nodal` is polynomial interpolation. Smooth scheme morphisms and open ring smooth loci do not assert smoothness of moduli stacks. The genuine flat-openness hit was read in Mathlib's UniversallyOpen source and is restricted to schemes. No candidate provides a one-line specialization to any new statement.

## Review by Q36

I read the complete item proofs in moduli-curves.tex 0DSY (`lemma-nodal-curves`) and 0E00 (`lemma-nodal-curves-smooth`), the algebraicity proof in quot.tex 0D5A and their surrounding definitions. The route remains Artin algebraicity, the proper image of the bad locus, then inclusion in the isolated-lci smooth open. I did not substitute the stable-curve compactification theorem that this prerequisite is supporting.

For the generic criterion I read artin.tex 07Y4, section-axioms [-1]–[3], definition-versal and definition-openness-versality. It is specialized to Spec Z, where the G-ring condition holds; it does not claim the criterion over an arbitrary nonexcellent base. The cardinal bound and both tangent and infinitesimal-automorphism finiteness are included. All hypotheses are defined in its statement instead of referring to numbered axioms for their meaning.

I read the statement and proof of each new curve input in quot.tex: 0D52 and 0D53 for descent and Isom spaces; 0D55 for limits; 0D56 for pushouts; 0D57 for tangent spaces; 0D58 for effectivity; and 0D59 for versality. The pushout node specifies its two maps, thickening and affine hypotheses and the 2-fibre groupoid. Formal effectivity includes the complete Noetherian local base and coherent transition identifications. Limits include arrows and eventual equality. The versality test is identical in the criterion and its input. These are genuinely separate requirements and not statements of the algebraicity conclusion.

For the remaining new nodes I read spaces-more-morphisms.tex 0DSH, including the etale-chart construction of its universal open; moduli-curves.tex 0DZX, its smoothness and field-point characterization; spaces-over-fields.tex 0ADD, which supplies a schematic neighbourhood at every point in dimension at most one; and spaces-morphisms.tex 042S, whose statement explicitly covers algebraic spaces. The isolated-lci node assumes ambient algebraicity, matching the point at which it is used. The separatedness and local finite type needed for 0ADD are present in step 6 because its geometric fibre is proper of finite presentation.

I opened and read every cited existing node's statement. Step 1 takes precisely descent and Isom representability from its input, and uses the explicit universe convention for the size condition. Step 2 checks every separate Artin premise: it does not infer tangent finiteness from the diagonal alone, and it uses effectivity only on bases allowed by the input. Step 3 identifies the 2-fibre product on objects and arrows, uses the actual algebraic-space fibre-product statement for Isom spaces, and uses smooth relative-dimension permanence on fixed-dimension scheme chart opens. Nonemptiness after field extension is the elementary nonvanishing of a tensor product over a field.

Step 4 constructs an open in the TOTAL space using 0DSH, then uses properness to remove the closed image of its complement from the base. I checked compatibility after arbitrary base changes fibre by fibre: a nonempty field fibre remains nonempty after field extension. Mere containment of an image in a stratum would not give a factorization; here it is an open characterized by the entire geometric fibres. Step 5 uses 042S to handle the extra nonempty requirement, then writes out the open intersection and restricted atlas. An empty family over a nonempty base belongs to the open of step 4 but not the one of step 5.

Step 6 applies the spaces-to-schemes input BEFORE the scheme-only `lem-trf-nodal-curve-lci-criterion`. Its closed-point condition follows from the item's stronger geometric-singular-point condition. The Fitting smooth-locus theorem needs flatness, local finite presentation and geometric purity: over the geometric field, flatness is automatic, presentation comes from the family and purity is exactly its geometric-fibre condition, including further algebraically closed extensions. Step 7 uses `pqf-lem-locnoeth-lft` for local Noetherianity, finite type for quasi-compactness, and the unramified local criterion for closedness of every point of the Fitting singular scheme. The closed immersion makes these points closed in C. Thus `lem-sc-noetherian-closed-points-finite` applies to X=C and that closed subset. Finiteness of the singular set is not an uncited assertion. Step 8 uses precisely the field-point and smoothness clauses of 0DZX. A complementary closed set with no geometric points is empty, so factorization through this open follows. Restricting a smooth atlas to an open preserves its lifting condition, since a nilpotent thickening has the same underlying points. Base-changing the atlas proves the field-extension clause. Off-unit generic inputs are declared in `split_report.tool_uses`.

Small cases checked: empty space and empty base; smooth proper curves; disconnected smooth curves; nodal reducible curves and self-nodes, including characteristic two; a proper cusp (in lci+ but not nodal); zero-dimensional curves and the disjoint union of a curve and a point (in C but not N); and a nonreduced double curve (not automatically in lci+ or N). Constant formal systems and trivial pushouts satisfy the new statements. Separatedness in 0ADD and completeness in effectivity are not dropped. All eight proof steps have fewer than 2000 characters. No new node is elementary or assumes the item or its conclusion.

## What remains

The one-level split is complete. Its eleven new prerequisites intentionally remain statement-only nodes for the queue. No Lean proof or compilation is claimed. The required remote dry run and direct push are the remaining delivery actions.

## Delivery checks

The first remote dry run passed (receipt 2b8f1b803ae). A final wording clarification of atlas representability and the elementary open-restriction lifting argument is being checked in the final dry run before push.
