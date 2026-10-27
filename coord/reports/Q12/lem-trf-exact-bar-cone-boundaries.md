# Worker report: lem-trf-exact-bar-cone-boundaries

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-exact-bar-cone-boundaries.json`: statement, split; no full Mathlib match. Nine proof steps; existing statement and source fields retained.
- No new nodes and no Mathlib leaves created.
- `citations.json`: one verbatim statement excerpt for every use in every step.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the item id, bar-resolution terminology and derived-colimit names. The isolated `Rep.barResolution` occurrence is group-specific and does not state this item. No project declaration supplies all its clauses.

## Wanted literature

None. Read `literature/stacks-project/sites-cohomology.tex`, Tags 08PG (`example-left-derived-colimits`) and 08PH (`example-morphism-categories`), and `literature/stacks-project/derived.tex`, Tag 0152 (`lemma-derived-canonical-delta-functor`) including the preceding cone construction, and Tags 05S9, 05SU and 05SE for the derived comparison and its shift. The explicit comparison calculation is agent-written, and `proof_origin.by` records that.

## Issues found and corrections

The item is true with its existing, recorded cone convention. There is no statement dispute and no statement change. It was statement-only; the delivery supplies the proof. A triangulated structure by itself is insufficient justification for claiming that its comparison commutes with shifts. Step 5 therefore fixes the **canonical derived** shift by the existing Kan-extension/coherent-shift statements before step 6 uses that equation. The proof never claims uniqueness of a connecting arrow from the first two arrows of an arbitrary distinguished triangle.

The source and the node use the same negative projection in the cone triangle. I checked the kernel contraction directly: in degree r, dh(x,y)=(x,-dx), hd(x,y)=(0,dx+y), whose sum is (x,y). For the bar augmentation the hypothesis is quasi-isomorphism, not a claim that a nonexact colimit preserves it. The proof applies the assumed acyclic-resolution comparison, never ordinary colimit to that quasi-isomorphism.

The reindexing consequence concerns the maps of these exact sequences obtained from augmentation-compatible bar maps and their derived comparisons. It does not need or assert that ordinary u_! preserves every short exact sequence. Step 8 defines the colimit map by its cocone and checks it is a morphism of the exact K sequences. The separate sibling `lem-trf-bar-resolution-derived-reindexing` identifies the normalized derived adjunct for a reindexing chain map; this delivery does not import that larger assertion or create a circular dependence on it. The scalar clause applies exact restriction to the complexes and comparison maps in the statement; it does not claim that restriction preserves projectives or requires a flat ring map.

## Searches and reuse

Read the existing DAG statements for all cited nodes before writing the proof. Searches of the DAG by bar resolutions, cone connecting maps, derived colimit, exact direct sums, enough projectives, canonical comparisons, and Tags 08PG/08PH, 0152, 05SA/05SC/05SU located all required general inputs. `tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality`; blueprint searches for bar/cone and derived/shift found no equivalent imported blueprint statement; tag searches 08PG and 0152 found zero blueprint matches. The inherited precise ancestry and `same_as: []` are retained. Read the chapter and unit records, and the main-20261015 local-term ancestor. This remains a generic derived-colimit tool in the already recorded cotangent/transitivity branch, without changing the curve unit or chapter route.

Ran the mandated `msearch.py` searches for the item with LeanFinder, Loogle, grep and LeanSearch, plus a second conceptual phrasing for the derived counit/shift input. Queries and results are copied from the actual `searches.jsonl`; the rejected unqualified Loogle identifier is recorded as rejected, not evidence of absence. Retained the item's earlier recorded searches. Read Mathlib `Algebra/Homology/DerivedCategory/ShortExact.lean` (triangleOfSESδ, lines 38 onward; its naturality and cone isomorphism), `SingleTriangle.lean`, and `HomotopyCategory/ShortExact.lean` for the returned cone-quasi-isomorphism results. These supply the general SES roof, not the whole bar-resolution/derived-comparison assertion. The returned total-left-derived counit only supplies a natural transformation; it is not the whole boundary compatibility statement. No new node is needed: the precise pointwise Kan bridge and coherent-shift theorem already exist.

## Tool uses

The off-unit tools are declared individually in `split_report.tool_uses`: the long exact sequence on complex cohomology, the denominator-to-pointwise-Kan bridge, everywhere-defined assembly, and the coherent-shift theorem. Each is used as a general categorical input; none replaces a step of the geometric unit's route. The left-adjoint colimit theorem and derived-category definition are Mathlib/definition tools. Existing same-unit nodes give exact representable sums, enough projectives and bounded-above acyclic computation.

## Review by Q12

I reviewed the statement against Stacks 08PG and 08PH, rather than assuming the seeded dependencies are sufficient. Stacks explicitly says the chain construction is exact and gives the reindexing generator map; the extra signed cone explanation comes from the construction immediately before 0152. There are no new nodes whose statements require a separate source review.

For step 1 I opened `lem-trf-representable-sum-shriek-acyclic`: its statement explicitly gives exact L_U and exact small sums, so it applies to arbitrary coefficient modules and a small E. No freeness of F(U) is needed. For step 2 I read `def-weil-abstract-derived-category` for the differential matrix, and `lem-weil-pbc-complex-ses-homology-long-exact` for the implication from zero kernel cohomology to an isomorphism on cohomology. The kernel short exact sequence is degreewise surjective since p is, and the displayed calculation proves its acyclicity.

Step 3 uses only the cone convention in that definition and the quasi-isomorphism just proved. I checked both squares of the diagonal cone map before inverting q, so its naturality uses statements and direct computation, not an unspecified theorem from a cited node's proof.

For step 4 I read the colimit universal property, the left-adjoint colimit-preservation statement, and the representable-sum statement. They give right exactness, enough projectives, and the coefficient colimit identification used here. I read the bounded-above acyclic computation statement in full: its hypotheses really do include enough projectives, additive right exact V and everywhere-defined LV. All hold here, while boundedness and termwise acyclicity are explicit for B. Its conclusion is precisely epsilon_B invertible and the stated formula, not merely existence of an unrelated isomorphism.

For step 5 I read the full statements of the pointwise Kan bridge, everywhere-defined assembly, additive homotopy triangulation, and right-Kan coherent shifts. The bridge explicitly identifies the projection at the identity denominator with the canonical epsilon. The last tool explicitly says that the counit commutes with shifts. Thus the epsilon shift equation in this step is supported by their actual conclusions. It is not inferred merely from exactness of LV.

In step 6 the only new calculation is the two naturality equations at q and at minus projection. The source q and target Vq are separately quasi-isomorphisms, by step 2 for the two already exact sequences. V need not preserve the arbitrary source kernel. Additivity identifies V of the cone, so these equations yield the signed roof identity as written. In step 7 I checked the types of delta_0 Qa'', Qa'[1] delta_B, and the placement of sigma in the final formula; the augmentation is a map of all three terms by step 1. Cancelling LV(Qa'') is justified by the hypothesis that a'' is a quasi-isomorphism, and cancelling m'' by step 4.

For step 8 I checked that a map to a precomposed bar sequence defines a target colimit cocone on E and hence the asserted map. The three such maps commute with the two short-exact-sequence arrows. Their source and target K sequences are exact independently; exactness of u_! on arbitrary presheaves is unnecessary. The reindexing acyclicity assumptions justify using the displayed bar-derived comparisons. For step 9 all kernel, cone and scalar-action formulas are unchanged on underlying groups. Thus restriction preserves the actual roofs and equations, not just existence of a triangle.

I tested E empty (all complexes are zero), E terminal (the unnormalized bar has alternating identity differentials and augmentation to F), the zero module, the two split exact sequences with one zero end, and a nonsplit module extension concentrated in degree zero. The contraction works in the last case without choosing a splitting; the negative projection is the sign required by the recorded cone convention. All sums are indexed by small sets in the fixed universe. No new statements were made, and no step exceeds 2000 characters or hides a comparison lemma: the nontrivial comparison inputs are the existing cited statements. This checks delivery-errors B through E, including the no-duplicate/no-restatement requirements (zero new nodes) and the statement-level citation requirement.

## Unfinished work

None in the stage-1 split. The downstream unsplit inputs remain their existing DAG nodes. No Lean was written, no compiler/build was run, and only the assigned sandbox was written.
