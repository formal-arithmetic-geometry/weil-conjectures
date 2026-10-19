# Worker report: lem-trf-elementary-module-devissage

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-elementary-module-devissage.json`: statement, split into seven steps following Stacks 057S; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-type-sheaf-fp-support.json`: new statement-only node, Stacks 057Q; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-finite-smooth-local-structure.json`: new statement-only node, Stacks 057K and its affine refinement 057L; no Mathlib match.
- `citations.json`: one verbatim statement quote for every cited node in each numbered proof step.

## Attachments

None for this item or the new nodes. Searches of the read-only slopmaster2 `WeilConjectures/` by the item tag, devissage/dévissage, elementary module, Stacks tags, and the geometric/support notions did not find the full assertions. The existing affine etale closed-immersion lifting node already has its own closed attachment; it is reused without modification. No source or DAG files in the shared repository were written, and no compiler, Lake, build or git command was run there.

## WANTED

None. All mathematical sources needed are in the local Stacks checkout.

## Findings and corrections

The inherited statement is retained verbatim. In particular its explicit hypothesis that x belongs to the fibre support makes dimension at x well-defined: without it, F=0 on a nonempty X leaves x outside the empty support, so the stated dimension at x is not a dimension at a point of that space and the supporting construction cannot choose z. Stacks 057S as printed does not explicitly state this hypothesis, but this item's creator already supplied it. I did not reopen or change it. The new supporting-subscheme lemma itself permits F=0, since its conclusion does not demand a point in Z.

The imported item had no proof. Its statement dependencies included flatness over a base, which is not assumed or used, and a redundant module finite-presentation definition, while omitting the actual module pullback, morphism finite-presentation, residue-field and affine-spectrum definitions. I removed the two unused dependencies and added those definitions, together with integral schemes for the geometrically integral clause.

The main construction follows the three paragraphs of 057S. I made two implicit checks explicit: one must lift over X times_S S_1, rather than lift over X alone; and the new sheaf identification follows from affine pushforward base change, with the cartesian square and its directions specified. The affine finite-presentation criterion is cited before using a finite coordinate presentation. No full module-devissage assertion is moved into a child node.

The item's recorded unit and blueprint ancestry were retained. The item is a descendant of the flattening input of lem-trf-local-term-locality, through the existing alteration/flattening chain. This work expands the 057S input to that flattening argument, and changes no chapter, unit, or unit realization fields. The current unit and chapter records, the main-20261015 convention, and the inherited blueprint ancestry were read. This item has no blueprint_update field.

## Not duplicates

Searches of the whole DAG for 057Q, 057K, 057L and their labels found no existing statement. Whole-blueprint searches for devissage, local structure, finite over, purely transcendental, sheaf lives, support, and the three tags found no imported blueprint statement of either new assertion. The following nearby statements were opened and checked:

- lem-trf-finite-type-sheaf-fp-support vs lem-weil-pbc-support-pullback-finite-type: the existing node proves closed support and its inverse-image behavior, but does not give a finitely presented closed subscheme carrying the module with prescribed fibre support.
- lem-trf-etale-finite-smooth-local-structure vs lem-weil-pbc-affine-etale-closed-immersion-lift: the existing node lifts an affine etale morphism across a closed immersion; it does not construct a finite-over-smooth factorization, geometrically integral fibres or the purely transcendental residue field.
- lem-trf-etale-finite-smooth-local-structure vs lem-trf-elementary-module-devissage: the new input is the scheme-level geometric local structure theorem with dimension of the whole fibre. The item concerns the dimension of the module's support, and must construct a supporting subscheme and extend its etale neighbourhood to the ambient scheme. Steps 2, 4, 5, 6 and 7 perform that additional argument.

The old affine etale lifting result was reused rather than duplicated as a 057R node. General etale composition/cancellation, etale base change, affine fibre products, residue fields of closed immersions and the module pullback/base-change statements are also reused.

## Mathlib searches

Every new node has LeanFinder in two different phrasings, LeanSearch, Loogle and a source grep, all run through the required msearch.py command. The item was also searched again. The exact query texts and returned declaration names are in the node records, with full returned responses under search-results/ and actual command log entries in searches.jsonl. Every service responded successfully. No unavailable service is treated as a negative result.

For the support node, Module.support_eq_zeroLocus and Module.mem_support_iff_of_finite were genuine nearby hits: they describe support via the annihilator of a finite module, not the existence of a finitely presented supporting subscheme on a prescribed fibre. I read Mathlib/RingTheory/Support.lean. The sheaf-presentation search hits describe finite presentation of a sheaf, which is not assumed here. For the geometric node and the item, the strongest relevant hits were Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial and the scheme Smooth chart results. Reading RingTheory/RingHom/StandardSmooth.lean and AlgebraicGeometry/Morphisms/Smooth.lean confirms that they assume smoothness and give etale polynomial coordinates; they do not turn an arbitrary locally finite type scheme into a finite scheme over a smooth family. None is an exact or one-line match. The grep hits in Geometrically/Integral.lean define a property, without the needed existence theorem. There are zero new Mathlib leaves.

## Review by Q36

I read flat.tex, lemma-elementary-devissage (057S), its entire proof and the immediately preceding lemma-sheaf-lives-on-subscheme (057Q) and proof. I read more-morphisms.tex, lemma-local-local-structure-finite-type (057K), clauses (1)--(6), its proof, and lemma-local-local-structure-finite-type-affine (057L), clause (7) and proof. The new geometric statement is precisely those six properties with affine choices, omitting the unneeded additional finite-presentation conclusion. The new support statement is the assertion of 057Q, with equality of supports expressly topological. It does not claim reducedness or equality of annihilator ideals after base change. I also read flat.tex lemma-lift-etale (057R), morphisms.tex etale composition and base-change lemmas, and coherent.tex lemma-affine-base-change (02KG). No SGA route is used.

For step 1, I opened the locally-finite-type and dimension definition statements and the etale composition/cancellation and open-immersion pullback statements. They supply exactly the etaleness of open restrictions and their composition and the module restriction/pullback identification. Cofinality of open neighbourhoods proves invariance of dimension at x under this restriction. An affine chart supplied by the local finite type definition suffices, without invoking a global noetherian hypothesis.

For step 2, I read the new 057Q statement against the source. It supplies the supporting closed immersion, finite presentation, the finite-type quasi-coherent module and equality of fibre supports. The closed-immersion definition supplies affineness and quotient coordinate rings. Images of algebra generators prove finite type of Z over the affine base directly. The required point z exists because the original x is in the support. The dimension is n because it is the same topological subspace, not because the scheme is reduced.

For step 3, I read the new geometric statement and checked all its hypotheses: Z to S is locally of finite type by step 2, and the point z and equality of fibre dimension are already established. It gives the singleton fibre, elementary residue fields, geometrically integral smooth family and pure-transcendence requirement without any module assertion. This is strictly an input to the ambient lifting argument, not a restatement of the module result.

For step 4, I opened the affine fibre-product statement, finite-presentation definition and affine criterion, closed-immersion definition, and both etale permanence statements. The affine criterion actually supplies the finite presentation over the entire affine B, so I added that citation rather than treating that passage as a definition. Tensoring that presentation is the explicitly written elementary calculation that preserves finite presentation. The quotient formula proves closedness. Etale base change is applied to a:S_1 to S; cancellation is applied to W to D to Z with both the composite b and D to Z etale. No unsupported inference that an arbitrary map into a base change is etale is made.

For step 5, I opened lem-weil-pbc-affine-etale-closed-immersion-lift: its exact hypotheses are affine T and W, a closed immersion D to T, and an etale W to D, all proved before application. Its statement supplies a cartesian square, not merely an abstract extension. The fibre-product universal property gives W=Z times_X X' with the correct projections; the affine fibre-product and finite-presentation statements justify the displayed quotient/presentation after base change. The two-line presentation base-change calculation is a step, not a new node. In particular finite presentation here does not mean that X to S had finite presentation.

For step 6, I read the closed-immersion residue-field isomorphism statement: it applies to both j and i at the distinguished points. Together with the elementary b, their maps give the isomorphism on residue fields for g, with the direction and composite displayed. The separate etale base-change and composition statements prove etaleness of g. The base neighbourhood a is already elementary. I declared the generic residue-field node as an off-unit tool in split_report.tool_uses; it does not replace any trace-formula unit step.

For step 7, I opened both module-pullback preservation statements and the affine pushforward base-change statement. The first two give quasi-coherence and finite type of b^*H separately. The last applies because j is affine and H is quasi-coherent, for an arbitrary g; no flatness assumption on g or H is needed. Its exact base-change isomorphism has the orientation used to identify i_*G with g^*F. The smooth scheme Y, finite map pi and distinguished fibre were not shrunk in the lifting, so all geometric properties from step 3 remain available.

I checked B1--B10: the two new nodes have standalone statements, definitions for their notions, exact local Stacks labels/tags, no proof or proof-dependencies, searched blueprint ancestry and genuinely executed Mathlib searches. C1--C8 were checked by opening each cited statement; citations.json quotes the full exact statement of every citation. Every non-elementary input is a node, and the remaining quotient and universal-property calculations are written in the steps. No new dependency was selected from a proof instead of a statement. Existing dependencies have no path back to the new children in this construction; the server DAG check is the final cycle check. D1--D5: the argument itself stays in the item, with seven actual construction/verification steps; the new nodes have distinct hypotheses and do not merely repackage its clauses. No proof step exceeds 2000 characters.

For section E I tested zero-dimensional fibres (n=0, permitting r=0 in the rational function field), nonreduced supporting schemes, a non-noetherian affine base, and the zero module for 057Q. For example, over a field a finite module on Spec k[t] with support at (t) gives n=0 and a zero-dimensional Z, whereas a free nonzero module has the whole one-dimensional fibre support. This distinguishes the geometric input from the module assertion. For the zero module one may take Z empty; the main item excludes choosing x in an empty support. For a non-noetherian base the argument only asks for finite presentation of j, which 057Q supplies, never coherence or finite presentation of F. No additional separability of kappa(z)/kappa(s) is assumed. The affine lifting theorem allows an arbitrary defining ideal, not just a nilpotent one. These checks required no statement correction. This is the author's direct-delivery check; the maintainer's independent review remains separate.

## Unfinished work

No unfinished argument in the item. The two new input statements are intentionally unsplit and join the stage-1 queue. No Lean work was attempted.
