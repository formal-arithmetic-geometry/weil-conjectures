# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-model-fibre-ample-open.json: statement, split using existing nodes; Mathlib searches find no exact match or one-line specialization.
- citations.json: verbatim statements for all 17 step citations.
- searches.jsonl: actual msearch.py searches in this session; the item's earlier recorded searches are preserved.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, the id, fibre/fiber ampleness, and ample neighbourhood/limit declarations found no declaration asserting the item. Existing modules about ample sheaves or graph twists do not give the inverse-system statement. No Lean code was written or compiled.

## WANTED

None. All sources used are present in literature/.

## Findings and changes

The imported statement is correct and unchanged. Its proof was empty. The delicate point is that the inverse system of proper morphisms is not assumed Cartesian. Therefore the stage fibres cannot be identified with base changes of a fixed initial proper fibre; their transitions must be checked separately. The proof now gives that check on affine charts and uses the actual inverse system of fibres. The Noetherian neighbourhood theorem and affine-limit ampleness descent already exist as lem-trf-noetherian-fibre-ample-neighbourhood and lem-trf-ample-affine-limit-descent. No duplicate nodes are needed.

The chapter and unit records, the current ancestor blueprint update, and SETUP's three levels were read. This follows the subsidiary ampleness argument already identified by the item's blueprint.from, using precisely the middle paragraph of Stacks 0D2S; it changes neither the trace-formula unit nor its route. Generic scheme tools from other units are declared in split_report.tool_uses. Definitions and the separated-implies-quasi-separated Mathlib leaf are used as notions/tools. There is no statement dispute.

## Searches and reuse

Searched the whole DAG for ampleness, its inverse-limit and neighbourhood forms, residue-field colimits, and source labels/tags 09MT, 0D2N, 0CUG and 0D2S. Read the statements of every cited node. Blueprint searches for ample, fibre, inverse limit and the source tags found no blueprint version of the item. The existing general fibre-products-and-limits blueprint node is reused, not recreated. The ancestor command confirms lem-trf-local-term-locality.

The msearch queries include LeanFinder in two phrasings, LeanSearch, Loogle for IsAmple and source grep. An initial grep without word boundaries also matches the substring in 'example'; its hits are irrelevant and were not treated as mathematical matches. The second grep with word boundaries in AlgebraicGeometry has zero hits. Semantic hits concern affine-transition-limit sections, opens, properness and generic descent, not line-bundle ampleness. The item is not a Mathlib leaf. All new search records reproduce executed queries; no unavailable search was recorded as absence.

## Not duplicates

No new nodes. Existing 09MT, 0D2N, 0CUG and the fibre-products-and-limits node are cited directly.

## Review by Q87

I read more-morphisms.tex Tag 0D2S, lemma-ample-in-neighbourhood, especially the paragraph from the residue-field colimit through the Noetherian neighbourhood. It uses Limits lemma-limit-ample (09MT) and Cohomology of Schemes lemma-ample-in-neighbourhood (0D2N). I read those statements and proofs in limits.tex and coherent.tex, and Limits lemma-inverse-limit-irreducibles (0CUG) for the residue-field identification. The item's conclusion about absolute ampleness over an affine neighbourhood agrees with the existing 0D2N node: the source gives relative ampleness and the node explicitly chooses an affine neighbourhood. No new statement is proposed.

Step 1 uses lem-weil-pbc-limit-residue-field, whose statement explicitly gives the limit in schemes of the residue-field spectra and compatibility with maps to the base stages; a mere ring-colimit assertion would not by itself be the quoted scheme-cone assertion. The definitions def-pc-scheme-fibre and def-pc-fibre-product give exactly the stage fibres and their induced maps, with identity/composition following from uniqueness.

Step 2 uses lem-weil-pbc-proper-base-change to make each fibre proper. pqf-lem-proper-basic explicitly says that over an affine base the source is separated and quasi-compact. The base here is Spec of a field, so that clause applies. lem-pc-separated-quasi-separated then supplies quasi-separatedness. No Noetherian property of the limit base is assumed or used. I read the corresponding base-change-proper and affine-separated passages of morphisms.tex, and the separated-implies-quasi-separated node (a Mathlib leaf).

Step 3 uses pqf-def-affine-morphism exactly for inverse images of affine opens under the two assumed horizontal affine maps. The affine-spectrum fibre-product formula gives the two tensor-product rings, and pqf-lem-affine-local-target applies to the resulting affine cover of the target fibre. def-pc-fibre-product justifies the inverse-image identification by its two projections. I checked that U_alpha maps into V and its pullback into V_j; x_j lies in V_j since it maps to x_i. This avoids an unjustified assertion that the square is Cartesian or that a map into a subscheme factors merely from its pointwise image. The chart computation is a direct use of the cited formula and definitions, not an uncited descent lemma.

Step 4 uses lem-weil-pbc-limit-affine-transition for existence of the fibre-system limit. The statement of lem-kun-fibre-product-limits requires existence of all indicated limits: that one now exists, the original Y and X limits are assumed, and the residue-field-spectrum limit is Step 1. Its canonical isomorphism is exactly the identification with Y_x given by def-pc-scheme-fibre. I also read the current main-20261015 blueprint statement of this generic tool.

Step 5 uses clauses (1) and (2) of lem-weil-pbc-invertible-pullback-tensor: preservation of invertibility and composition of pullbacks. These identify the pullbacks of the initial fibre line bundle with the stage restrictions and limit restriction. The hypotheses of lem-trf-ample-affine-limit-descent are checked individually: small nonempty directed index with initial index 0, qcqs stages from Step 2, affine transitions from Step 3, the scheme limit from Step 4, invertible initial bundle, and ample pullback by the item's hypothesis. Its conclusion supplies exactly stage fibre ampleness, not yet neighbourhood ampleness.

Step 6 uses invertibility preservation again, then the exact statement of lem-trf-noetherian-fibre-ample-neighbourhood with f_i, M_i and x_i. This citation explicitly gives an affine open and absolute ampleness, so there is no unsupported conversion from relative to absolute ampleness. Properness and the Noetherian hypothesis are those of the item, and fibre ampleness is Step 5. Both conclusions hold at the same i.

I checked delivery-errors B through E against the written file: all notions in the unchanged statement retain their definition dependencies; all proof citations say what is taken; proof_deps is the union of uses; no step invokes a proof hidden inside another node; no new node restates a clause. No proof step exceeds 2000 characters. The non-Cartesian system case is explicitly allowed. Empty fibres cause no failure: the descent theorem permits empty schemes, and if the limit fibre is empty its vacuous ampleness can descend to an empty stage as covered by that theorem. A singleton index reduces to the Noetherian neighbourhood lemma; a nonempty limit point ensures the stated residue fields exist. No finite-presentation, flatness, injectivity of transitions, or Cartesian hypothesis has been inserted.

## Unfinished work

None in this stage-1 item. Its existing dependency nodes retain their own stages; they have not been edited.
