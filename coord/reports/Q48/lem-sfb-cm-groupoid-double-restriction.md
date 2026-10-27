# Q48 stage-1 delivery: lem-sfb-cm-groupoid-double-restriction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cm-groupoid-double-restriction.json: statement, split into six steps; no Mathlib match for the whole item.
- citations.json: one verbatim statement excerpt for every dependency of every proof step.
- searches.jsonl: genuine msearch.py results, retained with the item searches.

There are **0 new nodes and 0 new Mathlib leaves**. The sandbox initially had no item or report, so the item was copied from the live repository. No repository file, launcher file or Lean file was changed, and no compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, double-restriction names, groupoid restriction, and Cohen--Macaulay/groupoid combinations. The source contains other uses of double restrictions and fibre Cohen--Macaulay loci, but no declaration giving this theorem. In particular RestrictedFibreCohenMacaulayLocus.lean concerns an open CM locus, not successive saturation maps. No sorry declaration was treated as a completed attachment.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Corrections and findings

The item statement is correct and unchanged. The source 04MW has typographical slips in the descriptions of h' (the fibre product there must involve R', with target t'); the item's explicit R_B formula already repairs these. Its last inverse display is missing a parenthesis, and the verification is left to the reader. Step 1 gives the correctly typed formulas in both directions and checks the two compositions using associativity and inverse/unit identities. These are transcription/detail omissions, not a change to the source theorem.

The important hypothesis check is that h_B need not be surjective onto U. Step 2 replaces U by the open image V of h_B; h_C factors through V by the explicit map (z,r) ↦ (j(z),r) to W. The singleton map W → V is surjective, flat and locally finitely presented, hence an fppf (and fpqc) cover.

No new CM descent node is needed: existing nodes for fpqc flatness and lfp descent, combined with the **first paragraph only** of lem-pur-cohen-macaulay-field-extension, prove the needed descent directly on fibres. The relative second paragraph of that node assumes Noetherian base schemes and was not used. No base in the present item is assumed Noetherian. The source's 045T base-change theorem has a locally finite-type hypothesis on the changing base and would not suffice for W → B; the arbitrary-field-extension statement of 00RJ is what justifies step 3 here.

The existing blueprint.from.node is null and remains null: blueprint_refs.py ancestor returns None for this entire seed-target chain. Its exact inherited place and via list are retained. The current latest blueprint unit and direct-image proof were read; the current text presents compactification/direct-image stability and contains no separate groupoid double-restriction node. The inherited supporting route is the 04MZ final assembly step under the existing bootstrap/slice chain. No chapter or unit file is changed.

## Searches and existing-node checks

Searched the whole DAG for 04MW, 04MX, 045V, Cohen--Macaulay base change/composition/fppf locality, and flat/lfp openness and descent. Ran blueprint_refs.py searches for “double restrict”, “045V”, “Cohen”, and “Cohen-Macaulay”; none gives a duplicate blueprint statement. The existing maximal-slice node cites this item and is not a possible dependency. Existing groupoid locus/slicing nodes give other conclusions, not this theorem.

Read the actual statements of all 17 proof dependencies. Used existing lem-weil-pbc-flat-lfp-open; lem-trf-fppf-covering-is-fpqc; lem-weil-pbc-flat-morphism-base-change; clause (3) of lem-weil-pbc-qcqs-morphism-permanence; lem-weil-pbc-fpqc-descend-flat; lem-weil-pbc-fpqc-descend-locally-finite-presentation; lem-weil-pbc-surjective-base-change; and the field-scheme paragraph of lem-pur-cohen-macaulay-field-extension. These are genuine generic tools, not duplicated new nodes. The three non-Mathlib off-unit tools are declared in split_report.tool_uses with their roles. The CM field-extension tool is commutative algebra; this use does not invoke purity or an SGA route.

The new item searches were run through msearch.py: both semantic services, Loogle, and Mathlib grep. A second semantic formulation used depth versus dimension and faithfully flat base change; another used the full successive-saturation statement. Read every returned hit: FlatDescent offers abstract DescendsAlong machinery; FinitePresentation and Flat offer individual stability instances; UniversallyOpen.of_flat gives the openness already represented by an existing leaf. None asserts the groupoid/CM conclusion. Loogle CohenMacaulay and the Cohen--Macaulay grep of AlgebraicGeometry have no hits. Exact query strings and real result records are in searches.jsonl and mathlib_searches. No unavailable response was called a no-match result.

## Not duplicates

No new nodes. The reused field-extension statement differs from the item: it concerns local rings on a locally finite-type scheme over a field after an arbitrary field extension; it has no groupoid, restriction, saturation, or flatness assertion about scheme morphisms.

## Review by Q48

I read Stacks more-groupoids.tex, lemma-double-restrict (04MW) and lemma-double-restrict-property (04MX), including the pointwise formulas and the open-image qualification; more-morphisms.tex lemma-CM-local-source-and-target (045V) and lemma-base-change-CM (045T); algebra.tex lemma-extend-field-CM-locus (00RJ); descent.tex lemma-descending-property-flat (02L2) and lemma-descending-property-locally-finite-presentation (02KY); topologies.tex lemma-zariski-etale-smooth-syntomic-fppf-fpqc (022C); and morphisms.tex lemma-fppf-open (01UA) and lemma-base-change-surjective (01S1). No new statement was introduced whose source needs a separate check.

Step 1 cites the groupoid definition, whose statement explicitly provides the source/target, inverse, unit and associativity laws used, and the fibre-product definition, whose universal property supplies both scheme morphisms. The composite a = r_1 r_0^{-1} goes from g(b) to gj(z), in the right order for R_B; its inverse formula is r_1 = a r_0. This is an elementary calculation, fully written out, not an invocation of 04MW as an uncited result. The formulas are built out of scheme morphisms and universal maps, so no separate appeal to an unproved Yoneda theorem is hidden here.

Step 2 uses the flatness definition to extract flatness from the given CM hypothesis; flat-lfp-open gives precisely openness; the affine-open finite-presentation node gives the required presentation even after replacing the target by its open V. The lfp definition and fppf-site definition then identify the singleton covering, and fppf-covering-is-fpqc supplies exactly the covering condition required in step 4. The fibre-product definition gives the explicit Z → W map. Flatness and lfp survive this target corestriction by the indicated identical local rings and affine neighbourhoods; no compositional CM assertion is assumed.

Step 3 uses flat base change and exactly clause (3) of qcqs-morphism-permanence, which includes lfp base change and does not require qcqs hypotheses for that clause. The scheme-fibre and fibre-product definitions identify the fibre as D_b after extending its residue field. The affine-spectrum fibre-product leaf gives the tensor description of the finite-presentation charts, and the lfp/finite-type definitions show those fibres are locally finite type over their fields. The first paragraph of CM-field-extension says both directions for arbitrary field extensions and gives Noetherianity as part of the CM local-ring conclusion. Thus its hypotheses hold without any Noetherian assumption on U, B or W. This step does not cite the relative clause of that node or the insufficient lft-base-change version 045T.

Step 4 uses the fibre-product definition to replace W ×_U Z by W ×_V Z. The statements of the two descent nodes explicitly allow an fpqc covering family of an arbitrary scheme and give respectively flatness and lfp of the original morphism from its base changes. The singleton of step 2 meets that condition even though W need not be quasi-compact over V.

Step 5 uses surjective-base-change to lift each x to e; it does not assume that a fibre product of nonempty sets is automatically a nonempty fibre product of schemes. Fibre definitions and fibre-product universality give the field-extension description at w. The affine chart argument is the same explicit tensor presentation already proved in step 3, now justified by step 4's lfp conclusion. Again only the first paragraph of the CM-field-extension statement is used, this time in its reverse direction, to descend the property at the particular point x. Flatness was established separately in step 4. All properties needed for Cohen--Macaulayness are therefore accounted for.

Step 6 uses only the definitions of flatness, fibre and lfp: passing from V to the open ambient U leaves target local rings, residue fields, fibre local rings and the selected affine chart ring maps unchanged. This is an elementary final check, with no uncited claim that composition preserves Cohen--Macaulayness.

I checked B--E of delivery-errors.md against the files: there are no new nodes to conceal a clause of the item; every non-elementary result is an existing cited statement, and citations.json copies the portions actually used. The item proof contains the comparison and descent argument rather than relocating it. There is no backwards dependency on maximal-slice, no new dependency cycle, no proof text in a statement, no definition cited as a substitute for a theorem, and no source tag used in place of a DAG dependency. All six steps are under 2000 characters (the longest is 1096); neither elementary step hides a separate geometric lemma.

For small cases I tested the identity groupoid, where the maps reduce to g, j and gj, and the comparison is the ordinary base-change diagram. For an open B contained properly in U and the identity groupoid, V = B confirms why surjectivity onto U would be wrong. For the pair groupoid the formulas become the expected cancellation of the intermediate B-coordinate, with no change of source and target order. If B is empty or C is empty, Z is empty and the assertion is vacuous. For arbitrary non-finitely-generated residue-field extensions, 00RJ still applies. A singular/non-Noetherian ambient base does not enter that theorem: only the finite-type schemes over residue fields are used. These checks required no statement correction.

## Unfinished work

None in the one-level stage-1 split. The item is ready for server dry-run checks and direct delivery; the maintainer independently reviews the mathematics.
