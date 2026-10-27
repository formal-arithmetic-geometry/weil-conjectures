# Worker report: lem-per-h1-koszul-last-product

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-h1-koszul-last-product.json`: statement split; no Mathlib match; five proof steps, using existing nodes only.
- `citations.json`: seven verbatim statement quotations for the seven step/node citations.
- `searches.jsonl`: the required search command's unchanged log, containing six searches from this session.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact blueprint tag and the Koszul/H1/product terminology, and read `RingTheory/KoszulRegularSequence.lean`. Its `IsH1Regular` and `IsH1RegularOn` are definitions, with no multiplication theorem. The existing sheaf-valued multiplication triangle is a different statement, not an attachment to this module-valued item.

## WANTED

None. The source used is present as `literature/stacks-project/more-algebra.tex`.

## What changed and why

The item was unsplit and the sandbox contained no previous node or report. The original statement is correct and has been preserved exactly: it is Tag 062G, `lemma-mult-koszul-regular`, clause (1), with coefficient module R. In particular, I did not introduce Noetherianity, locality, regularity of the prefix, nontriviality, or a proper-ideal condition.

Stacks deduces the result from the exact sequence arising from the multiplication cone (062C). Instead of creating another cone or exactness node, I expanded the needed degree-one cycle chase using the existing `lem-weil-pbc-koszul-tensor-cone-coordinates`. For a cycle (x,y) in the product complex, vanishing for g supplies x=du+gv and fy=-dv; vanishing for f supplies v=dw+fq and y=-dq. The explicit preimage of (x,y) under the product differential is (u+gw,q). This is an agent-written expansion guided by the Stacks proof, and `proof_origin.by` records that accurately.

Before settling on this proof, I searched the DAG for 062G/`lemma-mult-koszul-regular`, 062B, 062C/`lemma-koszul-mult`, and Koszul multiplication/last-generator terminology. I read the statements of the existing coordinate lemma and `lem-pc-koszul-coordinate-mul-triangle`. The latter is a triangle of sheaf complexes over Spec(R); importing it would require extra comparison results. The coordinate lemma already gives exactly the module formulas needed here. No new node is necessary for the elementary cycle chase.

The whole imported blueprint was searched with `tools/blueprint_refs.py search` for `koszul`, `062G`, `062C`, `H1-regular`, `H_1` and last-generator wording. No imported node states this multiplication result. I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`. The item's existing provenance is the algebraic regular-immersion criterion below this ancestor; this split changes no chapter or unit route. Its `blueprint` provenance has been retained, with `same_as: []`.

The coordinate lemma is a generic algebraic tool from another unit. It is declared in `split_report.tool_uses`, explaining why the item's unit has no replacement coordinate lemma. Definitions are used as notions.

## Mathlib searches

I retained the item's inherited searches and appended only the six searches actually executed with `msearch.py Q130 lem-per-h1-koszul-last-product`: two LeanFinder phrasings, one LeanSearch phrasing, Loogle `"Koszul"`, and two grep queries. The queries, results, dates and digests come from the generated log. All six services returned successfully.

The first LeanFinder results concern cotangent homology, differential identities, and exterior algebra. The second, phrased for scalar mapping cones and composites, returns mapping-cone component identities and a connecting-map comparison. These do not assert the multiplication result, nor identify arbitrary Koszul complexes with cones. LeanSearch returns ordinary regular-sequence constructors, which have stronger, successive nonzerodivisor hypotheses. The all-Mathlib grep finds a TODO at `Mathlib/RingTheory/Regular/RegularSequence.lean:21`, a future Koszul description in `Algebra/Homology/LocalCohomology.lean:45`, and an unrelated Koszul-connection docstring. I read the regular-sequence file's header to verify the TODO and its scope. No result makes the item a Mathlib leaf.

## Not duplicates

No new nodes were created. The existing module coordinate lemma is reused. The existing sheaf multiplication triangle was examined but is not needed; no new copy of either statement is proposed.

## Review by Q130

I checked the item against Tag 062G (`lemma-mult-koszul-regular`) in the local TeX, including its proof's use of 062C (`lemma-koszul-mult`). I also read 062B's statement and the adjoining-generator cone construction 0628/0629 with its matrix differential. This confirms the sign in the second coordinate is minus the prefix differential. There are no new statements to check against sources.

Step 1 cites the tensor product and chain-complex homology definitions. I read both complete statements: the former supplies the bilinear universal property and generation by pure tensors, and the latter supplies homology as kernel modulo image. The tensor unit identification is proved in the step: x tensor a maps to ax, with inverse x maps to x tensor 1; the bilinearity relation and differential linearity verify both inverse identities and the compatibility with cycles and boundaries. No general derived-tensor comparison or flatness theorem is used.

Step 2 cites the Koszul definition and the existing tensor-cone-coordinate lemma. The Koszul statement explicitly defines coefficient-module tensor complexes. The coordinate lemma's statement explicitly supplies all three degrees and both displayed differential formulas with the final scalar, for arbitrary M and prefix length r, including r=0. I checked that setting M=R and r=s requires exactly the ring and tuple hypotheses already present. Coordinates may be chosen separately for f, g and fg: only their common prefix complex and the stated formulas are used, so no unstated naturality or compatibility of the three choices is assumed. This is the sole non-elementary step, and it is marked accordingly.

Step 3 uses the degree-one homology definition, quoted verbatim in `citations.json`. Starting from dx+fg y=0, commutativity makes (x,fy) a g-cycle. Since its homology class is zero, it is the boundary of some (u,v); the two coordinate identities are written explicitly. Step 4 applies the other vanishing hypothesis to the now verified f-cycle (v,y), again using only the quoted kernel/image definition and the coordinate formulas established in step 2. Neither step assumes anything about prefix homology.

Step 5 substitutes the two boundary expressions. R-linearity gives d(gw)=g dw, so D_fg(u+gw,q)=(x,y). This proves that an arbitrary product-cycle is a boundary, and then uses the homology definition and step 1's explicitly established identification. There is no assertion of exactness left as an uncited black box. Steps 1, 3, 4 and 5 are elementary consequences of the cited definitions and already established formulas; none hides a separate lemma. Every step is shorter than 2000 characters, and the complete assembly proof is shorter than 3000 characters.

For edge cases, when s=0 the prefix has A_1=A_2=0, and the calculation reduces to injectivity of multiplication by the composite of two injective scalar maps. When R is the zero ring all modules and formulas are zero. Over R=Z/4 with prefix (1), the prefix need not generate a proper ideal and the same computation applies even for f=g=0: there is no illicit cancellation. For general prefixes, u,w are in A_2, v,q in A_1, and x,y in A_1,A_0 respectively, so each use of d has the correct source and target. No argument cancels f or g or infers prefix regularity.

Against delivery-errors B--E, I verified that no new restatement, elementary node, or duplicate was introduced; every cited statement was read, and each citation has a literal substring quotation; sources use verified tags and labels; the proof uses only facts supplied by these statements or the explicit calculation; and the statement and all maintainer-owned fields are preserved. The replacement of an implicit long-exact-sequence argument by the displayed boundary calculation is the substantive completion of this split.

## Unfinished work

None in this item's split. The existing coordinate lemma remains its reusable non-elementary dependency. Dry-run and delivery results are recorded by the delivery tool.
