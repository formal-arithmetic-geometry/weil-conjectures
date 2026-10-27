# NZ worker report: lem-sfb-geometric-tangent-unramified

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-tangent-unramified.json`: statement; split into six proof steps, using existing nodes only. The item is not a Mathlib leaf.
- `citations.json`: 16 entries, one for every citation of every proof step, copied verbatim from the cited statements.
- `searches.jsonl`: the search command's actual records for the five NZ searches; the item's inherited NP searches and results are preserved as well.
- `report.md`: this report. No new DAG nodes, no new Mathlib leaves, and no Lean files.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag and for tangent/unramified and geometric-tangent terminology found no declaration stating this item. The rational-point cotangent criterion exists separately and is used through its existing DAG node; it does not state this geometric-point criterion.

## WANTED

None. All sources used are present in the read-only literature tree.

## Statement clarification and source scope

STATEMENT-DISPUTED: the equivalent clause's unqualified word “morphism” is false if interpreted as any morphism of schemes rather than a morphism over the geometric field. For an explicit counterexample take $S=X=\operatorname{Spec}\Omega$, $f=\mathrm{id}$, and $\Omega=\overline{\mathbb Q(t)}$. The derivation $d/dt$ of $\mathbb Q(t)$ extends to its algebraic closure in characteristic zero. The ring map $a\mapsto a+D(a)\epsilon$ from $\Omega$ to $\Omega[\epsilon]/(\epsilon^2)$ reduces to the identity and is nonconstant; it is not an $\Omega$-algebra map. The identity morphism is nevertheless unramified and its relative tangent space is zero. I clarified the clause to read “morphism of $\Omega$-schemes”, exactly the relative condition in Stacks Tag 0B2C and the cited tangent-space definition. The main tangent-vanishing assertion and its hypotheses are unchanged.

The statement quantifies over every algebraically closed geometric point, including fields larger than the algebraic closure of a base residue field. `def-weil-geometric-fibre` fixes the usual chosen-algebraic-closure case; I added `def-pc-fibre-product` as a statement dependency to support the explicit arbitrary-field pullback already written in the item. In the converse I use an algebraic closure of the SOURCE residue field, not just the base residue field. This avoids an unjustified assertion that all points of one geometric fibre are rational, or an extra closed-point-density lemma.

## Existing nodes and Mathlib searches

I searched the whole DAG by Tags 0B2G, 02GF, 02G5, 02G8 and tangent/unramified terminology, and ran `tools/blueprint_refs.py search` for `unramified`, `tangent` and `cotangent`. The imported blueprint contains no equivalent node. The needed rational duality, linear dual-map criterion, rational cotangent criterion, and arbitrary-base-change identity for the unramified locus already have nodes. I reused them rather than creating copies or a node restating either direction of the item.

All five NZ Mathlib searches were run through the prescribed command and read: LeanFinder in two phrasings, Loogle with `"AlgebraicGeometry", "tangent"`, grep for the three tangent/unramified/cotangent patterns in AlgebraicGeometry, and LeanSearch for the geometric fibre tangent criterion. The semantic services return formally unramified schemes, formally unramified rings, and ring differential criteria, while the Loogle and grep searches return no hits. I read `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`, including the diagonal criterion and base-change instances. None states this geometric tangent criterion or specializes to it in one line. The existing linear dual criterion is already a Mathlib leaf (`LinearMap.dualMap_injective_iff`, `Mathlib/LinearAlgebra/Dual/Lemmas.lean:930`), so no new leaf is needed.

## Not duplicates

No new nodes were created. The rational-point cotangent criterion has a fixed field and closed rational points; the present item detects a morphism over an arbitrary base by all geometric field points. The unramified-locus node concerns the locus and its pullback, with no tangent-space conclusion. Their combination is the proof, rather than a duplicate of any one of them.

## Blueprint route and generic tools

I read the chapter and unit records and the current `main-20261015` direct-image proof. This item is the rigidity input beneath `lem-sfb-stable-pointed-isom-finite`, in the inherited alteration/plurinodal branch of the direct-image finiteness argument. It keeps that route, with no SGA input. The ancestor command prints `None` on this inherited created-node chain; I retained its supplied `blueprint.from.node = null`, the precise nonempty `from.place`, and the full `via` chain rather than inventing an ancestor.

The split declares three generic off-unit tools in `split_report.tool_uses`: rational tangent/cotangent duality, the closed-rational cotangent criterion, and the unramified-locus base-change identity. These are geometry tools used at their stated scope, not replacements for the six-functor unit's route. The Mathlib linear dual lemma and locally-finite-type base-change lemma need no route exception. No maintainer-owned top-level tool-use or review field is set.

## Review by NZ

I read the item's Stacks sources in `varieties.tex`: Tags 0B2C (relative tangent vectors), 0B2E (rational tangent/cotangent identification), 0B2F (map duality), and 0B2G (injective tangent criterion). In `morphisms.tex` I read Tags 02G4, 02G5, 02GF, 02G8, 01T4 and 0475, including the proof of the base-change equality of loci. The proof follows the rational specialization of 0B2G and the pointwise geometric test supplied by 0475; no unrecorded global descent or closed-point-density theorem is used. I also read Schemes Tag 01J9 for the point/residue-field description. There are no new nodes whose sources need independent validation.

For Step 1, `def-weil-geometric-point` says a field-valued point is a point together with a homomorphism from its residue field, and `def-pc-scheme` supplies affine neighbourhoods. I wrote out the split field-map argument giving residue field $k$, and the maximal-ideal argument showing that such a rational point is closed even without separatedness. This is an elementary argument, not an implicit Nullstellensatz use.

For Step 2, I opened the statements of `lem-sc-rational-tangent-cotangent-duality`, `lem-sc-dual-map-injective-iff-surjective` and `lem-sc-rational-unramified-cotangent-criterion`. They give precisely duality of the two maps, injective dual iff surjective original, and unramified at a closed rational point iff cotangent surjective, respectively. Both source and target points are closed and have residue field $k$ by Step 1; the morphism is locally finite type by the step's explicit assumption. The target cotangent is zero because its local ring is the field $k$. No finite-dimensionality, flatness, or finite-presentation hypothesis is added.

For Step 3, `lem-weil-pbc-lft-base-change` applies to the arbitrary map $\operatorname{Spec}\Omega\to S$. The statement of `lem-trf-unramified-locus-base-change` explicitly says $W_p=g^{-1}(W_f)$ without a flatness assumption and defines membership by unramified source neighbourhoods. Thus $W_f=X$ makes every rational point of the pullback unramified, and Step 2 supplies its zero tangent space.

For Step 4, the statement of `def-weil-algebraic-closure` includes existence for every field. The point/residue-field clause of `def-weil-geometric-point` constructs $a$ over the chosen arbitrary $z$. I checked that `def-pc-fibre-product` actually states the universal property with the two projection identities; applying it to $(a,\mathrm{id})$ gives an $\Omega$-point over $z$. This is elementary from those statements and it uses the exact all-geometric-points quantifier of the item.

For Step 5, the locally-finite-type base-change statement again supplies Step 2's only finiteness hypothesis. The same locus statement now REFLECTS membership from the constructed point to $z$; I do not use a one-way base-change lemma as if it reflected unramifiedness. Finally `def-weil-unramified-morphism` expressly recalls the affine-cover definition equivalent to its open-diagonal definition. Having an unramified source neighbourhood at every point supplies exactly that cover, so the global conclusion needs no additional finiteness assumption.

For Step 6, the cited tangent-space definition gives morphisms over the field and describes scalar multiplication by $\epsilon\mapsto\lambda\epsilon$; at $\lambda=0$ this is exactly the constant tangent vector. The dual-number definition gives the ring used in the statement. The equivalence of zero vector space and a singleton set of tangent vectors is elementary. The empty source/fibre cases are also checked directly, rather than treated as a nonempty point argument.

I checked the delivery-errors B–E requirements against the actual files: every object is introduced; the relative morphism ambiguity is repaired explicitly; every non-elementary input is a cited existing statement, with a verbatim quote; the proof does not use the internals of a cited proof. The six proof steps have lengths 613, 779, 664, 697, 773 and 678 characters, so no long step hides a comparison lemma. There are no new-node duplication, statement-only, source-tag or search-log issues. Small cases include empty $X$, empty fibres, identity maps, closed immersions over a nonreduced base, affine space over a field (nonzero tangent), and the dual-number thickening of a point (nonzero tangent). In particular, a nonflat closed immersion is unramified and all its geometric fibres are empty or reduced points, consistent with the statement's lack of flatness.

## Validation and unfinished work

No mathematical subtask remains. The required server validation and direct delivery are run after this report; their results are recorded below.
