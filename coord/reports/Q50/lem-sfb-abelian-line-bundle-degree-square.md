# Stage-1 report: lem-sfb-abelian-line-bundle-degree-square

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-line-bundle-degree-square.json: item, split into four steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-euler-degree-square.json: statement-only prerequisite; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-euler-tensor-homogeneity.json: statement-only prerequisite; no Mathlib match.
- citations.json: verbatim statement quotes for all three step citations.
- searches.jsonl: retained actual msearch.py output records.

## Attachments

None. Searched WeilConjectures for the blueprint tag, isogeny, polarization, Euler characteristic and the degree identity. Existing isogeny-degree and Euler-characteristic declarations define the objects or prove other degree calculations, and none states the arbitrary-line-bundle formula. No Lean file was written or compiled.

## WANTED

None. The cited Milne PDF and Stacks source are present. Milne attributes Theorem 11.1 to Mumford, Abelian Varieties, p.150; this delivery follows the available Milne statement, leaving its two distinct coherent identities as unsplit prerequisites, rather than claiming their proofs have been supplied.

## Corrections and scope

The item was unsplit with no proof or repair note, and the sandbox had no earlier node or report. The imported mathematical statement is correct, including the zero-degree convention for a non-isogeny; no STATEMENT-DISPUTED correction is needed. Retained its definitions, source, existing search records, and blueprint provenance. The ancestor command returns blueprint.from.node = None; retained that actual ancestry instead of inventing a blueprint node. Read the current blueprint under literature/blueprint/latest: its direct-image step (3) is the surrounding route; this auxiliary abelian calculation does not alter that step or either higher blueprint level.

The split uses Euler characteristic as the intermediate invariant. The homogeneity prerequisite concerns tensor powers and contains neither the line-bundle homomorphism nor intersection numbers. The degree prerequisite concerns the homomorphism and Euler characteristic and contains no intersection numbers. Neither restates the item or a clause of its conclusion. The item itself supplies the multivariable coefficient argument and division by g!, followed by substitution. The new nodes have no proof, proof dependencies, or proof sketch in their statements. The deferred task is to split those two genuine geometric theorems; it is not an unfinished step of this item's assembly proof.

## Not duplicates

lem-sfb-abelian-euler-degree-square vs lem-sfb-abelian-line-bundle-degree-square: the former identifies degree with coherent Euler characteristic squared; the item identifies degree with normalized top intersection squared, and needs the separate homogeneity and coefficient calculation to connect them.

lem-sfb-abelian-euler-degree-square vs lem-sfb-abelian-polarization-calculus: the existing node constructs the dual and homomorphism and supplies polarization identities and the effective ample criterion; it makes no Euler-characteristic or numerical-degree-square assertion.

lem-sfb-abelian-euler-degree-square vs lem-sc-isogeny-degree: the existing theorem identifies isogeny degree with the rank of a finite flat pushforward, while the new theorem computes degree using coherent Euler characteristic and includes non-isogenies.

lem-sfb-abelian-euler-tensor-homogeneity vs lem-sc-hilbert-polynomial: the existing node gives polynomiality and a degree bound only for an ample invertible sheaf on a proper scheme; the new theorem says the entire polynomial on an abelian variety is c n^g and permits arbitrary invertible sheaves and negative powers.

lem-sfb-abelian-euler-tensor-homogeneity vs lem-sc-snapper-numerical-polynomial: Snapper supplies polynomiality and a degree bound for general coherent sheaves; it does not make the lower coefficients vanish or identify the remaining coefficient with chi(L).

lem-sfb-abelian-euler-tensor-homogeneity vs lem-sc-riemann-roch: the existing theorem is for curves, while the new theorem applies to abelian varieties in arbitrary positive dimension and describes tensor-power homogeneity.

Searched the whole DAG by Euler/Riemann-Roch/abelian keywords and source place, and blueprint_refs.py by abelian Riemann, Euler characteristic, Riemann, degree Euler, tensor powers, degree homomorphism, homogeneous Euler, and Euler characteristic square. The Euler definition and curve Riemann-Roch nodes were opened and distinguished above. No existing blueprint node states either prerequisite. The sources for the new geometric facts are Milne I 11.1(a),(b), not Stacks tags invented for abelian Riemann-Roch. The existing normalization is Stacks Tag 0BEP (definition-intersection-number), read at varieties.tex lines 10388–10412.

## Review by Q50

I read Milne, Abelian Varieties, Chapter I, printed p.54 (PDF p.60), Theorem 11.1, for the item and both new inputs. It begins with an arbitrary invertible sheaf: ampleness occurs only in the paragraph after the theorem. Part (a) is degree equals chi squared; part (b) is chi(O(D)) = D^g/g!. I also read printed p.46 (PDF p.52), the paragraph preceding 10.9 defining degree as zero for non-isogenies. The degree used here is kernel scheme length, not the number of geometric points. The homogeneity input is the tensor-power consequence of (b), applied to nD: all integer powers are defined explicitly, including zero and negative n. These are substantive results to be split later, not marked elementary.

Step 1 uses only the homogeneity node's actual formula, copied in citations.json. Its hypotheses are exactly the algebraically closed field, abelian A of positive dimension, and invertible N in the item. The tensor identity for powers of the same invertible object is definitional tensor arithmetic. Step 2 uses the coefficient definition in def-sc-intersection-number, whose full statement I read. For the identity closed immersion, Z=A is nonempty because it has the identity point; its dimension is g and it is proper by the abelian-variety definition. The g sheaves all equal N. I wrote the polynomial-identity argument over Q and counted the g! permutations producing the squarefree monomial, so no divisor/intersection comparison or ampleness theorem is hidden here. Division takes place in Q, not in k: it is valid even if char(k) divides g!. Step 3 uses precisely the degree-square identity of the new degree node, whose kernel-length convention and zero non-isogeny value were compared word for word with the item. Step 4 is just substitution in Q and has no additional citation. Every cited statement was opened and its used part copied verbatim. The two new nodes have all notion dependencies: the existing Euler definition, invertible sheaves and abelian varieties, and for degree the existing group/isogeny definitions and polarization construction.

I tested the hypotheses and both new statements on N=O_A, where g>0 and chi(O_A)=0, and phi_N is the zero map, not an isogeny. The homogeneity formula at n=0 says the same vanishing, rather than accidentally giving 1. On an elliptic curve with line bundle degree d, the identities give chi(N^n)=nd, d(phi_N)=d^2 and top intersection d, valid also for d=0 and negative d. On a product of elliptic curves, a line bundle pulled back from one factor has positive-dimensional kernel, zero top self-intersection and zero Euler characteristic. An ample bundle and its inverse have top intersections differing by (-1)^g, which disappears after squaring; the statements correctly do not require positivity of chi(N). A mixed external product with positive degree on one elliptic factor and negative degree on the other has negative Euler characteristic and an isogeny, so it checks why ampleness cannot be inserted. In characteristic p, the formula uses scheme length and therefore still includes inseparable kernels. Dimension zero is excluded consistently in the item and both prerequisites; no 0^0 convention is introduced.

I checked delivery-errors B–E: self-contained statement-only new nodes, actual recorded searches with alternative semantic phrasings, no duplicate or transplanted item clause, no undocumented non-elementary inference, no circular citations, no stronger hypotheses, and no SGA source. All four proof steps are below 2000 characters (total assembly about 1620 characters). The only geometric inputs are the two named nodes; the normalization is an explicitly written elementary calculation from the existing definition. Searches returned division-polynomial, root-pairing, linear-dual, abstract Euler-characteristic, tensor-algebra and analytic Riemann-integration declarations, which have different objects and conclusions. All new-node search records preserve the exact tools and query strings in searches.jsonl. No Mathlib leaf is asserted.

## Unfinished work

None for the stage-1 split of this item. The two new unsplit nodes are the stated lower-level work. Delivery validation and push results are produced by deliver.py.
