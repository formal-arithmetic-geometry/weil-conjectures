## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-local-model-rhom-continuity.json`: item split into nine proof steps; statement unchanged; not a Mathlib leaf.
- `citations.json`: a verbatim statement excerpt for each of the seventeen step/node citations.
- `searches.jsonl`: five searches made through the required Q15 search command. The item's inherited Q51 searches are retained, and these actual Q15 searches are appended to its search record.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, local-model terminology, RHom/internal-Hom continuity and derivedHom/colimit declarations found no declaration stating both clauses for these pulled-back condensed coefficients. Existing finite-local-model descent files concern a different assertion. No Lean was written or compiled.

## WANTED

None. All mathematical sources used were available locally.

## What needed repair

The item had an empty proof. Its statement needs no correction: a finite constant local model over either allowed coefficient ring has a locally finite free resolution in degrees -1 and 0, including torsion integral models. The original bounded-target source 08JI is applicable after truncation, but the existing strict-perfect Hom node from 08JH gives a simpler computation for arbitrary target representatives. This avoids replacing an entire filtered diagram by unrelated choices of bounded representatives. The source metadata now names 08JH and 08JB as well as 08JI and Bhatt–Scholze Proposition 6.8.11(3).

The filtered internal-sheaf assertion is an agent extraction of the explicit finite Hom-complex calculation, not a quotation of Bhatt–Scholze's global direct-sum Lemma 6.8.12. I keep `proof_origin.by = agent`. No chapter or unit route was changed. The blueprint ancestor's coefficient-passage sentence is only the location served by this local base case; its forbidden older reference is not used as a source of the split.

## Searches and reuse

I searched the whole DAG by 08JI/08JB, RHom, finite free resolution and exact filtered colimits, then opened the statements of all chosen dependencies. Whole-blueprint searches `finite local model` and `08JI` returned none; broader searches `internal Hom` and `finite free` located contextual statements but none stating this local filtered-colimit comparison with the sharp lower bound. The existing resolution node is reused instead of creating a scalar-resolution node. The existing ringed-site strict-perfect Hom, slice restriction, module-object comparison and exact-colimit nodes are reused as generic tools.

The five Q15 queries in the log were read. Two distinct LeanFinder phrasings returned ordinary free-sheaf universal properties, sheaf cohomology and ordinary condensed closed structures. Loogle returned no hits. LeanSearch returned colimit existence/exactness infrastructure. Grep returned lattice/order preservation and unrelated colimit constructions. I read the relevant Mathlib sheaf colimit, homological-complex Grothendieck, sheaf Grothendieck and light-condensed monoidal sources, together with the free-sheaf declaration locations. None is an exact theorem about this derived internal Hom. The searches do not justify an attachment or a Mathlib-leaf status for the item.

## Not duplicates

No new nodes were created. The finite free resolution and strict-perfect Hom calculation are citations of the existing more general statements.

## Review by Q15

I read delivery-errors B–E, the chapter and unit records, the three blueprint levels in SETUP, the current blueprint ancestor proof and GOAL. For the mathematics I read Stacks `sites-cohomology.tex`, Tags 08JH, 08JI and 08JB, including the signed Hom-complex construction, and `sites-modules.tex`, Tags 03DA/03DB and the localized-site/extension-by-zero construction. I also read Bhatt–Scholze Proposition 6.8.11(3), printed p. 61, where finitely presented integral local models are treated through finite projective resolutions. There are no new-node sources to audit.

Step 1 uses the existing module-object/ringed-site equivalence: its statement explicitly leaves underlying sheaves unchanged and carries evaluation to evaluation. The Grothendieck module-category statement explicitly supplies exact filtered colimits on every small ringed site. The cohomology calculation is written out as preservation of the kernel/image and image/cokernel sequences, so arbitrary representative choices cause no missing derived-colimit assumption.

Step 2 uses only clause (1) of the weakly étale slice identification and the untwisted coefficient isomorphism. The cover members are objects of this site; no arbitrary base change theorem is invoked. The coefficient statement explicitly permits the untwisted case without assuming that ell is invertible on T.

Step 3 uses exact slice restriction, the sheafified sectionwise colimit description and the actual slice/sheafification comparison, including its statement about the sheafification unit. The last comparison is used on underlying abelian presheaves, which it explicitly covers; the module action is then the same action on sections. This corrects a possible hidden use of locality of sheafification. The derived internal-Hom restriction node states the required unrestricted slice isomorphism, rather than only a definition of restriction.

Step 4 applies the existing two-term local-model resolution on W. Its statement explicitly permits both A=O_E and A=E, finitely presented torsion P, arbitrary schemes and a=0. It supplies the exact scalar-extended sequence as well as the augmented quasi-isomorphism, so no flatness of L is silently assumed.

Step 5 uses precisely the strict-perfect node's arbitrary-target K-injective augmentation assertion, not its unrelated bidual clause. The finite-free internal-Hom node gives the finite-power identification; the Hom-complex definition gives the sign. I checked that a source term in degree -1 contributes C^(n-1), not C^(n+1), and that the second differential is d_C g - (-1)^n f u. The local free complex is bounded, so no infinite product interchange is present.

Step 6 writes out the finite-coproduct universal-property argument and verifies both differential terms. Step 7 identifies the map through the original cocone, using the displayed postcomposition formula and the evaluation-preserving module-object comparison. Thus the proof establishes the map in the item, rather than an unspecified isomorphism between its objects. These two steps are elementary consequences of the preceding cited models, not new lemmas.

Step 8 uses the standard t-structure statement's explicit equivalence with a representative vanishing below c. This choice is made for one target only; the diagram computation still uses the original complexes. The strict-perfect model therefore has no terms below c. I checked the integral test P=A/(uniformizer), with resolution [R -> R]: its Hom terms are C^n and C^(n-1), so Ext^1 appears above the bound and does not lower it. P=0, a=0, free P, negative c and the empty scheme also satisfy the calculation. There is no global uniform bound on local ranks or finite-cover assumption.

Step 9 uses the actual cover-local sheaf-isomorphism criterion on each cohomology sheaf and the derived cohomology-isomorphism criterion. Both are existing Mathlib leaves, and both statements were read. Exact slice restriction established earlier justifies passage to cohomology. Applying the same criterion to the map of a sheaf to zero proves global vanishing for the bound.

All seventeen citations have verbatim quotes in `citations.json`. The selected existing nodes have no dependency path back to the item. Every proof step is under 900 characters, so none hides a long inline comparison or a new unsplit lemma. Non-elementary off-unit statements are declared as tool uses with their exact purposes; none substitutes a different finiteness route. The item preserves its creation, blueprint ancestor and prior search data. Nothing was written to the read repository or launcher.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own stage status.

## Validation

Required server dry run and delivery pending below.
