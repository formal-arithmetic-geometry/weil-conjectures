# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-algebraic-dualizing-ext-bounds.json`: statement, split into nine proof steps; not a Mathlib leaf.
- `citations.json`: 27 verbatim statement quotations for the nine steps.
- `report.md`: this report. No new nodes, no Mathlib leaves, no unit-record changes.

## Attachments

None. Searches for the exact blueprint id, normalized dualizing complexes, and the corresponding algebraic Ext bounds in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration of this item. The upstream master reference likewise supplied no finished attachment.

## Wanted sources

None. All sources needed are present locally.

## Corrections and route

The imported statement is retained verbatim, including its nonzero ring, finite support dimension, and zero-module convention. Its source is Stacks `dualizing.tex`, Tag 0A7U, `lemma-sitting-in-degrees`, clauses (1) and (2). The source also has a depth characterization; that third clause is outside this item's statement and is not imported as a hidden induction hypothesis. The proof instead establishes just the two stated bounds simultaneously. In the regular-element case it derives vanishing in degree zero as well, directly from Nakayama.

The interrupted sandbox contained `write_split.py` and five genuine searches in `searches.jsonl`, but no node, report, citations, or completed delivery. I retained these searches and the draft argument and repaired unescaped primes in raw Python strings which prevented the draft script from parsing. I compared its item basis with the current shared node before writing. No delivery process was running when work resumed.

The existing blueprint ancestor is `lem-per-artin-gabber-affine-curve`, reached through the item's recorded `via` chain. I read the current main-20261015 ancestor proof and the chapter and unit records. This algebraic lemma supports the existing complete-local/normalization branch recorded in `blueprint.from.place`; it does not alter the perverse unit's route or its statement. Whole-DAG searches for Tag 0A7U and normalized algebraic dualizing complexes found this item and its users, not a duplicate proving both bounds. Whole-blueprint searches for `dualizing` and `normalized` found no equivalent algebraic Ext-bounds node.

## Mathlib searches retained

The five 2026-10-19 Q137 search records were read from `searches.jsonl` and copied into `mathlib_searches` with their exact tool and query text: two LeanFinder phrasings, Loogle `Module.supportDim, Ext`, LeanSearch, and grep `dualizing|supportDim.*Ext|Ext.*supportDim`. All services returned successful responses, so none is mislabeled unavailable. Their hits give support-dimension lemmas and abstract homological dimension; they do not give normalized algebraic dualizing-complex bounds. I read `Module.supportDim` in `KrullDimension/Module.lean:32`, the one-equation bound in `KrullDimension/Regular.lean:142`, and its regular-sequence dimension equality at line 197. These are supporting algebra lemmas, already represented by existing DAG nodes; they do not make this whole item a Mathlib leaf. The imported older search records are preserved rather than represented as new Q137 calls.

## Tool lemmas from other units

The `split_report.tool_uses` list declares the five general algebra tools: coherent RHom finiteness; finite-length simple filtration; support at the closed point implies finite length; removal of ideal-power torsion; and existence of a nonzerodivisor when the maximal ideal is not associated. Their statements are not supplied by this perverse unit. The Mathlib leaves and definition nodes are used with their ordinary algebraic meanings. No maintainer-owned `tool_uses` field is written.

## Not duplicates

No new nodes were created. Existing nodes are reused for all eighteen dependencies.

## Review by Q137

I read Stacks Tag 0A7U (`lemma-sitting-in-degrees`) and its proof in `dualizing.tex`, Tag 0A7Q (`lemma-dualizing-finite-length`), Tag 0G4H (`lemma-finite-ext-into-bounded-injective`), the dualizing definition in Tag 0A7B, Tag 0B52 (`algebra-lemma-one-equation-module`), and Tag 05EB (`more-algebra-lemma-divide-by-torsion`). There are no new-node sources to review. Every cited node's statement was opened, rather than relying on its title or proof. The quotations in citations.json are those actual statements.

1. The coherent-RHom node states finiteness of every cohomology module for coherent K and L when L has a bounded injective representative. The normalized-dualizing definition supplies that representative and coherence for omega; a finite module in degree zero supplies coherence for K. This proves the finiteness required by later Nakayama applications.
2. The bounded-below-injectives node applies because a bounded complex is bounded below; the RHom definition explicitly allows any K-injective representative. The Hom-complex definition and injectivity definition give the reversed degreewise short exact sequence. The cochain long-exact-sequence node supplies exactly the displayed order of the connecting maps. The scalar map is multiplication by f term by term, not a claimed unexplained compatibility. The zero complex handles M=0.
3. The finite-length filtration node supplies simple factors. The argument that every simple module over this local ring is its residue field is written out. Normalization supplies the residue-field dual, and Step 2 handles each extension. Exactness of localization is precisely what is needed to propagate support at the closed point through the filtration. No Matlis anti-equivalence or injective-hull identification is assumed.
4. The finite-module support-annihilator node states that the support is V(Ann), so a nonzero finite module contains the maximal ideal in its support. A second prime would give a chain of length one, contradicting d=0. The generic-stalk finite-length node actually states the required local support criterion and is applied only to a nonzero finite module. This sets the induction base without assuming the result being proved.
5. The quotient-dimension equality node explicitly permits a module nonzerodivisor, not just a ring nonzerodivisor. The chosen f is in the maximal ideal. Nakayama proves Q nonzero, and the equality makes its dimension d-1. The degrees i+1 outside [-(d-1),0] are checked for i<-d and i>=0; finiteness from Step 1 allows the second use of Nakayama.
6. The localization-exactness node gives the support inclusion for the injection of the cokernel into the next Ext of Q. The one-equation bound node has no nonzerodivisor requirement on P, which is essential here: f need not act injectively on Ext. Nakayama makes P/fP nonzero when P is nonzero, and the induction bound then yields dim Supp P <= -i. No localization-of-RHom theorem is assumed.
7. The Noetherian-submodule node applies to N inside the finite module M. A common exponent killing a finite generating set kills N. Away from the maximal ideal an invertible element kills N after localization. Thus the cited finite-length criterion applies when N is nonzero, and Step 3 applies also for N=0.
8. Exact localization identifies M and M/N away from the closed point. Since d>0, this quotient is nonzero; the support-annihilator criterion puts the closed point back, proving equality of the supports. The Noetherian definition makes the maximal ideal finitely generated, as required by the power-torsion quotient node. Its conclusion excludes every nonzero vector with annihilator the maximal ideal, exactly the hypothesis of the nonzerodivisor-existence node. Steps 5 and 6 are already proved for all modules of dimension d admitting such an element, so applying them to M/N is not circular.
9. The same exact sequence of Ext groups gives the degree vanishing. Exact localization gives support contained in the union of the outside supports. In degree zero, closedness and the local chain argument put each support inside the closed point; this avoids silently assuming a general dimension-of-unions theorem. In other degrees the torsion part's dual is zero. These arguments prove both clauses, not just one.

I checked small cases: M=0 gives empty support and zero dual; a residue field gives only degree-zero dual by normalization; every finite-length module follows its simple filtration; over a DVR, a free module has its dual in degree -1, while a direct sum with residue-field torsion has degree-zero support only at the closed point. The inductive argument does not assume completeness, regularity, a coefficient field, or equidimensionality. It never claims that f is a nonzerodivisor on an Ext module. No new unsplit statement, new notion, clause-restating node, or SGA source is introduced. Each non-elementary fact used has a cited node; the remaining support, scalar, and filtration arguments are explicitly written. All nine steps are under 2000 characters and hide no separate comparison theorem.

## Unfinished work

None in the stage-1 split. Its supporting nodes retain their current statuses; this delivery does not claim to prove Lean declarations.
