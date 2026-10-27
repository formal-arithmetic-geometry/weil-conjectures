## Files written

- dag/nodes/sec-trace-formula/lem-trf-prelog-pushout-hom-extension.json: statement item, split into six steps; no exact Mathlib match.
- citations.json: five step/node citations, each checked against the current node statement.
- searches.jsonl: actual msearch records; seven fresh item searches, with both semantic phrasings read.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and prelog/logification/log-structure terminology found no declaration of this assertion. Related logarithmic material under lean/Sheaf is not an attachment under the brief.

## Wanted literature

WANTED: Kato (1988), Logarithmic structures of Fontaine--Illusie, section 1 (associated log structure and its universal property), for lem-trf-prelog-pushout-hom-extension. Travaux de Gabber VI 1.1 explicitly sends the reader there; its conventions do not provide the quotient proof. Accordingly proof_origin.by is agent.

## Corrections and route

The item statement, statement dependencies, source, and blueprint ancestry are retained. The live item had no proof. No statement dispute arose. The proof expands exactly the universal-property argument isolated from lem-trf-associated-log-universal-stalks, returned steps 4--5, in its fine-log chart-spreading ancestry; it does not invoke that parent, which would create a cycle. The companion lem-trf-prelog-pushout-log-axiom was opened: it constructs the log structure, whereas this item assumes it. Its construction theorem is unnecessary here.

Whole-DAG searches for prelog, logification, congruence and units isomorphism and whole-blueprint searches for prelog, associated log, unit pushout and log structure found no duplicate supplying the complete assertion. The existing monoid-sheafification leaf supplies the only non-elementary operation. The same-as list remains empty; the blueprint ancestor command confirms lem-trf-local-term-locality. This item is not the unit's key node, so no unit record changes.

## Review by Q150

I read Travaux de Gabber Expose VI 1.1, printed p.69 (the text beginning “Pour le langage des log schémas”), and its conventions on the etale topology, structural homomorphism and local Noetherianity. I read the complete log-structure definition in def-trf-fs-log-blowup and the complete statement and Mathlib match of lem-trf-commutative-monoid-sheafification. I also read Stacks sites.tex, section-sheaves-algebraic-structures, Tag 00YR, especially (alpha) and (epsilon), which identify algebraic sheaves and give the sheafification adjunction. The PDF is conventions only: I have not represented its reference to Kato as an available proof. There are no new nodes requiring additional sources.

Step 1 checks restriction of every generating relation and the identities i, j and eta on pairs. This is elementary from the quotient definition, naturality and the structural formula assumed by the item. Step 2 cites the log-structure definition for exactly its isomorphism from the inverse image of the units. Since this is an isomorphism of sheaves, its inverse is natural and monoidal on sections, and a section over a unit is its unique inverse image. No cancellativity, integrality, saturation or injectivity of gamma is used.

Step 3 uses that unique inverse image to show v(e)=j_K(gamma(e)), and writes both sides of the generating relation under the proposed map. The kernel congruence contains the generators and hence their generated congruence; this proves well-definedness directly, rather than citing an uncited pushout theorem. Multiplication uses commutativity of K. The restriction equality is written on representatives. These quotient and naturality calculations need no new lemma node.

Step 4 cites the existing sheafification node's actual Hom-bijection with target K, which is a monoid sheaf by the log-structure definition already assumed in the item. We do not use an existence theorem over an unverified large index category: eta is already assumed to exhibit sheafification, and a universe containing all site and coefficient data can be fixed as the cited node requests. Step 5 uses injectivity of that same Hom-bijection with target the multiplicative etale structure sheaf O_X; equality is checked on every quotient representative. O_X here denotes the fixed structure sheaf in the item's log-structure data, so no presheaf-to-sheaf assertion for a different ring object is being substituted. The formula at [m,1] establishes the first inverse identity.

Step 6 cites the log-structure definition for the unique lift of a unit, proving automatic unit preservation before using it. Its equation on [m,u] identifies g eta with the constructed w. It then cites the sheafification Hom-bijection for uniqueness, proving the other inverse identity. Both citations are to the statements, not to constructions hidden in their proofs. citations.json quotes their exact phrases and covers every uses entry.

I checked the small cases M=1 (only the unit group remains), the trivial log structure K=O_X^times whenever gamma factors through units, the zero ring on the empty etale object (0=1 and the unit group is singleton), and noncancellative M. None of the formulas cancels a monoid element or requires a nonempty object. A map v need not exist: the construction and inverse identities give a bijection of empty sets as well. Local Noetherianity is retained but unused by this formal argument. All six steps have fewer than 2000 characters; no hidden long comparison is present. No new statement-only node duplicates a clause of the item, and no Mathlib-leaf claim is made for generic results that supply only part of the assertion.

I corrected the initially tempting inference that compatibility alone determines a section of L: uniqueness is used only over units; equality of arbitrary maps out of L uses the sheafification Hom-bijection. The quotient's structure-compatibility is established before either inverse identity. No hypotheses or conclusion were changed.

## Unfinished work

None in the stage-1 split. Kato's source is wanted as above; the full replacement argument is recorded as agent-written. Delivery verification is performed by the required server dry run.
