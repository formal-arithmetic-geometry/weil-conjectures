## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-nested-regular-ideals-finite-tor.json: item, statement unchanged, split following Stacks 09PW.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-tor-ideal-generators-injective.json: statement, unsplit; Stacks 09PV, no Mathlib match.
- citations.json: one entry per cited node per proof step, with verbatim statement quotations.

Attachments: none. Searched project WeilConjectures/ for the blueprint tag, nested ideals, finite Tor dimension, quotient regularity and generator-space injectivity. The project regular-sequence change-of-generators declarations and finite-projective-dimension theorem do not state the item. No Lean was written or compiled.

WANTED: none. All sources used are present in literature/stacks-project/.

The original statement is faithful to Stacks 09PW and needed no correction. It had no proof. Finite Tor dimension is already expanded using ordinary module Tor, so there is no comparison with an unspecified derived coefficient category. The only new input is 09PV; regularity of replacement generators is already supplied by lem-trf-lift-regular-generators-through-fibre specialized to the identity map. It would have been a duplicate to create another minimal-generator regularity node.

The ancestor command prints blueprint.from.node = None. The inherited created.item chain reaches lem-sfb-admissible-direct-image, which has no created record although its blueprint.from points to det-thm-sf-ctf-stability-direct-images. I retained that inherited null ancestor, copied the exact via chain for the new node, and made the immediate 09PW proof location explicit. The current blueprint/latest direct-image proof, paragraph (3), is the parent route; this split is supporting algebra along its existing etale-chart comparison branch. No chapter, unit or route was changed.

Nothing remains unfinished within this one-level split. The new 09PV node is intentionally statement-only and awaits its own split. Dry-run and delivery results are recorded below after execution.

## Not duplicates

lem-sfb-finite-tor-ideal-generators-injective vs lem-sfb-nested-regular-ideals-finite-tor: the new node states injectivity of K/mK into J/mJ for arbitrary nested proper ideals under a Tor bound. It assumes no regular generation of J and asserts no regular generation of K or J/K. The item's proof still constructs adapted generators and proves their prefix/tail regularity. The item mentions 09PV as a proof input in its source field, whereas its theorem is 09PW.

DAG searches by 09PV, 09PW, minimal generators and independence-of-generators found no existing generator-space injectivity theorem. The whole-blueprint searches by 09PV, regular sequence, minimal generators, ideal generators, finite Tor and generator spaces found no equivalent statement. The residue-basis node explicitly declines to assert regularity of a replacement list; the lift-through-fibre node does assert it and was reused. A full search of Lean by the item tag and its notions yielded no exact attachment.

## Review by Q61

I read dpa.tex Tags 09PW (lemma-regular-sequence, lines 1593--1621) and 09PV (lemma-injective, lines 1572--1591), including both proofs. For the one new node I checked 09PV's hypotheses: A is Noetherian local, both ideals are proper because they lie in m, and the Tor condition is exactly that of 09PV. Its proof's square-zero construction invokes the preceding lemma-not-finite-pd: a nonzero kernel class f can be isolated by an intermediate ideal between mK and K; its expression in mJ gives a relation whose lifted value is f, with multiplier 1 nonnilpotent in the residue quotient. This is a distinct homological obstruction, not the regular-generation conclusion of the item. I did not copy that argument into the unsplit statement.

For Step 1 I opened the entire statement of lem-trf-lift-regular-generators-through-fibre: it explicitly gives the residue basis and regularity for every lifted basis. With R=S=A, c=id, and its two ideals J, all its ring, finiteness, residue-field and beta-isomorphism assumptions hold. The ideal J is finite from its given regular generating list. Step 1 only takes its residue-basis clause.

For Step 2 the quote from the new 09PV node states the exact map and bound used. There is no unproved inference that finite projective dimension automatically gives an injection of arbitrary tensor inclusions; the necessary theorem is the new cited node.

Step 3 uses the definition of Noetherian ring, whose statement says every ideal is finitely generated. I wrote the finite scan argument for extracting a basis from the residues of a generating list. Its linear independence and spanning follow at each insertion/omission, with no general basis-extension theorem hidden in the step.

Step 4 first uses the already established injection to preserve independence. It then scans the original finite residue basis to extend the family; the insertion argument is explicit. I opened lem-sfb-independent-family-spanning-cardinality and checked Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:290--291: its statement bounds an independent family's cardinal by any spanning set's cardinal. Applying it to the two bases in both directions identifies their finite lengths. I replaced an initial terse reference to elimination by this existing Mathlib leaf, so no uncited dimension theorem remains.

For Step 5 I read lem-weil-pbc-nakayama-local-generators, and Algebra 00DV (lemma-NAK), especially items (4) and (8). The module K is finite by Noetherianity and its chosen residues span, exactly the generator-test hypotheses. I checked the second use of the lift-through-fibre node takes its regularity clause, with all identity-map assumptions as in Step 1. This is a generic algebra tool use, recorded in split_report.tool_uses; it does not introduce trace-formula hypotheses or change the unit route. Its dependency closure supplies ordinary commutative-algebra facts only.

For Step 6 I opened both cited statements: quotient-local-structure gives a nonzero local A/K with maximal ideal m/K; regular-sequence gives precisely the multiplication-injectivity and nonzero final quotient conditions. I also read Algebra 00E9 and 07BJ in the local-ring section. I corrected an initially guessed quotient-lemma tag to these actual labels. The successive tail quotients are identified by equality of the equivalence relation on representatives, so the same multiplication maps prove regularity; this is written explicitly. There is no assumption that A itself is regular local.

I tested K=0, K=J, J=0 (hence K=0), a field A (only J=K=0), and all empty-list boundaries s=0, s=r and r=0. For K=J, the Tor bound is zero and the quotient ideal is generated by the empty list. For K=0, the injection has zero domain and the prefix is empty. As a check that the new hypothesis matters, take A=k[x]_(x), K=(x^2), J=(x): the generator-space map is zero with nonzero domain, and k has nonzero Tor in every degree over k[x]/(x^2), computed by the periodic multiplication-by-x free resolution, so the Tor hypothesis correctly excludes it. A=k[x,y]_(x,y), K=(x), J=(x,y) tests a genuine nonempty prefix and tail.

I checked delivery-errors B--E against the files: the new node introduces every object and contains no proof; all notions have a definition citation or explicit meaning; the source is the actual 09PV label; no clause restates the item; every non-elementary input has a node that states it; proof_deps is exactly the union of uses; no cited statement depends on the item. All six proof steps are below 2000 characters. The logged Mathlib searches used two semantic phrasings, Loogle, LeanSearch and source grep. I read the candidate cotangent and quotient-projective-dimension declarations: their maps or hypotheses differ, so none is marked as a leaf. Every search record is copied from the actual searches.jsonl entries, preserving tool and query.

## Validation

The required deliver.py --no-push command exited 0 and printed OK at bf31f5b45f0: server preflight passed. This includes the server DAG and split checks. One new node, zero new Mathlib leaves. The inherited null blueprint ancestor was accepted; its cause and intended route remain documented above.
