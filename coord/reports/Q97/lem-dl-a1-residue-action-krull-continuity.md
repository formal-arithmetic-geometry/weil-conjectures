# Q97: lem-dl-a1-residue-action-krull-continuity

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-residue-action-krull-continuity.json: item split into four elementary steps; statement unchanged; previous source, citations and searches retained; six actual logged searches appended.
- citations.json: empty list, because none of the proof steps cites a node. The statement retains def-pd-separable-closure as its definition dependency.
- report.md: this report.

No new nodes; no new Mathlib leaves.

## Attachments

None for the whole item. The sorry-free project definition IntermediateField.fixingSubgroupContinuousMulEquiv in lean/WeilConjectures/Mathlib/FieldTheory/KrullTopology.lean proves exactly the first topological clause for an arbitrary intermediate field of an algebraic extension. It contains no residue-action continuity assertion, so it does not discharge this conjunctive item. The older existing lem-exc-fixing-subgroup-krull-topology also only concerns the first clause, and assumes a finite intermediate field in a separable closure. It cannot prove the statement for arbitrary F. No declaration with the item's blueprint tag was found in WeilConjectures; concept searches and inspection of the relevant FieldTheory files found no exact attachment.

## WANTED

None. Both relevant Stacks files are present.

## Problems found and changes

The imported item had no proof, but its statement is correct. The first clause does not require F/K finite, nor Omega/K normal or separable. The previously recorded Loogle query KrullTopology, Continuous used an unknown identifier; the new query uses the actual fixingSubgroup name and was executed by msearch.py. All six new queries are recorded exactly as run in searches.jsonl and the node, with the actual returned names. Prior research remains verbatim.

The proof follows the finite-evaluation topology underlying fields.tex Tag 0BMJ (lemma-galois-profinite), and supplies explicitly the elementary quotient/lift calculation for the residue homomorphism appearing in pione.tex Tag 0BSW (lemma-identify-inertia). These source tags motivate the argument; no theorem about decomposition groups, finite étale lifting, compactness, or Galois correspondence is applied. The proof is marked agent-written because the arbitrary-local-subring generality and the finite-lift argument are elaborated here. Stacks' Galois hypothesis is not transferred to Omega/K: our topology is already specified in the item's statement.

## Searches and duplicates

Read coord/brief-stage1.md, stages/1-dag.md, the three levels in SETUP.md, GOAL.md, the item's chapter/unit records, and coord/delivery-errors.md B–E. The current blueprint rem-dl-a1-conventions was read under literature/blueprint/latest; its extension-across-infinity equivalence is the ancestor place served by this technical topological comparison. The blueprint search for Krull and residue action, the DAG filename/concept searches, and the source searches found no node covering the entire item. The existing finite fixing-subgroup lemma was opened and compared, rather than silently using it outside its hypotheses. No new node is proposed, so the same-tag new/existing duplicate checklist is vacuous.

Read Mathlib/FieldTheory/KrullTopology.lean for its finite-intermediate-field basis, stabilizer openness and topological group structure; Mathlib/FieldTheory/Galois/Basic.lean for the algebraic fixingSubgroupEquiv; Mathlib/FieldTheory/Galois/Profinite.lean for the continuous ordinary restriction maps returned by search; and Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean for mapAut and residue_smul. The ordinary restriction maps restrict field automorphisms inside the original extension, whereas the residue map passes through a quotient of T: they do not state the item's second clause. The algebraic residue-action instance supplies no topology comparison. The item is therefore split, not classified as a Mathlib leaf.

## Review by Q97

I read fields.tex at lemma-galois-profinite (Tag 0BMJ verified in tags/tags), including its description of the topology induced from maps of a discrete set, and pione.tex at lemma-identify-inertia (Tag 0BSW verified in tags/tags), including the decomposition group's action on the local ring and its induced residue map. The current blueprint's paragraph on unramifiedness at infinity gives the intended comparison; the proof stays below that unit route. There are no new nodes requiring additional sources.

Step 1 compares the actual equations defining neighbourhoods on both sides, including translates at any h. The bijection is justified by the F-fixing condition, not by a finiteness or Galois theorem. Both topologies use finite subsets of the same Omega. Thus the identification is a homeomorphism even when F/K is infinite.

Step 2 spells out well-definedness rather than assuming a local-ring automorphism fixes the maximal ideal without explanation: units are preserved, and in a local ring the nonunits are its unique maximal ideal. Invariance under inverses holds because Gamma is a group and the preservation hypothesis applies to every member. The same observation makes preservation of j(kappa_s) a bijective restriction. The induced automorphism fixes kappa by the precise hypothesis of the item, and the quotient equation gives the group law. No existence, surjectivity, or lifting theorem for Galois groups is used.

Step 3 uses only that finitely many exact point equalities define an open stabilizer in the stated Krull/subspace topology. Reducing the equality g(z_i)=z_i gives the equality on j(a_i); injectivity of j then gives equality on a_i. Fixing kappa and these field generators fixes all rational expressions in them, which is the asserted containment. I do not claim that every automorphism fixing residues fixes the chosen lifts, nor that this lift stabilizer is normal.

Step 4 repeats the same calculation for an arbitrary finite subset of kappa_s. Lifts exist by the definition of the quotient E, without any claim of compatible multiplicative lifts. For every point g, the set gH_A is explicitly the open set defined by the finitely many equalities h(z_a)=g(z_a). Its image lies in r(g)W_A by the homomorphism equation proved in step 2. Those cosets form the specified codomain basis, so the open-neighbourhood definition proves continuity at every point. This avoids hiding a finite-Galois-cofinality or continuity-at-identity lemma.

Each step is elementary from the definitions and hypotheses already in the item; no step takes a theorem from a cited node, hence citations.json is genuinely empty. The separable-closure definition was opened: it supplies the meaning of kappa_s in the statement, but the proof actually works for any invariant subfield, so no property theorem of a separable closure is invoked. None of the steps exceeds 2000 characters (lengths 568, 655, 525, 732). No elementary observation or clause of the item has been moved into a new node.

Small cases checked: F=K gives the identity comparison; F=Omega gives the one-element subgroup; arbitrary infinite F makes no difference to the finite-subset bases; Gamma trivial makes the residue map constant; T a field has zero maximal ideal and the quotient calculation reduces to restriction; empty finite subsets give the whole stabilizer; e=kappa with an empty generating family gives the whole preimage. No finiteness of T, no henselianity, no surjectivity of r, and no algebraicity of E/kappa is needed. No statement correction or unresolved mathematical issue remains.

## Unfinished work

None for the split. The required deliver.py --no-push invocation exited 0 with OK (not pushed) at aab168c201a; server preflight passed. The final report update is checked once more before the push.
