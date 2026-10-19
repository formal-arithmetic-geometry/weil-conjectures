# Q108: complete algebraic dévissage and projectivity after localization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-complete-algebra-devissage-projective-localization.json`: item, statement, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-basis-base-open-universal-injectivity.json`: new statement-only node, unsplit; no Mathlib match. This is the base-open universal-injectivity part of Stacks 05IA, with an already R-flat module.
- `citations.json`: 29 exact statement quotations, one for each use in each numbered proof step.
- `searches.jsonl`: the actual search-command log; the item retains the searches inherited from its creator and adds the searches performed by Q108.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` by the item's exact blueprint tag, projective-localization terms, and dévissage terminology found no declaration of complete algebraic dévissage or the present theorem. The generic-basis / universal-injectivity searches in the algebra-related project directories likewise found no declaration of the new lemma. The homotopy-category and constructible-sheaf dévissage declarations concern different objects. No upstream-master sorry is treated as a finished proof.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Audit of the starting node and route

The statement is the projectivity conclusion of Stacks Tag 05IB (`flat.tex`, `lemma-complete-devissage-flat-finitely-presented-module`, lines 3228 onward). It is correct and has not been changed. In particular N is finitely presented over S, not over R. The generic finite-presentation/flatness implies projectivity theorem in Mathlib cannot apply directly to N over R. No extra hypothesis, Noetherian assumption, or finite generation over R was introduced.

I read the trace-formula chapter, the sk-i-curve-zero unit and the inherited blueprint ancestry. This is supporting commutative algebra in the historical semistable-alteration branch recorded by the parent, not a replacement of the current unit's contracting-correspondence proof. The inherited from.place records that history; the new node adds the precise 05IB induction sentence served. Neither chapter nor unit has been changed. This item is not the unit's key node.

The only new statement isolates the shrinking of the first free map. It says nothing about complete dévissage or projectivity, and therefore does not restate the item or a projectivity clause of it. The proof of the item itself carries the tail induction and splitting.

## Searches and Mathlib verdicts

Before creating the new node I searched the whole DAG by 05IA / induction-step-fp and by generic basis, universal injectivity and localization, and searched the whole blueprint with blueprint_refs.py for 05IA, universally injective, generic fibre, devissage, and projective-related phrases. The broad projective result list contains geometric/projective-morphism statements, not this module shrinking assertion. No blueprint node supplies it. The new id is distinct from all existing ids. I read the existing 05I3 local generic-basis and free-subtraction statements and the 05FT / 0564 / 058P nodes rather than duplicating them.

The actual Mathlib commands queried LeanFinder with two phrasings of the new lemma, LeanSearch, Loogle `Module.Flat, LinearMap.lTensor`, and grep for universal-injectivity/pure-localization terms. Semantic searches returned flat localization, going down, and topological universally injective scheme morphisms. These are not universal injectivity of a module map after tensoring with arbitrary modules. The Loogle tensor-injectivity theorem assumes the tensoring module is flat, whereas the desired map must survive tensoring with every module. The new lemma is unsplit, not a Mathlib leaf.

For the item I ran two fresh natural-language searches, Loogle and grep. I read `Module.Flat.projective_of_finitePresentation` at Mathlib/RingTheory/Flat/EquationalCriterion.lean:287-289: its finite-presentation hypothesis is over the same ring as projectivity. I also read `Module.FinitePresentation.exists_notMem_bijective` at Mathlib/Algebra/Module/FinitePresentation.lean:510-518: it spreads a localized isomorphism in the module's coefficient ring, not a universally injective map on an open of a smaller base. Neither is a one-line specialization. The exact queries/results and verdicts are recorded in the node files and command log; no failed service has been recorded as a negative search.

## Not duplicates

- lem-trf-generic-basis-base-open-universal-injectivity vs lem-trf-local-generic-basis-universal-injective: the existing 05I3 statement is over a local base and concludes universal injectivity there. The new 05IA statement produces one principal open of the original, possibly nonlocal base; finite presentation is what permits this spreading.
- lem-trf-generic-basis-base-open-universal-injectivity vs lem-trf-free-subtraction-flatness: the existing statement assumes generic-basis conditions at every base prime and concludes universal injectivity globally. Here the basis condition is at one specified base prime, and the conclusion requires finding a base neighbourhood.
- lem-trf-generic-basis-base-open-universal-injectivity vs lem-trf-complete-algebra-devissage-projective-localization: the new node has no dévissage or projectivity conclusion. It is the free-subtraction tool used before the smaller-length induction.

The new source tag 05IA has no other existing node. Existing 05FT, 0564 and 058P statements are cited, not recreated. The two existing 05FT interfaces are themselves already in the DAG; I use lem-trf-local-fibres-integral-projective.

## Review by Q108

I read the full statement and induction proof of 05IB in flat.tex, definition 05HX and remark 05HY there, 05IA's statement and proof of (1) implies (2), and 05FT. I also read Algebra 0564 and 058P in algebra.tex, checking their hypotheses against the existing nodes. For the new node, 05IA is applied with q=p=rB. Its explicitly stated prime and contraction hypotheses make this choice legitimate; localizing an R-flat module in B preserves R-flatness, so 05IA(1) holds. The extra cokernel-neighbourhood assertion of 05IA(2) is not claimed by the new node. It has a self-contained statement and no proof or proof dependencies, as required for a newly created unsplit node.

Step 1 uses the complete-dévisage definition for the chain, its zero case and N=M1; the projective-module definition gives the zero-module lifting property. The induction is on length, for all allowed algebras and modules, not on an unstated finiteness invariant.

Step 2 uses exactly the affine smoothness comparison and smooth-ring-map definition for finite presentation, smooth-ring-map flatness for flatness, and smooth-geometrically-reduced for reducedness after every residue-field extension. The given irreducibility plus the integral-scheme definition gives integrality. I checked that nonemptiness is included in irreducibility and that the integral definition explicitly includes the equivalence with reduced plus irreducible. This supplies both hypotheses of 05FT and the fibre hypothesis of the new lemma; smoothness alone would not supply geometric irreducibility.

Step 3 uses 0564 twice, with finite AND finitely presented algebra maps. For S to A1, finiteness follows from surjectivity. For B1 to A1, finiteness is part of the dévissage, but finite presentation is not assumed there; the proof explicitly supplies it. Composition gives A1 finitely presented over R; the displayed B1-polynomial presentation then proves that B1 to A1 is finitely presented. Thus the cited finite-extension theorem applies without a Noetherian assumption. This is the point where an unverified 'finite implies finitely presented' would be wrong. I did not use such an inference.

Step 4 takes the base-open universal-injectivity conclusion from the new node and the fibre isomorphism/prime ideal from the complete-dévisage definition. The nonzero fibre proves contraction to r, so every extra hypothesis in the new node is checked rather than added to the item.

Step 5 uses only the smooth clause of lem-pc-proper-base-change and the algebra finite-presentation base-change theorem, together with the complete-dévisage, flatness and localization definitions. It writes why localization preserves cokernels and the finite data, why the fibre condition remains the same, and why localized flatness follows by a tensor identity. These are routine fraction and presentation arguments, not a hidden new theorem. No properness assumption is used.

Step 6 applies lem-trf-local-ui-flat-cokernel to a genuinely universally exact sequence, whose universal exactness comes from the universal injectivity just obtained and the quotient description of the cokernel. Its middle module is flat by hypothesis and localization. The finite-presentation definition supplies the explicit finite matrix for C, adding r1 relations; no sheaf-cokernel theorem is misapplied to modules. The complete-dévisage statement supplies precisely the tail identification. At n=1 its final cokernel is zero.

Step 7 invokes only the induction hypothesis at length n-1, after checking its new algebra B1, module C, flatness, finite presentation and tail data. This is not a circular citation of the item. The projective and localization definitions cover the zero-cokernel case and the elementary preservation of exactness already proved with fractions.

Step 8 takes projectivity of the localized B1 from the exact 05FT node statement, under the flatness, algebra finite presentation and geometrically integral fibres established earlier. It does not use the theorem for a merely irreducible nonreduced fibre. Finite sums preserve lifting by adding componentwise lifts, as written; this is an elementary step within the proof, not a new node.

Step 9 uses the projective-module lifting property to obtain a section of the actual quotient onto C_h. The splitting formula and its inverse via the kernel prove the decomposition. I checked the final localization, rather than merely saying to clear denominators: for h=a/f1^k, the composite localization inverts both f1 and a, hence equals localization at f1*a by the ring localization universal property. The displayed fraction formula respects the scalar action. Projectivity transports along that ring isomorphism. The final f lies outside the original prime because both factors do.

For edge cases I checked n=0, n=1, zero free rank, N=0, and a general non-Noetherian base. A zero base ring has no specified prime, so contributes no counterexample. A smooth algebra with empty fibres cannot satisfy the stipulated geometrically irreducible/nonempty fibre condition; no such case was fed into 05FT. I also checked the example S=R[x], N=S: it is not finitely generated over R in general, and the split does not assume it is. All nine proof steps are shorter than 2000 characters. Every cited statement was opened and its used portion copied verbatim to citations.json. Off-unit generic tools are declared with their purposes in split_report.tool_uses. No definition, statement, Lean file or launcher file outside this item's authorized sandbox was edited.

## Unfinished work

The single new 05IA consequence remains statement-only, to be split in a later item. This is the intended one-level boundary. No part of this item's induction is left implicit as a future proof obligation.
