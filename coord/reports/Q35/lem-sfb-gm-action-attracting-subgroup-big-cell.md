# Stage-1 delivery: lem-sfb-gm-action-attracting-subgroup-big-cell

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-gm-action-attracting-subgroup-big-cell.json: item split, statement unchanged; no Mathlib match after four search kinds and two semantic phrasings.
- citations.json: verbatim live-statement quotes for every step/node pair.
- No new nodes, no Mathlib leaves, no unit-record edits, no Lean files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and attracting/cocharacter terminology. The semidirect-product hits in LinearAlgebraicGroup/RankOne.lean concern an abstract degree datum and do not state this scheme theorem. The existing tangent and group-scheme infrastructure does not supply every clause of this item.

## Literature

WANTED: Brian Conrad, Reductive group schemes, Theorem 4.1.7 and the paragraph after Example 4.1.9, printed pp.112-114, for lem-sfb-relative-dynamic-subgroups as used by this item. No local copy was found in the named literature directory. Read online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf; no download or literature edit was made.

Read Milne, Algebraic Groups, printed pp.261-266 (concentrators and Theorem 13.33) and pp.267-270 (Luna maps and Theorem 13.41). The proof is marked agent-origin because its assembly specializes existing DAG inputs, with the missing local reference recorded above. Conrad's theorem uses the dynamic method, with its semidirect-product reduction, rather than a forbidden SGA source. The inherited Milne route is preserved.

## Problems found and corrected

No mathematical statement dispute. The original item had no proof. Its blueprint ancestor command returns None: the inherited provenance chain is broken before a blueprint node. I retained all inherited provenance fields, searched the whole blueprint, and recorded the exact supporting place in split_report instead of inventing an ancestor. The current latest blueprint unit and direct-images proof were read; this item is a supporting group-theory input below the alteration branch, not the unit's key statement.

I initially considered reusing the algebraically closed cocharacter-limit and transverse-subgroup nodes, then found the existing arbitrary-ring dynamic-subgroup theorem. Reusing that existing statement avoids duplicate nodes and additional field-descent machinery. The new proof still carries the stability argument, the zero-tangent fixed-group argument, the identification of the actual multiplication map, and density. Nothing was moved into a new node.

## Not duplicates

No new nodes. Existing lem-sfb-relative-dynamic-subgroups is strictly more general than the required dynamic-subgroup input and is cited directly. The existing positive-weight-affine-space-arbitrary-field node supplies its explicitly allowed zero-dimensional case; no new zero-dimensional-group lemma is created. Searches also inspected cocharacter-limit-smooth-structure, smooth-affine-concentrator, transverse-subgroup-product-open, torus-fixed-scheme-smooth, torus-centralizer-smooth-connected, and the full blueprint searches for cocharacter, concentrator, subgroup/tangent, multiplicative/action, dynamic/subgroups and positive/weight.

## Review by Q35

I checked B through E of delivery-errors against the five steps, with each cited statement open. There are no new statements to audit, and all cited inputs are existing nodes. The item has exactly its original hypotheses and conclusion. All steps are under 1000 characters, so none exceeds the 2000-character long-step threshold. Every non-elementary inference is supplied by a cited statement. The naturality and orbit calculations in step 2 are written out rather than hidden under a compatibility claim.

Step 1 uses the finite-type/Noetherian finite-presentation statement only for the coordinate algebra. A field is Noetherian by its two possible ideals. This verifies the finite-presentation hypothesis of the relative dynamic theorem. That theorem's statement explicitly treats an arbitrary automorphism action and all test algebras. It supplies smoothness, closedness, connected geometric fibres, positive Lie weights, the fixed subgroup with zero-weight tangent, and the limit-group semidirect-product isomorphism. Apply it again to the reciprocal action to reverse the signs. Its arbitrary-base-change clause makes geometric connectedness applicable, with no assumption that the ground field is perfect or infinite. I compared its formulation with Conrad Theorem 4.1.7 and Milne 13.33.

Step 2 uses only dual-number naturality and injectivity of closed-subgroup tangent maps from the affine-group calculus statement. The stability calculation is explicit over every A: commuting the action of t with the orbit parameter gives an extension with value 1 at zero. Laurent restriction is injective even for nonreduced A, since polynomial coefficients remain unique. The universal affine point gives the scheme action. Differentiating the commuting inclusion diagram gives equivariance. This is an elementary application of the cited calculus and the action identities, not an unsupported general representability assertion.

Step 3 uses exactly the zero-dimensional clause of the positive-weight theorem, whose statement expressly permits an empty direct sum and any field. The fixed subgroup from step 1 has all its required hypotheses: smooth, geometrically connected, affine, finite type, rational fixed identity, zero tangent. I supply the trivial action on it. No argument incorrectly infers positivity from merely having no zero weights on H; the positivity hypothesis is vacuous on the zero tangent of Z. The conclusion identifies the whole scheme with Spec k, and hence all A-points with the identity, not only geometric points. I read the local source Theorem 13.41, including its zero-dimensional specialization.

Step 4 uses the dynamic theorem's actual scheme multiplication isomorphism and open multiplication map. With Z the trivial subgroup, its isomorphism Z times U_+ to P is literally the inclusion of U_+ into P; the test-algebra formula verifies this identification. Substitution therefore gives the stated multiplication in the stated order U_- times U_+, with no accidental reversal or different map. The image contains 1.

Step 5 uses smooth-over-field regularity, then regular/nonempty/connected implies integral, with the identity providing nonemptiness and geometric connectedness providing connectedness. The integral definition explicitly includes irreducibility. The open-immersion definition makes the image a nonempty open subset, and the two-disjoint-opens contradiction proves its density in the underlying space. These are generic scheme tools, declared in split_report.tool_uses where they cross units, not a change of the unit's route.

Small cases: H=1 gives U_-=U_+=1 and the identity open immersion. For a trivial action on any H, both attracting subgroups are 1 and h_0=Lie(H); the big-cell hypothesis applies only in the zero-tangent case, consistent with the fixed-subgroup argument. For Ga with action t^n, n>0 gives U_+=Ga and U_-=1, while n<0 reverses them. On Ga^2 with weights +1,-1 the multiplication is the usual additive isomorphism. In characteristic p the weight p is still a positive algebraic character, despite its differential on the torus being zero; the proof never replaces characters by differentials. Finite fields, imperfect fields and nonreduced test algebras are allowed throughout. A disconnected zero-dimensional smooth group would invalidate step 3, but the connectedness hypothesis is supplied explicitly, so that case is excluded legitimately.

I checked proof_deps is the union of all uses and created citations.json by copying the live statements verbatim. I preserved the existing statement, source, created fields and blueprint fields. No Lean, compiler, Lake, repository writes, launcher edits, or subagents were used. Actual Mathlib queries are logged in searches.jsonl; returned affine-space, abstract-group, Lie-weight and smooth-locus hits do not state this algebraic-group theorem. No search was invented or unavailable result called a negative match.

## Unfinished work

None at this one-level stage-1 split. The already existing unsplit dynamic-subgroup and positive-weight nodes remain independent queue items; this delivery does not claim to have split or proved them.
