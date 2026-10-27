# Stage-1 delivery: lem-sfb-relative-finite-hilbert-algebraic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-finite-hilbert-algebraic.json: item, split; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-hilbert-stack-descent.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-cover-stack-algebraic.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-weil-restriction.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for all 22 step citations.

## Attachments

None. Searched the item tag and Hilbert notions in lean/WeilConjectures. The Hilbert/Defs.lean interface is the set-valued functor of closed subschemes of a scheme fibre product, not the stack of arbitrary finite covers mapping to a space. Its representability results do not attach to this item. No Lean was written or compiled.

## WANTED

None. All sources are present in literature/stacks-project.

## Findings and proof route

The item is true as stated; no statement dispute or hypothesis change. Its source is criteria.tex Tag 06CI (lemma-hilbert-stack-relative-space). The empty sandbox contained only dispatcher markers and no delivery was running. The inherited item and its search records were retained. All additional Mathlib searches used msearch.py and their actual answers are saved and recorded, including two semantic phrasings per new node. Loogle's Weil hits are Weil divisors, not Weil restriction; the grep hits are analytical Hilbert bases or restriction of scalar fields. LeanSearch's pseudofunctor descent equivalence assumes a stack, and does not supply descent for the constructed finite-cover groupoid. None is an exact match or a one-line specialization.

The source chooses an atlas U of H_d(X), proves W=H_d(X/Y) times_{H_d(X)} U is a setoid sheaf, constructs V=W times_Y X, and applies the space bootstrap. Our same construction works for every scheme T mapping to H_d(X), not merely an atlas U. Thus q is representable; the already existing representable-source algebraicity theorem completes the proof. This is the same Hilbert/Weil-restriction/bootstrap route, and avoids a redundant new smooth-cover algebraicity node. The source's diagonal proof is written in step 2; no new node restates the diagonal or the item's conclusion.

Read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3). The current text uses compactification/proper and open direct images and does not spell out the inherited auxiliary alteration/moduli chain. blueprint_refs.py ancestor returns None, matching the existing null ancestor; retained the full inherited place and via list and added exact places for the new inputs. Whole-blueprint searches for finite Hilbert, Hilbert stack, faithful Hilbert, Weil restriction and source tags found no matching node; restriction-of-scalars hits are coefficient-module functors, not the geometric restriction functor.

## Not duplicates

- lem-sfb-finite-hilbert-stack-descent vs lem-sfb-relative-finite-hilbert-lci-open: the existing node proves openness and descent of the unramified lci locus under representability, flatness and lfp; the new node proves descent of the entire Hilbert groupoid for arbitrary F and gives no lci conclusion.
- lem-sfb-finite-hilbert-stack-descent vs def-sfb-relative-finite-hilbert-groupoids: the existing node defines the tuples and arrows (and lci subcategory); the new node proves effective fppf descent for those tuples, which is not asserted by the definition.
- lem-sfb-finite-hilbert-stack-descent vs lem-sfb-relative-finite-hilbert-algebraic: the item concerns algebraicity under an fppf space presentation; the new node is effective descent for arbitrary F, with no representability or atlas conclusion.

The other new statements have no source-tag collision. The finite-cover stack is a strict foundational special case, not a renamed relative-Hilbert algebraicity assertion: it has only Z/T and its isomorphisms, and no X, Y, F, target diagonal or nontrivial Weil restriction. The Weil-restriction node represents a functor of sets and asserts no stack algebraicity. The descent node works for arbitrary F and asserts neither representability nor an atlas. None is elementary from existing cited nodes: their proofs respectively need effective affine descent, an algebra-structure quotient atlas, and geometric representability of restriction of scalars.

## Review by Q132

I read criteria.tex 06CI in full, including its two displayed fibre-product constructions and the use of the space bootstrap; 05XW's diagonal argument; 05YH and 05YJ's Weil-restriction identifications; 05YS; 05YQ and its proof via the free-algebra quotient presentation; and 05YF. For the new descent node I read examples-stacks.tex 05WB and 05WC and the 05XV faithfulness proof. The new node asserts only the 05WB descent conclusion: the faithful argument remains explicitly in the item. For the other two new nodes, the precise sources are criteria.tex 05YQ (proposition-finite-hilbert-point) and 05YF (proposition-restriction-of-scalars-algebraic-space). Their definitions are included or cited, with all bases and ranks introduced. New nodes have no proof or hidden proof sketches.

Step 1 uses the new descent statement to get both H and H_X as fppf stacks, the exact tuple/arrow definition to compare arrows, the finite-locally-free definition for flatness and lfp, and the fppf-site definition for the covering. Positive d makes every fibre algebra nonzero; hence its spectrum is nonempty. Equality of y-isomorphisms follows from the assumed isomorphism sheaf, not an unproved diagonal hypothesis. I corrected the step's source document to examples-stacks.tex.

Step 2 uses the existing space-fibre-product statement for P and B, change-of-base (2) to view them over T, covering-calculus (2) for flat/lfp/surjective base changes, and precisely the existing bootstrap statement whose conclusion is that an fppf sheaf with a representable fppf space cover is a space. That bootstrap does not require a diagonal hypothesis. The explicit fibre P times_I T' equals A_1 times_T T' by alpha_2=phi alpha_1, so its hypothesis is really verified. No use is made of the cyclic stack bootstrap (the parent item).

Step 3 uses the Weil-restriction node with the actual finite locally free scheme Z/T and E=Z times_S X, space products to construct E, the tuple definition to normalize covers, the new C_d algebraicity statement, and the existing representable-source algebraicity theorem. That last theorem has no initial stack hypothesis and requires no lfp for its first conclusion. No closed immersion of Z into X is required.

Step 4 uses only step 2, the tuple definition, and the Weil-restriction theorem. The algebraic space here is Isom_Z(y|_Z,F(x)), not Isom_T of incorrectly based objects. I wrote the comparison maps, their inverse normalized tuple, the uniqueness of arrows preserving the comparisons, and pullback compatibility. This checks a groupoid equivalence, not merely a set of isomorphism classes.

Step 5 uses the fppf descent conclusion of the new descent node and the 2-fibre-product and arrow conventions. I wrote the entire short setoid argument: faithfulness kills automorphisms, unique local arrows satisfy cocycles, and descent glues objects and arrows. Thus the presheaf of classes is already a sheaf and W is equivalent to it. It is marked elementary because this is a direct componentwise descent and uniqueness argument from the cited statements, with no new geometric input or representability theorem.

Step 6 uses the explicit 2-fibre-product convention, the space-product theorem, and the statement of representable-pullback-over-space, which allows an arbitrary space base change with no atlas assumption. I checked that V's two descriptions retain exactly h,t,a and the two comparison isomorphisms with the same arrows. Its scheme fibres over W are the assumed X_y, not fibres of a different morphism. The existing sheaf bootstrap applies after step 5, and the existing representable-source algebraicity theorem then applies to q and H_X. These statements were opened and read, and citations.json copies their exact clauses. The only declared off-unit proof tools are the generic algebraic-space product theorem and the finite-locally-free definition; neither replaces a unit route.

Small cases: d=1 gives H_1(F) equivalent to X; F=id_S gives the ordinary stack C_d; empty base and empty X=Y allow empty atlases and fibres. d=0 is deliberately excluded from the faithfulness argument: a zero cover cannot detect two different target isomorphisms. Weil restriction with rank zero is terminal over T, and E empty with positive-rank Z gives the expected empty fibre; neither requires separation or finite presentation of E. Nonreduced T and inseparable finite covers are allowed throughout; no replacement of finite locally free by finite etale occurred. Arbitrary automorphisms in Y are retained until the faithful pullback kills them. All proof steps are below 2000 characters, no SGA source is used, and no cycle through the parent stack bootstrap is introduced.

I checked delivery-errors B to E: new statements are self-contained, correctly tagged, statement-only, searched and not duplicates; every non-elementary geometric fact is cited as a node; the item carries the diagonal argument and both functor identifications instead of moving its conclusion into a child. Statement/definition meanings and all extra assumptions were checked as above. No mathematical work remains unfinished in this one-level split; the three child proofs are intentionally queued as unsplit.
