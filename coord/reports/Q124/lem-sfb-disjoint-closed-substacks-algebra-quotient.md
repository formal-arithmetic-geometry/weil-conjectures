## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-disjoint-closed-substacks-algebra-quotient.json: item split into five steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-cartesian-module-fppf-realization.json: one new statement-only lemma, unsplit; no Mathlib match. This is the general cartesian scheme-module realization criterion, without algebraic-stack or closed-immersion hypotheses.
- citations.json: exact statement quotations for every step/node pair.
- searches.jsonl: searches actually run through msearch.py, including both semantic phrasings, Loogle and source grep. No query was invented. No Mathlib leaves were created.

## Attachments

None. Searched lean/WeilConjectures by the item tag and closed-substack, algebra-quotient, cartesian-module and fibred-module terminology. The scheme closed-immersion declarations returned by semantic search do not state the stack theorem. No project theorem covers every clause.

## WANTED

None for this split: the needed Stacks sources are present locally. The inherited blueprint metadata mentions an ancestor's wanted PDF; this work does not need that document.

## Issues found and choices made

No statement dispute or mathematical weakening. A surjection here means fppf-locally liftable; it does not mean surjective on global functions. The restriction formula on a nonaffine T is retained verbatim, not replaced by a globally surjective quotient of rings.

The initial source points to 06WT. That proposition is useful for presentation descent but is not the direct statement needed on an arbitrary fibred category. I read and extracted the more precise 06WK cartesian criterion instead. The new node's explicit section formula is its standard scheme-module formulation. The proof of 06WK invokes the associated-module equivalence; I also read descent.tex 03DT (lemma-sheaf-condition-holds) and 03DX (proposition-equivalence-quasi-coherent), and stacks-sheaves.tex 06WI and 0EM8, to check that sheafness and the local-presentation convention are included.

The Chinese remainder step has an elementary sheaf-local proof: the open complements of the two closed supports cover every test scheme, and on either complement one factor is zero. Affine refinement reduces lifting to A -> A/I. Thus no new CRT node, comaximality lemma, finite-product exactness lemma or closed-stack pushforward clause was manufactured. The algebra.tex 00DT proof was read as the source of the local observation. I read morphisms.tex 01QQ, 01QO and stacks-properties.tex 0507 to verify the closed-immersion and scheme-test scope.

I read the chapter and unit records, SETUP's three levels, and the current literature/blueprint/latest direct-images proof (3). The inherited ancestry serves the adequate-moduli supporting input below that unit; no unit or chapter route is replaced. tools/blueprint_refs.py ancestor reports a null blueprint ancestor for the current item. I retain that existing null and its explicit inherited proof place, and prepend the item to the new node's via chain. Blueprint searches for closed substack, cartesian quasi-coherent, compatible quasi-coherent, 06WK, 06WI, 03DX and quasi-coherent module found no exact duplicate. The latest blueprint does not state this auxiliary algebra lemma separately.

## Not duplicates

lem-sfb-cartesian-module-fppf-realization vs lem-sfb-stack-flat-scalar-sections: the existing node assumes a quasi-coherent algebra on a qcqs algebraic stack and proves flat scalar extension of global sections and preservation of surjections. The new node constructs an fppf sheaf from compatible ordinary modules on every object of an arbitrary fibred category, with no qcqs or flat-base-extension hypothesis. Their common tag 06WK is a source input, not equality of statements.

lem-sfb-cartesian-module-fppf-realization vs lem-sfb-qcoh-presentation-tensor-equivalence: the existing node is a DM/etale-atlas equivalence for cartesian module assignments and does not identify those assignments with big-fppf local-presentation sheaves; the new node needs no atlas or DM hypothesis.

lem-sfb-cartesian-module-fppf-realization vs lem-sfb-groupoid-module-descent-tensor-cokernel: the existing node concerns modules on a specified scheme-groupoid quotient and descent data on that groupoid. The new node concerns any category fibred in groupoids and explicit sections on all scheme objects, without a quotient presentation. It cannot be obtained by applying that statement when the general stack relation is only an algebraic space.

lem-sfb-cartesian-module-fppf-realization vs lem-sfb-disjoint-closed-substacks-algebra-quotient: the new node has no closed substack, algebra product or surjection conclusion. Steps 1 and 3 supply its substantive cartesian-module hypotheses, and step 4 proves the quotient property separately. It does not restate a clause of the item.

## Review by Q124

I checked B--E against the actual source text and the statements, rather than treating a source tag or a definition as a theorem. For the item I read the scheme ideal/closed immersion correspondence (01QQ), affine closed-immersion characterization (01QO), invariant closed-substack descent (0507), and the two-ideal argument in 00DT. For the new node I read 06WK and its proof, 06WI, 0EM8, and the associated-module results 03DT/03DX invoked there. Its generality is intentional: the argument restricts to each object's scheme and does not require the fibred category to be an algebraic stack.

Step 1 uses the definition contained in lem-sfb-invariant-closed-substack-descent: every scheme pullback is a closed subscheme. def-weil-closed-immersion explicitly supplies the affine quotient characterization and affineness. The structure sheaf is a free rank-one module, hence quasi-coherent. lem-weil-pbc-affine-pushforward-base-change (1) gives quasi-coherence, (2) gives the algebra comparison for O, and (3) gives its composition compatibility. I checked that no flatness, noetherianity or finite presentation is required by that node. Its arrows are scheme morphisms here, as required.

Step 2 applies exactly the new node's realization statement, including sheafness, to the assignments and comparisons already constructed. The equality of section formulas is the definition of ordinary direct image, and the algebra operations commute with the algebra comparison of step 1. def-sfb-stack-quasi-coherent-algebra really uses this big-fppf local-presentation convention.

Step 3 uses lem-weil-pbc-quasi-coherent-module-direct-sum for ordinary scheme modules, not a stack theorem. I checked its statement includes the componentwise binary sum. A binary module sum is also its product. The pullback comparison is written using the inclusions and projections and the additive tensor formula from def-pc-module-pullback. The identities displayed in the step prove that comparison is invertible; hence there is no hidden preservation-of-products theorem. The realization criterion then applies a second time.

Step 4 takes precisely the base-change-image clause in lem-sfb-smooth-presentation-closed-subsets to obtain disjoint closed supports on arbitrary T. def-weil-closed-immersion supplies closedness and the affine quotient description. On either open complement one closed scheme has empty underlying space and is the empty scheme, so its section ring is zero. A representative of the other quotient element gives the local lift. The two open complements cover because the original supports are disjoint; affine open refinement is an fppf cover. This proves exactly the locally surjective definition, without a global-sections exactness assertion. The whole residual argument is elementary from these cited statements.

Step 5 evaluates the convention in def-sfb-stack-quasi-coherent-algebra on every object. It checks the actual canonical restriction maps, not merely the existence of some map. No additional comparison theorem is used.

Small cases: an empty ambient stack; either or both closed substacks empty; one substack equal to the ambient stack (forcing the other empty); a disjoint decomposition of the ambient stack; nonreduced closed subschemes; infinitely generated defining ideals; nonflat base change. All are covered. The hypothesis of disjointness is necessary: taking both substacks equal to Spec k makes the diagonal k -> k x k nonsurjective, also locally. The new criterion handles the zero module and arbitrarily generated modules, and requires a genuine cocycle rather than unspecified isomorphisms. None of its statements contains a proof sketch. No proof step exceeds 2000 characters. Generic off-unit scheme tools are declared in split_report.tool_uses. No SGA source is used, and no Lean file or compiler was touched.

## Unfinished work

The new statement-only criterion deliberately remains unsplit for a later item. The present item's mathematical split and citation audit are complete; required server checks and direct delivery follow.
