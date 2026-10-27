# Stage-1 delivery: lem-sfb-divide-finite-flat-subgroupoid

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-divide-finite-flat-subgroupoid.json: existing statement, now split in ten steps; no Mathlib match.
- citations.json: one entry for every cited node at every step, copying its statement verbatim.
- searches.jsonl: actual msearch results. write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, divide/subgroupoid wording, GroupoidScheme and subgroupoid. No declaration states the item. Mathlib's ordinary categorical quotient groupoid does not construct an internal groupoid in schemes.

## WANTED

None. All required mathematics is in the available Stacks sources.

## What was wrong or incomplete

The item had no proof. Its statement is unchanged. It strengthens the terse conclusion of Stacks 04S4 by spelling out surjectivity, the unit kernel square and the equality-of-arrow-images criterion. These are valid: the first is included in the existing affine quotient theorem, the second follows from the restriction pullback (also written in 06N0), and the third follows from canonical transport and the effective kernel pair P. No STATEMENT-DISPUTED correction is necessary.

The source's last paragraph says that the represented quotient sheaf has the plain-groupoid operations, without checking descent of their formulas. Steps 6-9 supply those checks. Composition requires a lift of the common middle object; it is constructed on the pullback of q^3, not by assuming arbitrary global lifts exist. Associativity is checked after q^4. The source also has a typographical omission in the sentence giving the iff characterization (the expression r' = is missing); step 5 writes the complete equality.

The inherited blueprint.from.node is null. The prescribed blueprint_refs.py ancestor command independently reports None. I retained that maintainer-owned value, its detailed place and the via chain. I read the current latest blueprint unit and direct-image proof, rather than an old snapshot. This is a generic prerequisite in the recorded alteration/moduli route, not a replacement of a unit step.

## What remains unfinished

Nothing in this item's one-level split. Existing dependencies remain their own DAG items; none has been duplicated or silently assumed proved in Lean.

## Searches and reuse

Read every inherited mathlib_searches record, including both LeanFinder phrasings and the earlier LeanSearch, Loogle and grep results. Repeated the item searches with the mandated msearch command under Q84 so the present transport/descent question was checked and logged: LeanFinder on division by a finite flat monomorphic subgroupoid; LeanSearch on descent along the equivalence subrelation; Loogle on Groupoid and Scheme; grep on GroupoidScheme|subgroupoid|quotientGroupoid. Hits concern ordinary groupoids, finite-group quotients in Galois categories, affine scheme morphism properties, and general stack descent. None specializes to this statement in one line.

Also investigated whether a finite-locally-free base-change node was needed. msearch LeanFinder, LeanSearch, Loogle and grep return the separate finite, flat and locally-finite-presentation base-change instances. No node was created: step 2 obtains exactly the required assertion in a few lines from existing finite permanence, fppf covering base change, and the definition finite+flat+locally-finite-presentation. Composition is already the Mathlib leaf lem-trf-finite-locally-free-composition. This avoids an elementary new node.

Searched the entire DAG for 04S4, 03BM, finite-flat equivalence quotients, quasi-finite effective descent, fpqc descent of morphisms and covering permanence. Used blueprint_refs.py search for finite flat equivalence, divide subgroupoid, double coset, and base change finite locally free: no blueprint match. The 03BM and 02W8 nodes already present are reused as generic tools, declared in split_report.tool_uses alongside the kernel-pair quotient-descent lemma. There are no new-node duplicate pairs.

## Not duplicates

No new nodes. The existing 03BM quotient theorem is cited, not recreated. Of the available 02W8 effectivity results I use the fppf covering-family theorem; its singleton specialization is precisely the required case.

## Review by Q84

I read bootstrap.tex, Tag 04S4 (lemma-divide-subgroupoid), its whole proof and the preceding plain-groupoid discussion, groupoids.tex Tag 03BM (proposition-finite-flat-equivalence), more-morphisms.tex Tag 02W8 (lemma-separated-locally-quasi-finite-morphisms-fppf-descend), descent.tex Tag 023Q (lemma-fpqc-universal-effective-epimorphisms), morphisms.tex Tags 02KC/02KD, and the cartesian-square paragraph of stacks-morphisms.tex Tag 06N0. There are no new nodes whose sources need separate review. No SGA route is used.

For step 1 I opened and read def-a1-groupoid-scheme, def-pc-finite-locally-free, lem-weil-pbc-finite-morphism-permanence and lem-a1-finite-flat-affine-relation-quotient. The permanence theorem actually gives affine source over an affine target, allowing the affine hypothesis on P in the quotient theorem. The monomorphism to U times_S U gives uniqueness of relation arrows; identities, inverse and composition give the three equivalence laws. Thus 03BM has every hypothesis, and its statement supplies all of the quotient assertions used. Composition compatibility is a direct consequence of that uniqueness.

For step 2 I read lem-a1-fppf-kernel-pair-quotient-descent, lem-trf-fppf-covering-base-change, lem-trf-finite-locally-free-composition, lem-trf-fppf-covering-is-fpqc and def-pc-fppf-site. The first states that q is an fppf covering under exactly the kernel-pair and surjectivity hypotheses obtained in step 1. Finite permanence gives finiteness after base change; covering base change supplies flatness, local finite presentation and surjectivity. Together these give finite locally free, so the composition leaf applies to q^n. No affine, Noetherian or finite-type hypothesis on S has entered.

For step 3 I read the actual groupoid and fibre-product definitions. The inverse formula has the correct endpoints, and composing transports cancels the two middle factors to give the displayed cocycle. This is an elementary computation, not an invocation of a hidden quotient lemma. I deliberately keep the source order (t,s) during the construction and specify the factor swap to the item's (s,t).

For step 4 I read the full statement of lem-trf-separated-lqf-fppf-effective-descent. It accepts a singleton fppf covering, requires separated locally quasi-finite local structure maps, and imposes neither quasi-compactness nor local finite presentation on R over V. The item's j hypothesis supplies exactly these assumptions. Its conclusion explicitly identifies the descent datum with canonical transport, which is the ingredient step 5 uses. The covering base-change lemma really gives h as an fppf covering. I read lem-weil-pbc-fpqc-representable-descent; its statement gives existence and uniqueness of compatible morphisms, not just the definition of descent, so it supports all subsequent gluing and equality tests.

In step 5 the endpoints of two arrows with equal h-images yield actual T-points of P times_S P by the kernel-pair identification. The canonical-descent identification then forces the precise formula. This proves the global iff without presuming that a general point of the sheaf quotient has a global representative. Replacing an inverse arrow by its inverse gives the exact form written in the item.

For steps 6 and 7 I checked compatibility on the entire kernel pairs before applying the quoted representable-descent statement. Inverse sends p^{-1}rp' to (p')^{-1}r^{-1}p. For units, the unique P-arrow p:x to y gives e(y)=p e(x)p^{-1}; the same image criterion gives h(p)=he(x). The maps over S are checked after the covering, as required by the statement of representable descent.

For step 8 I checked the morphism D to bar_U^3 and that its base change by q^3 is a covering by the cited base-change lemma. Three chosen object lifts determine the two lifted arrows via the actual pullback isomorphism, so their composition is defined. On overlaps, a'=u_2 a u_1^{-1} and b'=u_1 b u_0^{-1}, hence a'b'=u_2 ab u_0^{-1}. This is precisely the compatibility required for representable descent. In step 9, unit and inverse laws are the original laws after h; composable triples use four object lifts and q^4. Uniqueness in the cited descent theorem reflects equality. These checks prove all operations are preserved, rather than merely transporting a groupoid structure without explanation.

Step 10 proves the kernel square on all test schemes using the fibre-product universal property. If h(r)=bar_e(u), its endpoints have q-image u and give a unique p in P; the pullback description of R forces r=p. This is equality as schemes, not containment of topological supports. The same natural correspondence identifies the two asserted descriptions of P.

I checked B-E against the finished JSON: self-contained unchanged statement and definition citations; no new unsplit statements with hidden proofs; no duplicated or restated clause nodes; no circular dependence on the item; every non-elementary inference cites a statement I read, and citations.json copies that statement verbatim. Every proof step is below 2000 characters. Small cases checked: U empty (all relations and descended objects empty); P the identity relation (q and the descended groupoid recover U,R); P=R a finite flat equivalence relation (the descended arrow relation is the identity); nontrivial isotropy in R (not killed unless in P); and q a finite-flat cover without a global section (local lift constructions remain valid). The monomorphism hypothesis on P is essential for unique connecting arrows and is used in each relevant step. No new statement requires a separate small-case test.
