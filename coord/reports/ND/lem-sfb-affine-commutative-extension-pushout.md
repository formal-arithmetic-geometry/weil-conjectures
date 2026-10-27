# Stage-1 delivery: lem-sfb-affine-commutative-extension-pushout

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-commutative-extension-pushout.json: statement, split in six steps; no Mathlib match.
- citations.json: 18 verbatim statement quotations, one for each step/node citation.
- searches.jsonl: actual msearch log, preserved as generated.

No new nodes; no new Mathlib leaves. Only the sandbox was written. No Lean writing, compiler, Lake, build, repository git operation, or subagents.

## Attachments

None. Searched all lean/WeilConjectures for the blueprint id, antidiagonal, group-extension pushouts and affine quotient terminology. The abstract extension and torsor contracted-product results do not state affine representability and every clause of this item. GroupScheme/Basic.lean supplies no such quotient construction. No sorry-free project attachment found.

## WANTED

None: the needed Milne PDF and Stacks source are available.

## Findings and corrections

The original statement is retained verbatim. It is valid without perfectness, smoothness or connectedness. Its empty proof is replaced by the antidiagonal argument that makes Milne Proposition 14.48's pushout diagram explicit. This is marked proof_origin.by = agent: Milne does not write out this whole construction.

The existing reviewed lem-sfb-affine-normal-quotient-geometry already gives the hard representability theorem, the fppf quotient interpretation, kernel and faithfully flat finitely presented quotient map. The existing lem-sfb-faithfully-flat-group-quotient-universal gives the relevant factorization theorem. I reused both instead of creating a quotient theorem or separate nodes restating clauses of the item. To establish faithful flatness of q-prime I compare E/K to Q by two explicit inverse homomorphisms; I do not infer flatness from pointwise surjectivity. Kernel coordinates are glued over arbitrary algebra-valued points, not merely over fields.

Read SETUP's three levels, GOAL, the chapter/unit records, and the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This auxiliary structural-group lemma stays below the inherited alteration prerequisite chain; it changes no chapter/unit route. The ancestor command reports blueprint.from.node = None for this inherited chain; its precise existing from.place and via list are retained. Blueprint searches for pushout, normal subgroup, group quotient, and quotient.*normal found no same statement. same_as remains [].

Mathlib searches: read the six new msearch results, with two semantic phrasings, Loogle, LeanSearch and two grep scopes. The first grep scope AlgebraicGeometry/Group returned zero, so I broadened to all AlgebraicGeometry. The broader hits concern ring pushouts, affine gluing, fppf precoverage, and flatness. LeanSearch's flat_and_surjective_iff_faithfullyFlat_of_isAffine is not an existence theorem for normal group quotients. LeanFinder's affine-scheme colimits and abstract group pushouts do not assert the represented fppf group pushout. The log and item retain the exact queries actually run. Historical searches in the repository node are also retained, not claimed as newly run by ND.

## Not duplicates

No new nodes. Reused lem-sfb-affine-normal-quotient-geometry (general normal affine quotient) and lem-sfb-faithfully-flat-group-quotient-universal (factorization for an existing quotient); neither is the present extension-pushout lemma. The blueprint pushout-monicity node is about arbitrary sheaves and gives no affine representability, so it is not an attachment for this item.

## Review by ND

I read Milne iAG2017 Proposition 5.18, printed pp.102–103, Theorem 5.13, printed pp.100–101, and Proposition 14.48 with its displayed pushout row, printed pp.295–296. Proposition 5.18 works for arbitrary affine algebraic groups over any field and supplies the exact normal quotient input through the existing reviewed node. I also read Stacks Tag 01QO (morphisms-lemma-closed-immersion) and Tag 023Q (descent-lemma-fpqc-universal-effective-epimorphisms) in their local TeX sources. No SGA is used.

Step 1: I opened the statements of the affine-product formula, the affine criterion for closed immersions, Ga, subgroup schemes and finite type. The product has coordinate algebra k[B][T]. Because i-star is surjective, adjoining T and sending it to minus phi-star(T) still gives a surjection. The image is N itself and is normal because every algebra-valued group G(R) is abelian. These are direct coordinate/definition calculations, not a hidden graph-closedness lemma.

Step 2: I opened lem-sfb-affine-normal-quotient-geometry and checked its statement, not its proof: the exact sheaf quotient in this item, finite-type affine representative, scheme kernel, and faithfully flat finitely presented quotient map all appear there. J is closed, finite type and normal by step 1. Commutativity is checked after local lifts and descends in the represented sheaf. No hypothesis of smoothness is used.

Step 3: I read the factorization node. Its source and target must be affine finite type, its quotient map must be faithfully flat, and the restriction to the scheme kernel must be zero. Those hold for rho:G->E, target Q, and q composed with the first projection; q i = 0 verifies the restriction on every algebra. The two triangle identities and b i = j phi follow from the explicit antidiagonal relation. The cited fully faithful Yoneda statement says precisely that natural maps between represented functors correspond to morphisms; this is the restricted version actually needed on affine tests.

Step 4: I opened lem-sc-kernel-subgroup, which gives K(R)=ker(q-prime(R)) and the closed embedding of K, rather than only a definition of a kernel. The affine closed-immersion criterion gives a quotient coordinate algebra, hence finite type. I checked j's injectivity using n=0 forced by injectivity of i(R), and local surjectivity onto K using x=i(n) and t+phi(n). On overlaps the unique additive coordinates agree, so representable descent (whose statement explicitly supplies unique gluing of morphisms into a scheme) applies to these fppf affine covers, which are fpqc. The represented Ga and K are affine, so fully faithful Yoneda supplies the scheme isomorphism. This proves a closed kernel embedding, including nonreduced test algebras.

Step 5: I reread both general group-quotient statements. K is a closed normal subgroup of the affine finite-type E. The universal-property lemma applies three times, with exactly the kernels N, K, J already proved. The written identities show vu=1 and uv=1: the second uses p rho(x,t)=p b(x), since p j=0. This proves q-prime is an isomorphism after the faithfully flat finitely presented map p; it avoids any unquoted descent-of-flatness fact. The exactness and j identification then follow from step 4.

Step 6: I read the sheafification definition's actual universal property. For an arbitrary commutative sheaf H, f(x)+g(t) is constant on each J orbit because f i = g phi. Thus it is already a natural map on the specified orbit presheaf, so its unique extension to the sheafification E is justified by that cited statement. This also proves uniqueness and the pushout property among represented sheaves without restricting targets to affine groups.

I checked delivery-errors B through E against the written files. No statement-only nodes are needed, no new duplicates or relabelled clauses occur, and no unquoted non-elementary lemma is hidden. Every proof use has a verbatim quotation checked against its node statement. The largest step is 905 characters, below the long-step threshold. Boundary checks: if N=0 the construction is B times Ga; if Q=0 it is Ga and b=phi; if phi=0 it is Q times Ga; if B=N=Ga and phi=id the quotient coordinate is x+t. In characteristic two the displayed minus equals plus and the relation and t+phi(n) calculation remain correct. None of these checks assumes reducedness; the proof uses all commutative algebras, so infinitesimal kernels are included.

## Unfinished work

No mathematical part remains. Server dry run and push results are recorded below when they finish.
