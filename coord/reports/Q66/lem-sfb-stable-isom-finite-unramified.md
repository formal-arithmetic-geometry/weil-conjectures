# Stage-1 report: lem-sfb-stable-isom-finite-unramified

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stable-isom-finite-unramified.json`: statement, split into eight steps; not a Mathlib leaf. The statement is unchanged. Added its existing unramified definition to `stmt_deps`.
- `citations.json`: one verbatim cited-statement entry for each step/node pair.
- No new DAG nodes and no new Mathlib leaves. Search logs and actual result files are retained in this sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag, stable curves, stable Isom and unramified Isom terminology. There is no declaration giving this statement. Ordinary isomorphisms of schemes being finite do not represent an Isom functor and are not attachments.

## Literature wanted

WANTED (inherited from the existing parameter node): Morrison, *GIT constructions of moduli spaces of stable curves*, arXiv:0810.2340, Section 3.3 pp.15--17, for `lem-sfb-ten-canonical-hilbert-parameter`. That existing node records its author exposition as read online but its local PDF as wanted. This delivery uses its full stated interface as a black box; it adds no new claim about Hilbert stability, quotient existence or projective coarse moduli.

## Findings and corrections

The original item is true and its statement is retained, including arbitrary test schemes and nontrivial automorphism groups. The source's properness theorem implies finite type, but adding new nodes separately asserting finite type and finite unramified diagonal would only repackage the item's clauses. Existing nodes instead give an actual short argument without creating any new node.

The important hypothesis issue is that `lem-sfb-stable-pointed-isom-finite` assumes its base is a finite-type scheme over a field. It cannot be applied directly to arbitrary T. I apply it only on S = J x_k J for the already existing ten-canonical parameter scheme, then pull back to a Zariski open cover where both families have projective frames. Scheme gluing extends representability and finiteness to arbitrary T. The universal embedded families are H-projective as required by that theorem, whereas the original families over T are only required to be projective-bundle morphisms. No projectivity convention is silently changed.

The finite type of the coarse space in `lem-sfb-unpointed-stable-coarse-projective` is not a proof that the stack is of finite type. I take only its explicitly stated smooth-stack assertion. Local finite type follows on a smooth atlas; quasi-compactness is proved universally on every affine base by the finite-type parameter J and projective frames. Thus the proof really proves the stack assertion independently of its coarse space.

The universal Isom scheme parametrizes all curve isomorphisms. The frames construct maps to J; their preservation is not imposed on Isom. Normality is not assumed: it is needed only for the separate generic-extension conclusion of the pointed-Isom theorem, which is not used here.

`blueprint.from.place` already gives the precise main-20261015 paragraph (3) alteration/moduli prerequisite; it is retained. The ancestor command returns null through the historical creation chain, and the inherited null ancestor/via chain is retained. Searches of the full imported blueprint for `stable curve`, `stable unpointed` and `0E9C` give no duplicate. A broader isomorphism search gives unrelated category-theoretic and geometric comparisons. Existing stable pointed Isom and stable coarse-moduli nodes are reused, not recreated. No unit or chapter record is changed.

## Unfinished work

None for this one-level split. The existing cited nodes remain separate DAG tasks where applicable. No Lean was written, no compiler or build command was run, and no repository or launcher file was modified.

## Review by Q66

I read the item's actual Stacks source in `moduli-curves.tex`: 0E7A (`lemma-stable-curves-deligne-mumford`), 0E9A (`lemma-stable-separated`), 0E9B (`lemma-stable-quasi-compact`), and 0E9C (`theorem-stable-smooth-proper`). Their proofs separate the infinitesimal, uniqueness and boundedness inputs. I also read the linked DM-locus and vector-field arguments in that file, and `curves.tex`'s tricanonical and stable-vector-fields lemmas. The assembly here reuses the existing ten-canonical bounded parameter and the already split stronger pointed-Isom theorem; it is therefore marked agent-origin, rather than claiming to reproduce verbatim the Stacks tricanonical/properness proof. There are no new nodes whose sources need review.

For step 1 I opened the ten-canonical parameter node and checked that its statement really gives Z projective finite type, J locally closed, and the actual frame functor. I opened the finite-type-over-Noetherian, Noetherian-open-subscheme, quasi-compact-open-immersion finite-type and finite-type composition/base-change nodes: they give exactly the properties used. A field is Noetherian without a perfectness hypothesis. I added the closed-immersion definition explicitly when checking that J closed in V has affine quotient charts; the quotient is finitely generated even if its ideal has not been chosen finitely generated. This proves finite type, and does not assert finite presentation from that elementary quotient argument.

For step 2 I opened the stable-coarse theorem's statement and verified it explicitly says smooth Deligne--Mumford stack over every field, in the same moduli convention. I take its smoothness only. The smooth-morphism definition contains local finite presentation. The parameter theorem explicitly gives the projective-frame torsor and functoriality on arbitrary bases. For every affine B, the cited base-change theorem applies to J_B -> B regardless of whether B is Noetherian. Its quasi-compactness gives a finite subcover of the pullback of any open cover of the stack; surjectivity on geometric objects makes that cover a cover of the entire stack. This is why no smoothness assertion about J -> M, or properness of the coarse map, is smuggled into this step.

For step 3 I read the whole statement and proof of `lem-sfb-stable-pointed-isom-finite`. Its first conclusion, with n=0, is exactly the finite unramified Isom representation needed over the finite-type S. The fixed-projective-space embeddings of the universal curves are supplied by the parameter theorem, so the stronger H-projectivity convention in the cited theorem is met. Its representing functor is on all S-schemes and therefore commutes with further pullback. The separate normal-integral extension conclusion is not used. The product S is finite type by the two clauses of the cited scheme theorem.

For step 4 I checked the parameter theorem really states local freeness, arbitrary base change, Zariski local triviality of frames, and the natural groupoid equivalence. Taking intersections of the two trivializing covers suffices; their intersections need not be affine. The fibre-product definition gives the representing bijections. I opened both cited permanence nodes: finite and unramified are stable under every scheme base change, with no finite-type or Noetherian restriction on the new base. The local Isom scheme imposes no frame equality.

For step 5 I opened `lem-weil-pbc-glue-schemes` and checked every part of its input: the opens are the inverse images of the actual base intersections, the overlap maps are the unique maps representing the identity natural transformation of Isom, their restrictions obey the cocycle, and the triple-open inverse-image condition is exactly the triple intersection in T. The statement gives the glued scheme, its open cover and its specified intersections. The separate morphism-gluing node, whose statement I also read, gives I -> T. It is not necessary to take a false affine-intersection shortcut.

For step 6 the same morphism-gluing statement gives both the representing morphism into I and gluing of curve morphisms. Gluing the inverse maps as well proves that the result is an isomorphism. This spells out the sheaf property rather than citing a definition of a stack for a theorem it does not contain. Equality and naturality follow from uniqueness on the open covers.

For step 7 I opened the finite-local-on-target node; its clause (3) is precisely the arbitrary-open-cover test used. I read the unramified definition and the source's open-diagonal formulation (02G4/02GE). The proof writes out why the open diagonals cover and glue, so it does not take target-locality from the unramified-base-change node, which states only base change and restriction. Morphism gluing supplies the inverse to the diagonal on its open image. No flatness is inferred from unramifiedness.

For step 8 I opened the current full moduli-groupoids definition: the fibre groupoids and their 2-fibre products keep automorphisms, and include the compatibility equation on arrows. Unwinding this definition identifies each diagonal fibre with the discrete Isom functor, not with isomorphism classes of curves. Specializing the pair to (C,C) gives the inertia base change, so its finiteness follows from the already constructed finite scheme.

I checked B--E of `coord/delivery-errors.md` against these files. There are no new nodes to be elementary duplicates, clause restatements, unsearched leaves, or proof-bearing unsplit nodes. Every non-elementary input is an existing node, each quoted in `citations.json` from its actual statement. I checked recursively that none of the selected dependency nodes reaches this item, so the new edges introduce no cycle. Every proof step is below 2000 characters. Off-unit scheme tools are declared in `split_report.tool_uses` where required; they are generic gluing and finiteness facts, not a replacement for a unit route.

Small cases: empty T gives the empty representing scheme; if the curves are not geometrically isomorphic the relevant fibres are empty; for C=D the construction gives the full finite automorphism scheme, not a point. It works for g=2, reducible curves and self-nodes because these are included in the cited stable-family theorem. Arbitrary positive characteristic is allowed, including when an automorphism-group order is divisible by the characteristic: unramified does not mean a tame stabilizer, and no division by that order occurs. Disconnected, nonreduced, non-Noetherian and non-quasi-compact T are handled by the arbitrary cover and base-change arguments. The projective frames are chosen only locally, and never require triviality of the vector bundle on T.

## Not duplicates

No new nodes were created. The existing finite-type-base pointed-Isom result and ten-canonical parameter node are cited in place of duplicate constructions.
