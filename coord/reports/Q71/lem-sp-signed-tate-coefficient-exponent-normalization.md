# Stage-1 split: lem-sp-signed-tate-coefficient-exponent-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-signed-tate-coefficient-exponent-normalization.json`: statement node, now split into 12 proof steps; statement unchanged; no Mathlib match.
- `citations.json`: 23 entries, one for each step/node citation, checked as literal substrings of the cited statements.
- `report.md`: this report.

There are **0 new nodes and 0 Mathlib leaves**. Sandbox preparation scripts and the actual `searches.jsonl` are supporting work records, not additional DAG nodes.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag and theorem names and by the finite Tate/coefficient/exponent notions. The named normalized-family declarations occur in `lean/Sheaf/SecSmoothPurity/ScalarExtensionFunctor.lean`: `scalarExtensionTateMaps_existsUnique` (line 272), `scalarExtensionTateLevelIso_existsUnique` (line 424), and `scalarExtensionTateIso_exponent_naturality` (line 452). I read their statements, normalizations and proofs: each theorem still has `sorry`. The source's `WeilConjectures/EtaleCohomology/TateTwist/FiniteKummerLevel.lean` supplies a degree-one comparison for specified valuation-ring quotients; `Basic.lean` defines integer twist families, and `KummerClass.lean` treats geometric pullback of Kummer sequences. None states this item's simultaneous normalized coefficient and exponent families for arbitrary finite commutative rings. I therefore claim no finished project attachment.

## WANTED

None. The blueprint and the Stacks sources needed for this finite ordinary-sheaf argument are present.

## Corrections and earlier gaps

The imported item had no proof. Its statement is mathematically sound and remains verbatim unchanged, as do its statement dependencies and maintainer-owned fields. Its blueprint ancestor is `det-sp-scalar-extension-functor`; I retained its existing precise `from.place` and searched the whole imported blueprint, including `signed Tate` and `Kummer exponent`, finding no alternative statement of the full normalization theorem. The unit and chapter remain unchanged; this auxiliary item is not the unit's key statement.

The main point requiring care is the direction of the negative-degree map. A semilinear map cannot simply be dualized covariantly. I first prove that its ordinary scalar extension is invertible, then use the actual scalar-dual evaluation map and precompose with that inverse. I also write both negative-degree exponent-square evaluations. The local-basis argument uses generation over B, so it never silently assumes that f is surjective.

During self-review I removed a draft appeal to a merely described canonical tensor/dual comparison for a specific pure-tensor formula. The final proof uses the explicit evaluation statement `lem-sp-scalar-extension-dual-evaluation` and proves its local invertibility by its basis formula. This makes the normalization come from a statement that actually gives it, rather than from an auxiliary node's proof or an unspecified choice of isomorphism.

## Unfinished work

No unresolved mathematical step or new unsplit dependency was introduced. This is a natural-language stage-1 proof, not a Lean proof. No Lean file, compiler, Lake command, or build tool was used. The generic existing nodes below this item keep their existing project status.

## Searches and reuse

All five additional searches were run through the required `batch2/msearch.py` interface and are recorded with their actual query strings in `searches.jsonl` and the item. They comprise LeanSearch, Loogle, grep in Mathlib's AlgebraicGeometry directory, and two different LeanFinder phrasings. All services answered successfully. LeanSearch found ordinary tensor-power pairings, dual evaluation and `IsBaseChange.toDualBaseChange_tmul`; the first LeanFinder query found cyclotomic-character and Kummer-extension facts; the second found sheaf morphism extensionality and sheafification uniqueness. Loogle and the targeted grep found no hits. I read these results: none states the signed finite-root sheaf normalization plus exponent square, nor specializes to that whole item in one line. The inherited Q56 search records were preserved.

I searched the DAG and whole imported blueprint before deciding to add no nodes. In particular the existing scalar-extension dual-evaluation, tensor universal property, tensor restriction, and compatible-root statements already provide the independent inputs. The recursive formulas, dual inverse construction and evaluation calculations are proof steps, not new nodes restating clauses of the item.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The split reuses `det-def-sp-tate-twist-locally-free`, `lem-sfb-localized-site-tensor-restriction`, `lem-pc-sheaf-modules-tensor-closed`, `lem-pc-sites-sheaf-tensor-bilinear-universal`, `lem-sp-scalar-extension-dual-evaluation`, `def-pur-roots-of-unity-sheaf`, and `def-pur-sheaf-hom`.

## Review by Q71

I read the chapter record, the scalar-extension unit record and current `_section.md`, the item's full statement, paragraph (3) of `sk-def-sp-scalar-extension-functor.proof.md`, and the expanded Lean normalizations. I also read the finite clauses and proof of `sk-def-sp-tate-twist-locally-free`. For the sheaf operations I read Stacks `sites-modules.tex`: Tag 03EK (`section-tensor-product`, including its bilinear universal property), 03EL (`lemma-tensor-product-pullback`), 04TT (`section-internal-hom`), 03EM (`lemma-internal-hom`), 03EO (`lemma-internal-hom-adjoint-tensor`) and 03CY (`lemma-sheafification-presheaf-modules`), plus `sites.tex` Tag 04TQ (`lemma-glue-maps`). These are local primary sources already in the project. No SGA source is used. No new node needs an additional source.

For step 1 I opened the actual statements of the four cited nodes. The finite clauses of `det-def-sp-tate-twist-locally-free` give a single compatible-root cover, not just separate abstract trivializations. Its displayed generator map, tensor restriction from `lem-sfb-localized-site-tensor-restriction`, and the unitors explicitly asserted by `lem-pc-sheaf-modules-tensor-closed` identify the basis as zeta_n tensor 1. `def-pur-sheaf-hom` describes morphisms on all slices, so the dual basis is a basis of the internal Hom sheaf, not just of a group of global maps. The required hypotheses are precisely ell invertible on T and ell^n R=0, the latter following from n>=m. Taking E=Q_ell merely instantiates the unused integral-coefficient parameters of the finite clauses.

For steps 2 and 3 the cited `lem-pc-sites-sheaf-tensor-bilinear-universal` states the bijection for sheaf maps induced by pure tensors. I checked balancing over Z/ell^n in step 2 and over A in step 3, and explicitly regarded the target as an A-module through f. The section formulas commute with every restriction. Consequently these are sheaf maps determined by their pure-tensor prescriptions, with positive powers defined by a base case and an actual successor step.

For step 4 that same universal property constructs beta_d from a balanced map; multiplication by b proves B-linearity. Local inverses are written down for all d>=0, not inferred from flatness of B. `def-pur-sheaf-hom` explicitly says its morphism presheaf is a sheaf; hence it justifies gluing the inverse maps, whose overlap agreement follows by uniqueness of an inverse. This cites a theorem present in the node's statement, rather than assuming a theorem about a notion it merely defines.

For step 5 I checked the entire statement of `lem-sp-scalar-extension-dual-evaluation`: it gives exactly the map and formula st alpha(f(x)) on every slice. Its statement does not itself assert invertibility, so the step proves that assertion using the root bases and gluing, before using the inverse. The domain P_A is indeed locally free rank one by step 1, even when A or B has zero divisors. Composition with beta_d inverse has the correct covariant direction and yields the required equation, and extending this map is visibly an isomorphism.

Step 6 uses the tensor universal property only for uniqueness on degree-one tensors and successive powers. For negative degrees it evaluates on a B-basis contained in the image of the A-basis; the internal-Hom sheaf's separatedness makes the local equality global. This does not require the underlying semilinear map to be an epimorphism. Both cited statements say exactly these tensor-detection and sheaf-locality facts.

For step 7 `def-pur-roots-of-unity-sheaf` gives the actual power transition and its linearity after restricting the larger scalar ring. Clause (2) of `det-def-sp-tate-twist-locally-free` identifies the map induced by that transition as an isomorphism for every finite ring killed by ell^k. I checked k>=m, so this applies to each of A and B without a valuation-ring or residue-field restriction. The tensor universal property gives the prescribed map, rather than an arbitrary isomorphism between its endpoints.

Step 8 writes the negative transition as precomposition by the positive inverse, using precisely the slice internal-Hom definition, and proves both inverse and evaluation identities. Its positive uniqueness uses the cited tensor universal property. Step 9 checks identity and composition on the actual root power maps and gives the inverse-composition calculation in negative degree; its three cited nodes supply the root, tensor and Hom interpretations, while the displayed arithmetic is elementary. Step 10 gives the identical degree-one tensor value for both paths and an explicit induction for positive powers. Step 11 evaluates both negative paths on exactly the same positive image y; its two displayed equalities prove the asserted compatibility, and the Hom sheaf cited there detects equality after the root cover. Step 12 computes both scalar-extended paths on x tensor b, applies the square already proved, and uses the tensor universal property. Thus none of these steps hides a new compatibility lemma.

I tested the statement and proof at r=0, r=1, r=-1, n=k, k=m and n=k=j. The identity and composition formulas reduce correctly to exponent one or to composition of inverse maps. I also tested the empty base, B=0, and A=0 (then a unital map forces B=0): the trivializations and formulas remain isomorphisms of zero sheaves. As a non-flat case, Z/ell^2 -> Z/ell satisfies the argument, since local invertibility concerns rank-one scalar extensions, not exactness of tensor on arbitrary modules. As a non-surjective case, F_ell -> F_ell[epsilon]/(epsilon^2) confirms why a B-basis, rather than surjectivity, is used for negative uniqueness. No nontrivial-ring, flatness, connectedness or finite-type hypothesis was added.

I checked delivery-errors B1-B10: no new nodes need schema or leaf claims, the item introduces its objects, TeX is written once, the source tags and labels were read, actual searches are logged, and no incomplete Lean declaration is attached. For C1-C8, every non-elementary input is in a cited statement, citation quotes are literal, and off-unit generic tools are declared only in `split_report.tool_uses`. The compatible-root result supplies the finite local models; tensor restriction, unitors and the bilinear universal property are generic tools absent from this unit's own construction. No unit route was replaced. For D1-D5 the argument remains in the item's steps, with no new node carrying an item clause; both inductions have a base and successor. For E1-E7 I checked the hypotheses and edge cases above, the direction of the dual maps, and the actual Kummer exponents. No source error or statement dispute was found. Every step is under 2000 characters (the largest is 910), so no long-step lemma is concealed.

The server-side `srvcheck.py ... check_dag` passed without a finding introduced by this item. The server-side `review_split` passed with zero new nodes and the declared generic tool uses; it notes that the parent unit has no realization recorded yet, which this non-key item is not authorized to fill. The required full delivery dry run is the next validation.
