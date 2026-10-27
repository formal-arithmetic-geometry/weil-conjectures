# Q125: lem-pur-tensor-mate-invertible-input

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-tensor-mate-invertible-input.json: statement, now split into six proof steps; no Mathlib match for the item.
- citations.json: twelve step/node records, quoting each cited statement verbatim.
- searches.jsonl: actual results of the prescribed search wrapper; retained for delivery validation.

No new nodes and no new Mathlib leaves. Statement, statement dependencies, prior searches, source, creation record, and blueprint ancestry retained. The new proof uses the existing Mathlib leaf lem-sf-quasi-inverse-hom-bijection.

## Attachments

None. Searches of WeilConjectures for the blueprint tag and tensor/invertibility terminology found no project declaration covering this finite-coefficient constructible pro-etale statement with every hypothesis and its naturality clause. CategoryTheory.Adjunction.isIso_projectionTensorMap_of_isInvertible (WeilConjectures/CategoryTheory/Adjunction/ProjectionTensorMap.lean:125) is a useful formal theorem, but does not itself instantiate the specified geometric categories, adjunction, projection map, or symmetry convention. It is not claimed as an attachment of this item. Its general formal proof motivated checking an explicit Hom-test proof here.

## WANTED

None.

## Problems found

No statement dispute. The imported item had an empty proof; the source's final sentence does not justify why the tensor mate on an invertible input needs no smoothness hypothesis. The split supplies that argument without invoking purity, exceptional base change, or an unrestricted ambient pro-etale right adjoint. No coefficient category is changed.

## Unfinished work

None in this one-level split. The cited nodes retain their own existing statuses.

## Searches and reuse

Read the chapter sec-smooth-purity, unit sk-prop-cohsm, the current main-20261015 unit text, and lem-pur-co-smooth-composition.proof.md. Searched the entire DAG by tensor-mate, invertible-input, projection/dualizability, quasi-inverse and Yoneda terms; searched blueprint_refs for invertible input and tensor map and checked the ancestor. Existing geometric sibling nodes do not supply the desired proof, and the existing formal tensor-equivalence Mathlib leaf does. All newly run Mathlib queries are recorded exactly from searches.jsonl, including both LeanFinder phrasings, LeanSearch, Loogle and the source grep. The interrupted provider turn had completed and logged the LeanFinder calls; their records were inspected and reused. Search results concern reflective monoidal categories, ordinary modules, or general mate identities, rather than an exact theorem for this geometric canonical map. The grep returned the elementary Yoneda Hom test, whose two-line proof is included explicitly instead of creating a node.

## Not duplicates

No new nodes. In particular, no new abstraction restates this item, and no new Yoneda or tensor-cancellation node duplicates an existing result.

## Review by Q125

I read the current source proof's final base-change sentence and the complement defining (G11) in the current unit. Those passages specify that the tensor map is the transpose of inverse projection followed by the exceptional counit. I also read Stacks categories.tex, Tag 0FFM, label categories-lemma-invertible, including its proof that a two-sided inverse object makes tensoring an equivalence. The proof here is marked agent-written because the blueprint sentence does not give this Hom calculation. There are no new-node sources to audit. The abstract project theorem in ProjectionTensorMap.lean was read as additional corroboration, and is not substituted for a cited node statement.

For step 1 I opened the complete statements of lem-sf-tensor-ctf, lem-pur-all-stage-ctf-pullback-unit, lem-pur-derived-pullback-tensor-iso and def-weil-exceptional-inverse-image. Tensor closure is clause (ii) of the first; the second explicitly allows schemes not separated over k and supplies both the restricted pullback and unit. The third supplies the natural tensor comparison. Applying it to each of the two inverse equations gives both inverse equations for Q. The exceptional definition supplies the transported constructible adjunction and its finite-Tor restriction, not an ambient adjoint. The constructions of the quasi-inverse tensor comparisons use just associators, evaluations and unitors and are written in the step.

For step 2 the complete statement of lem-sf-quasi-inverse-hom-bijection asserts exactly bijectivity of the functor's actual map on Hom sets from arbitrary quasi-inverse natural isomorphisms. It does not require the chosen inverse-factor evaluations to satisfy triangle identities. The projection statement fix-prop-projection-formula supplies invertibility and naturality in both inputs on bounded constructible first inputs and finite-Tor second inputs. Here every test B is finite-Tor, hence bounded constructible, and P is finite-Tor by hypothesis. The finite coefficient and separated finite-type hypotheses match exactly. I checked the dependency closure of all geometric tool citations: none reaches this item.

For step 3 I read the exceptional definition and the full displayed transpose in def-pur-co-smoothness. The latter's formula starts with symmetry, then inverse projection, then the counit tensored with P and the left unitor. Thus its map is t after symmetry, with exactly the t constructed here. I use the definition of that map, never the condition that it is invertible. The Hom-set chain is a composition of already justified bijections with the adjunction; no representability theorem is hidden in it.

For step 4 I checked both sides of the projection naturality equation: each has source F(B tensor Q) and target F(omega) tensor P. Composing with the counit and left unitor gives the explicit transpose of t after f tensor identity. This establishes that the bijection is postcomposition by the specified arrow, which is the essential canonical-map requirement. The cited projection statement says natural in K and L, and the cited adjunction definition gives natural Hom bijections. This step uses neither an unnamed inverse mate lemma nor the proof of another DAG node.

Step 5 uses only earlier steps. For any A, B=A tensor Q' gives B tensor Q isomorphic to A, inside the same finite-Tor category by step 1. The two tests A=GP and A=omega tensor Q explicitly construct a two-sided inverse; I checked the composition directions. This elementary proof avoids an uncited application of Yoneda and creates no unnecessary node.

For step 6 I checked projection naturality in P and the counit transpose equation again. The displayed equality has source F(omega tensor Q) and target F(omega) tensor P-tilde. After the counit and naturality of the left unitor its transpose gives G(a)t=t-tilde(1 tensor H(a)). Symmetry naturality changes this into the statement's required naturality square. Thus naturality is proved for all morphisms between invertible objects, not merely for chosen inverse data or isomorphisms.

I checked sections B through E of delivery-errors against these files: there are no new nodes requiring independent statements or searches; all non-elementary ingredients are existing cited statements; each citation is copied verbatim into citations.json; elementary steps are explicit functor, adjunction, associator or two-test calculations; no argument is moved into a restatement node. Every step is under 2000 characters. Existing off-unit operation properties are declared as generic tools in split_report.tool_uses, without changing the unit route.

Small cases: for the identity morphism, F=G=H=id and the transpose is the unitor after symmetry, hence invertible as claimed. For P=the coefficient unit the argument reduces to the adjunction counit transpose and the unitors, independently of invertibility of omega. For empty T the derived category is the zero category and both Hom tests remain bijections; for empty U necessarily T is empty. Shifted units or rank-one local systems require no choice of a global trivialization: their two inverse equations suffice. Arbitrary inverse evaluations need not satisfy triangles because only the existing quasi-inverse Hom-bijection leaf is used. There is no assumption on invertibility of omega, smoothness, or a dualizing base-change map, and no assumption that U or T is absolutely separated.
