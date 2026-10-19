# Q100 — lem-sfb-proper-open-tower-derived-unit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-tower-derived-unit.json`: statement, split; no Mathlib match. Ten explicit proof steps, unchanged statement and statement dependencies, complete proof dependencies, blueprint provenance, and declared tool uses.
- No new nodes; no new Mathlib leaves.
- `citations.json`: 21 literal excerpts, one for each step/node citation.
- `searches.jsonl`: search-command log; the item's prior searches are retained and the six searches run for this delivery are appended to its record.

## Attachments

None. Searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and for proper/open and derived-unit terminology. Read the unbounded generic `RightDerivedFunctor/Comp.lean` and the étale compact-support comparison files, including `LowerShriekIndependenceUnbounded.lean` and `LowerShriekFormalismComparison.lean`. The former gives general composition machinery; the latter includes bounded-below adjunction-unit comparisons and a still unfinished unbounded refinement isomorphism. None states every clause of this chain-level tower assertion. Generic derived composition is not an attachment for the explicit augmentation homotopy and choice-independence clauses.

## WANTED

None. All sources used are present locally. No SGA route is used.

## Findings and changes

The item was unsplit, with no proof. Its statement is coherent and is retained verbatim; no STATEMENT-DISPUTED correction is needed. The closest Stacks source is the resolution formula in more-etale.tex Tag 0F7B, `lemma-shriek-proper-and-open`, together with the tower construction of Tag 0F7J, `lemma-shriek-composition`. The horizontal and vertical composition proofs between those lemmas demonstrate the resolution method. The unit, lifting, and change-of-resolution equations are written out here rather than attributed as a verbatim theorem of Stacks; `proof_origin.by` is therefore `agent`.

The proof avoids treating nonexact composites such as `s_* i_!` as functors on arbitrary derived inputs. The source is the stated localized termwise complex, and all applications of such composites are to actual chain maps or homotopies. The only preservation of quasi-isomorphisms used for open extension is the existing exactness theorem. For direct images we use exactness of their constant-coefficient *left adjoints* to preserve K-injectives, not exactness of direct image.

## Existing-node and blueprint searches

Read all statement-dependency nodes that supply comparison data and all proof-cited node statements. Searched the whole DAG for K-injectives and right-derived units, and used `tools/blueprint_refs.py search` for `derived unit`, `K-injective`, `proper/open`, and `resolution paths`. The existing Hom-to-K-injective bijection supplies both the lift and every resolution comparison, so a separate lifting node would be redundant. The proper/open node supplies Gamma's representative map, not the present augmented tower calculation. No new node was needed. `blueprint_refs.py ancestor` confirms `sk-lem-geo-affine-local`; the split realizes proof (2)'s last Hom equality through the 0F7J composition identification, via the recorded parent `lem-sfb-quasifinite-compact-support-exact`.

Mathlib searches were run only through `msearch.py`. Read all returned hits and read `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean` at lines 105–135 and 155–215. `rightDerivedNatTrans_comp` is natural-transformation functoriality; `totalRightDerivedUnit` assumes the right-derived functor and defines its unit. Neither gives the geometric square, the K-injective tower, or the explicit two augmented maps. The first Loogle query rejected the abbreviated identifier; this is recorded as a rejected query, and the corrected quoted-name query returned the actual declarations. The two LeanFinder phrasings returned objectwise injective resolutions, structure-sheaf pushforward identities, or unrelated gluing. LeanSearch likewise returned general/objectwise machinery. None supplies all the item in one specialization.

## Not duplicates

No new nodes. The lift is an application of `lem-weil-pbc-kinjective-hom-derived`, and the two-line unit formula is an elementary naturality calculation using `def-sfb-right-derived-functor`; neither was promoted to a redundant node.

## Review by Q100

I read the item against the unit and chapter records, the current blueprint unit text, Stacks 0F7B and 0F7J in more-etale.tex, 070I (`lemma-K-injective`), 070K (`lemma-enough-K-injectives-implies`), 070Y (`lemma-K-injective-defined`), and 08BJ (`lemma-adjoint-preserve-K-injectives`) in derived.tex, 03DJ (`lemma-extension-by-zero-exact`) and 04JC (`lemma-flat-pullback-exact`) in sites-modules.tex, and 0D6E (`lemma-derived-pushforward-composition`) in sites-cohomology.tex. The last tag states composition through derived adjoints; its explicit normalization is supplied by the existing composition node's statement. I checked that normalization rather than inferring it from a definition of direct image. There are no new-node statements to audit.

1. Step 1 uses exactly the constant-module inverse-image node's clause (3): exact, additive, and left adjoint to direct image. The right-adjoint-preserves-K-injectives statement then applies to q, p, and s. This establishes the additional K-injective targets needed later, including s_*p_*M. Constant coefficients are essential to this application; an arbitrary nonflat ringed-topos pullback would not suffice.
2. Step 2 uses the open-composition node for a_! = b_!j_! and the extension-exactness node's explicit preservation of quasi-isomorphisms. Composing b_!u with v and reading the definition of resolution proves the claim. No new lemma is hidden here.
3. Step 3 uses the Hom bijection with K-injective target p_*M. The derived-category definition supplies invertibility of Qw. Taking Qc(Qw)^{-1} both constructs ell and proves uniqueness after precomposition with w; degreewise injectivity of w is unnecessary.
4. Step 4 uses the proper-support node's section-preserving naturality, whose statement really gives natural, linear identifications, and direct-image additivity from the inverse-image/adjunction node. The explicit homotopy is s_*h precomposed with s_*i_!q_*u. This proves the displayed assertion already in the homotopy category, not merely after deriving s_*.
5. Step 5 uses the total-derived definition's natural unit and invertibility on K-injectives, with the compact-support definition's unbounded interpretation. Cancelling eta_T in its naturality equation is the entire argument for the resolution-unit formula; no composition theorem is smuggled into it.
6. Step 6 uses the proper/open node's exact displayed representative i_!q_*I -> p_*M and the compact-support definition's explicit action on maps of K-injective models. The square is commutative, proper/open, and between Noetherian schemes with finite A as required; it need not be Cartesian. L and p_*M meet the K-injectivity conditions for applying Rs_* by their actual representatives.
7. Step 7 uses the support-composition identification and both specified composition comparisons. The direct-image node's normalization with the identity resolution of p_*M gives the identity at QM; the written naturality equation along Qt then gives the comparison at Q(a_!J). This checks the prescribed comparison, rather than merely finding some isomorphism of outputs.
8. Step 8 again uses the Hom bijection, now with targets I', M', and L'. The sources of the inverses are u, v, and w, all stipulated quasi-isomorphisms. This constructs the three augmented comparison maps in the homotopy categories and specifies their unique classes, without requiring strict degreewise commutation.
9. Step 9 substitutes these three equations and the proper-support naturality equation. It cancels Qw only after noting that the target p_*M' is K-injective, using the cited Hom bijection. The displayed equation proves the naturality of ell; the two equations for alpha and beta give beta t = t'a_!f for the other path.
10. Step 10 uses extension-exactness to obtain the quasi-isomorphism beta. For gamma it instead uses that alpha is a homotopy equivalence between K-injectives: q_* need not preserve arbitrary quasi-isomorphisms. The Hom node explicitly says such K-injective quasi-isomorphisms are homotopy equivalences. Additive functors preserve those homotopy equations. Uniqueness over the augmentations makes the three-choice cocycle automatic and fixes the source complex. Thus choice-independence and naturality use the same comparisons actually constructed in steps 8–9.

I checked the small and limiting cases: zero complexes (all Hom classes vanish), empty open immersions, identity open/proper maps, nonmonomorphic resolution maps, and genuinely unbounded complexes. The argument requires neither boundedness nor constructibility nor invertibility of the coefficient-ring order. Identity choices reduce the augmentation equations to identities; a replacement of J is allowed through its homotopy equivalence, not through an unjustified descent of the termwise source. The zero ring also causes no issue. No target is changed.

I corrected one potential omission while checking step 7: the identity normalization at M must be related to a_!J using the explicit naturality equation along t; that equation is now included. I also checked every cited statement against its literal excerpt in citations.json. Every non-elementary input has a cited node, no new statement repeats a clause of the item, and every proof step is shorter than 2000 characters. The off-unit citations are declared generic tool uses serving the fixed 0F7J route.

## Unfinished work

None for this one-level split. The existing unsplit dependencies remain their own stage-1 items. No Lean was written or compiled.
