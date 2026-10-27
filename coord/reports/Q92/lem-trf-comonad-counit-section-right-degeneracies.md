## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-comonad-counit-section-right-degeneracies.json`: split the item into five elementary calculations; retained its statement and sole statement dependency, `def-trf-comonad-standard-resolution`. Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: one verbatim quotation from that definition node for each of the five steps.
- `report.md`: this report and signed review.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. Naturality of a supplied natural transformation and preservation of composition by a functor are definitions, so their two-line applications are proof steps, not auxiliary nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for comonads, extra degeneracies, and counit-section terminology. The relevant hits concern Cech contractions or unrelated sheaf counits; none states this item. Read `lean/Sheaf/CategoryTheory/ComonadStandardResolution.lean`: it supplies only the resolution predicate, not the result. Its resolutionPower and the transported operator formulas agree with the definition node.

## Sources and blueprint

Read `literature/stacks-project/simplicial.tex`, Example 0G5M (`example-godement`, lines 6193 onward), Lemma 0G5N (`lemma-godement`), and Lemma 08ND (`lemma-standard-simplicial-homotopy`, lines 6729 onward), including the second homotopy equivalence and its section given by the right-whiskered unit. Also read Lemma `lemma-godement-section` to distinguish a simplicial section from the extra-degeneracy identities under consideration. The Stacks proof treats the adjunction case; the proof here is explicitly agent-written at the generality of an arbitrary counit section. No missing document is needed; WANTED: none.

Read the chapter/unit records `sec-trace-formula` and `sk-i-curve-zero`, and the current latest blueprint's corresponding section, unit, and locality statement/proof. The inherited provenance is the long auxiliary chain through cotangent-resolution coherence under locality. The latest locality proof itself contains no comonad lemma; no claim is made that this generic auxiliary is verbatim in that blueprint. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality`; searches `comonad` and `extra degenerac` both returned zero blueprint nodes. Retained the item's already precise inherited `blueprint.from.place`, and filled `same_as` and the split report's blueprint explanation.

## Searches reused

The interrupted run left only `searches.jsonl`; it had not written an item or report or started delivery. Read all six logged searches and their candidate results rather than repeating them. The two LeanFinder phrasings query both a counit section without coassociativity and right insertion natural in section-preserving maps. LeanSearch asks for contraction of the comonad bar resolution; Loogle searches `"Comonad", "counit"`. The two logged grep patterns search AlgebraicTopology and CategoryTheory/Monad. Added exactly these six executed queries to the item's existing search records, preserving the older records.

Read Mathlib `AlgebraicTopology/ExtraDegeneracy.lean`, especially the structure fields (77 onward): those prescribe a left extra degeneracy and do not construct our right insertion. Read `CategoryTheory/Monad/Basic.lean` for counit and comultiplication naturality: each is a defining square, not this entire family of identities. Read `CategoryTheory/Monad/Algebra.lean` (Coalgebra, 262 onward): it assumes an extra coassociativity law. Read `CategoryTheory/Monad/Equalizer.lean` (CofreeEqualizer maps, 49 onward): equalizer arrows are not the required simplicial operators. None discharges the entire item in one line, so this is a split, not a Mathlib leaf.

DAG searches for 08ND, 08NC, counit-section terminology and right extra degeneracies found the existing standard-resolution definition, left-adjunction-image extra degeneracies, simplicial reversal, face/mixed identities and counit augmentation nodes. Read the statements of those relevant candidates. The left extra-degeneracy node is about U applied to an adjunction resolution, while ours evaluates a comonad resolution at an arbitrary object with a counit section. Reversal assumes exactly the right identities that this item must establish, so cannot establish them. The face/mixed identity nodes concern the ordinary simplicial identities, not interaction with v. None is used as an unjustified substitute. No new candidate id is created, hence there are no new-vs-existing duplicate pairs.

## What was wrong or unfinished

The imported item had no proof. Its statement is correctly typed with functional-order composition and is unchanged. No source error or statement dispute was found. Removed no preexisting dependencies; introduced no Lean code, compilation, new objects or coassociativity hypothesis. Nothing remains unfinished in this one-level split.

## Review by Q92

I read the supplied standard-resolution node's full statement alongside Stacks Example 0G5M. It explicitly defines e and c as natural transformations, prescribes d_i and s_i counted from the left, sets the augmentation in degree zero to e, and defines powers starting at the identity. Those are exactly the facts used; no existence theorem for a standard resolution is needed because B is supplied. Every cited step uses this same definition node, and every citation file quote is a literal substring of its statement.

Step 1 unfolds its face formula and p_0=e_b. The rightmost face on W_{n+1} is T^{n+1}(e_b), so applying the functor T^{n+1} to the stated equation e_b v=1 proves the terminal-face identity. The n=-1 augmentation equation is the original hypothesis. Regrouping powers is just expansion of the recursive definition, with induction on the outer exponent; no structural comparison theorem is hidden.

Step 2 uses the defining naturality square of e at the actual arrow v:b -> Tb. This gives e_{Tb} T(v)=v e_b and therefore the required d_0 t_0 boundary. It does not assume e is invertible or v is a coalgebra structure.

Step 3 uses naturality of that same e at T^{n+1-i}(v). I checked both its domain and codomain and the range i<=n+1, so this exponent is nonnegative including the last allowed i. Applying T^i gives d_i^{n+2} t_{n+1}=t_n d_i^{n+1}, with every superscript identifying the correct source degree. This is one defining square, not a non-elementary theorem needing a node.

Step 4 instead applies the defining naturality square of c at T^{n-i}(v). Its left side becomes s_i^{n+1} t_n and right side t_{n+1} s_i^n. The range i<=n ensures a nonnegative exponent. Crucially it uses c's naturality only: neither c_b v=T(v)v nor a compatibility between v and c enters. The available Coalgebra result would add that hypothesis and was correctly rejected.

Step 5 applies T^{n+1} to T(f)v=v' f. Functoriality yields exactly the two required degree maps and their commuting square; degree -1 is the premise. The definition node supplies the functor T and its iterates. No naturality in arbitrary f is claimed: section preservation is kept as a hypothesis.

I tested n=0 explicitly: d_1^1 T(v)=T(e_b v)=1, d_0^1 T(v)=v e_b, the two faces in step 3 reduce respectively to naturality at T(v) and T of naturality at v, and the sole degeneracy relation is c_{Tb}T(v)=T^2(v)c_b. The endpoint i=n+1 in step 3 and i=n in step 4 use the arrow v itself before applying an outer power, so there is no missing boundary case. For T=id with identity structure all displayed equations force v=id and hold. To test a section that actually fails the coalgebra law, take the function comonad T(X)=X^M for the two-element group M={1,g}, with e evaluation at 1 and c(h)(a)(b)=h(ab). On X={0,1}, set v(x)(1)=x and v(x)(g)=0. Then e v=id, but at x=1 and (g,g), c v has value 1 whereas T(v)v has value 0. The displayed naturality-square proofs still apply, confirming that no coalgebra law was silently required.

Against delivery-errors B--E: there are no new nodes and hence no statement-only, hollow, TeX, or duplicate-node issue (B); all five citations are checked against the definition's actual statement and naturality is expanded instead of silently imported (C); the steps carry the calculations rather than relocating clauses to new lemmas and do not cite a descendant or assume their conclusion (D); each exponent, source degree, boundary, and morphism hypothesis has been checked as above (E). The original arbitrary-section statement required no correction. Each step is well below 2000 characters; no long step conceals a separate lemma. During review I made source/target degrees explicit, spelled out the recursive regrouping of powers, and replaced an initially uninformative product-comonad example (whose sections do satisfy the coalgebra law) with the function-comonad example above, which really violates that law.
