## Worker report

Files written: dag/nodes/sec-zeta-weil/lem-zl-condensed-finite-closed-model-lifts.json (statement; split, no Mathlib match). Supporting audit file: citations.json. No new nodes or Mathlib leaves.

Attachments: none. Searched the live read clone's lean/WeilConjectures by the exact blueprint tag, closed-model-lift terminology, and condensed/henselian terminology. No declaration states the item. The existing sorry declarations are not treated as finished proofs.

WANTED: none.

The statement is unchanged. Removed the unused direct statement dependency on the derived constant-module functor (the scalar realization definition already supplies it), and added the explicit definitions of weak etaleness, flatness, quasi-compact morphisms and pro-etale coverings. The empty proof is replaced by seven steps. No outstanding mathematical work in this one-level split; the cited unsplit projective calculus is a separate existing item.

The proof follows the finite-component paragraph of Hemo--Richarz--Scholbach, Theorem 4.13, with the refinement already built into this item's statement. It does not use that paragraph's claim that arbitrary closed subschemes of w-contractible schemes are w-contractible: the given W_a are w-contractible, and Corollary 4.4(2) applies to their actual henselian lifts. It also does not identify the models P_a for distinct indices. The finite closed cover is only used to obtain joint surjectivity and a finite affine covering family.

I read the current main-20261015 smooth-proper purity ancestor proof and the chapter/unit records. This auxiliary local-model argument stays under its inherited adic Hom-tensor and truncation route. The shared ring and affine-geometry lemmas in split_report.tool_uses are generic tools, unavailable as statements of the purity unit; no purity step is replaced.

Mathlib searches: ran the required leanfinder, leansearch, loogle and grep commands, plus a second semantic phrasing. Read all returned hits. The affine-limit compatibility and cover constructions do not involve the derived condensed-coefficient categories, henselian lisse restriction or prescribed perfect scalar models. Loogle and grep returned no hits. Every new search entry is copied from the actual searches.jsonl record; previous item searches are retained. No Mathlib match was claimed.

## Not duplicates

No new nodes. Whole-blueprint searches for “finite closed”, “henselian lisse”, “prescribed models” and “closed covering” returned no blueprint match. The closed-lift search located the existing adjunction infrastructure. DAG searches located the existing filteredness, reduction, henselianity, rigidity, scalar-projective calculus, ind-etale stability, faithfully-flat spectrum surjectivity and affine permanence nodes; these are reused instead of being recreated.

## Review by Q68

I read HRS Corollary 4.4 and its proof, Lemma 4.1's monoidal perfect-complex description, the pullback/locality statements, and Theorem 4.13 including its finite-component paragraph in the local PDF. I also read Bhatt--Scholze Definition 2.2.10, Lemma 2.2.12 and Lemmas 6.1.1--6.1.2 in the local PDF. For the covering details I read Stacks proetale.tex Tags 097P (lemma-lift-ind-etale) and 0989 (definition-fpqc-covering), morphisms.tex Tags 01S7 (lemma-affine-separated) and 01SH (lemma-morphism-affines-affine), and algebra.tex Tag 00HQ (lemma-ff-rings). There are no new nodes needing separate sources.

For step 1 I opened the five cited statements. The construction really gives a small diagram of finitely presented etale algebras; the filteredness node states filteredness of that diagram, the ind-etale definition is exactly a filtered colimit of these algebras, the reduction lemma specifies the map C/IC to Cbar, and the existing henselian lemma applies to this very colimit, not an arbitrary lift. Its hypotheses hold because Cbar_a is given ind-etale over A/I_a. No finiteness of I_a is assumed.

For step 2 I read the entire henselian lisse rigidity statement: it asserts both the equivalence of w-contractibility for a henselian pair and full faithfulness on dualizable objects. Thus it supplies exactly the two facts used, after step 1 identifies the closed fiber with the given W_a. This is not a general assertion about closed subschemes.

For step 3 I opened the locality and projective-calculus statements. The former explicitly treats every scheme morphism, preserves dualizable objects, and commutes with canonical scalar extension. The latter explicitly says that L_T(P) is dualizable for any perfect P on a w-contractible affine T, without flatness of the section ring over R. All those hypotheses are established here. This ensures that step 4 applies full faithfulness to both objects, not just K.

Step 4 uses only the full faithfulness clause of the rigidity statement and elementary category reasoning: lift alpha and its inverse by surjectivity on the two Hom sets, and use injectivity on endomorphisms to prove both composite identities. The same injectivity proves uniqueness. The prescribed reduction and canonical scalar identifications are retained, so the restriction really is the original alpha_a. No new categorical lemma is hidden in this step.

For step 5 I read ind-etale stability's explicit implication to weak etaleness, the definition of weak etaleness (which includes flatness), and the spectrum-surjectivity theorem for faithfully flat maps. The faithful-flat hypothesis is imposed on A/I_a to Cbar_a, exactly as required. Surjectivity lifts a point of X_a to W_a; the canonical reduction map places that point inside V_a. One does not incorrectly assert that V_a lies over X_a.

For step 6 I read affine permanence's clauses (3) and (4), the theorem that a morphism between affines is affine, and the local-ring definition of flatness. They yield affineness of the finite disjoint union and quasi-compactness of its map. Flatness is checked at a point in its open summand, whose local ring is unchanged. For step 7 the same affine-morphism theorem gives affine inverse images of every affine open U in X. Those finitely many affine opens cover U in image by step 5, exactly the covering definition's quantifiers. Thus the covering claim does not rely on a hidden general fpqc recognition lemma.

Edge cases: X empty and an empty index set; an empty summand W_a; I_a=0; I_a=A; zero ring A; repeated or overlapping closed pieces; nonreduced rings; non-finitely-generated ideals; zero perfect complexes; distinct P_a. The arguments impose none of the missing finiteness, noetherianity, connectedness or coefficient-flatness hypotheses. In the empty-index case X is forced empty, the empty affine coproduct has the required map, and the covering definition allows zero chosen affine opens. For Cbar=0 the henselian lift has C/IC=0 and a henselian ideal IC=C, forcing C=0 by uniqueness of idempotent lifts; there is no unwanted nonempty lift. No statement dispute was found.

I checked delivery-errors B--E: no new statement-only nodes, proof sketch masquerading as a statement, duplicate, clause-restatement, or invented Mathlib leaf; all non-elementary facts have explicit statement citations; no uses of another node's proof; and all 17 step/node pairs have verbatim statement quotes in citations.json. The proof has seven steps of at most 549 characters, so no long step hides an extracted lemma. The source's unsupported arbitrary-closed-subscheme shortcut is avoided using exactly the prescribed covers already present in the item's hypotheses.
