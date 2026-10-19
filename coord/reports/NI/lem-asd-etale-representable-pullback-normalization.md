# Stage-1 report: lem-asd-etale-representable-pullback-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-asd-etale-representable-pullback-normalization.json`: statement item, now split into five proof steps; no Mathlib match for the full normalized comparison.
- `citations.json`: ten citations, with verbatim quotes from the cited statements.
- `searches.jsonl`: actual Mathlib queries logged by msearch.py; the inherited item searches are retained in the node.

No new nodes and no new Mathlib leaves. No unit, chapter, source, Lean file, shared repository or launcher file was changed. `write_split.py` is a sandbox-only artifact used to write the JSON.

## Attachments

None. Searched the project checkout under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, for representable pullback and Yoneda/upperStar terms, and read the project Yoneda source. No declaration supplies every clause of this item. The free abelian represented-sheaf equivalence in `SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/CohomologyPresheaf.lean` concerns a different coefficient category. It is not an attachment for the sheaf-of-sets comparison. Historical dependency-audit module paths for the algebraic-structures adjunction and representable-sheaf theorem are absent from this local checkout; no attachment claim is based on those audit records.

## WANTED

None. All mathematical sources needed here are available locally.

## What was wrong or incomplete

The imported item had a complete statement and no proof. Its statement is unchanged. The existing node `lem-galois-inverse-image-representable` proves existence of a natural isomorphism, but its statement does not characterize the specified adjunct on the identity. Citing its proof to obtain normalization would violate C3/C4. Instead this split reuses the smaller general evaluation and co-Yoneda leaves already used by that node, and computes the normalization directly.

The generic scheme-functor Yoneda node `lem-pc-yoneda` is not used: its statement is restricted to presheaves on all schemes over a base. The existing `lem-galois-yoneda-hom-bijection` explicitly covers every category and every presheaf, including the small etale categories required here. Its naturality clauses are also explicit.

The Mathlib searches found general sheaf adjunctions, scheme representability, and Yoneda infrastructure, rather than a declaration stating the normalized small-etale representable comparison. Read `Mathlib/CategoryTheory/Sites/Pullback.lean:55-88` and `Mathlib/CategoryTheory/Yoneda.lean:724-760`; these provide the ingredients rather than an exact or one-line specialization covering the item. The two leanfinder queries used different formulations, one for the scheme comparison and one for arbitrary continuous functors of sites. Loogle and LeanSearch were also tried. The search wrapper's single-file grep output labels its first field with the source line number; the printed hits were checked against the actual file, and are not claimed as declaration matches.

## Not duplicates

No new nodes were created. Whole-DAG title/statement searches, Stacks-tag searches (03Q1, 04D3), and blueprint_refs searches for Yoneda, representable and pullback were read to identify the existing tools. The nearby unnormalized representable comparison is reused at the level of its existing generic ingredients, not duplicated as a new node. No imported blueprint node states the complete normalized assertion, so `blueprint.same_as` remains empty.

## Review by NI

I read Stacks `etale-cohomology.tex`, Tag 03Q1 (`lemma-stalk-pullback`), especially part (4) and its displayed adjunction/Yoneda chain at lines 4700-4722. I also read `sites.tex`, Tag 04D3 (`lemma-pullback-representable-sheaf`, lines 2619-2628), and `categories.tex`, Tag 001P (`lemma-yoneda`, lines 541-566). The item follows the first source's proof; the normalization is the explicit identity-section calculation that identifies the particular map in the statement. There are no new nodes whose sources need separate validation.

Step 1 uses clause (1) of `lem-weil-pbc-etale-base-change-finite-limits`, which explicitly states that arbitrary scheme base change sends etale objects to etale objects and arrows to id-times-arrow. It therefore gives both the eligibility of P' for Yoneda and the identity/composition laws needed for beta. `lem-weil-pbc-small-etale-representable-presheaf-sheaf` explicitly makes both represented presheaves into sheaves, for any representing scheme over the base. The restriction equation for beta is written out. No etaleness of f is assumed or used.

Step 2 uses only clause (1) of `lem-weil-pbc-etale-inverse-image-algebraic-structures`, namely the sheaf-of-sets adjunction and the sectionwise description of direct image. The full-subcategory sentence of `def-weil-pbc-etale-sheaf-of-sets` licenses using presheaf Yoneda for sheaf morphisms. The general `lem-galois-yoneda-hom-bijection` gives evaluation at id_P, evaluation at id_P', and naturality in H. I opened and read each cited statement, and copied these clauses into citations.json. This avoids both a Yoneda-full-faithfulness citation in place of evaluation and a definition citation in place of a theorem.

Step 3 computes beta_P(id_P)=id_P' from Step 1's functor. By definition c is the adjunct of beta. The evaluation bijection in the cited general Yoneda statement sends id_B to that same section, so its injectivity proves Phi_B(c)=id_B. The composite adjunction/evaluation bijection also proves the claimed uniqueness, rather than merely asserting it. There is no presumption that the specified comparison is invertible at this point.

Step 4 cites `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`. I checked its complete statement: for arbitrary category objects A,B, it produces the isomorphism theta:B->A and specifically the formula Phi_H(u)=u composed with theta. Those are exactly the two facts used. Substitution u=c gives c composed with theta=id_B; composition with theta inverse proves that the specified c is theta inverse. This argument does not assume that the small-etale site or its sheaf category is a small colimit index category.

Step 5 uses the same base-change functor clause and the same sets adjunction. At every arrow a:W->P the two adjuncts are explicitly equal by b_f(t) composed with b_f(a)=b_f(t composed with a). Naturality of the adjunction in both variables gives the displayed square for c_P and c_Q. Thus the naturality clause is about the specified comparisons, with the correct source and target, rather than about an unspecified family of isomorphisms.

I checked the item statement's definition dependencies against the statement text: schemes, the small etale site, the fibre product, sheaves of sets, representable sheaves and the sets adjunction are all already named. The chapter/unit metadata and current blueprint paragraph 2 of `prop-asd-smooth-base-change` are preserved; this is the elementary representable infrastructure for the ordinary inverse-image and twist comparison, not a change of the smooth-purity route. The only non-Mathlib infrastructure statement is explicitly declared as a generic tool in split_report.tool_uses.

For B--E: there are no new statement-only nodes, no duplicate or clause-restating children, and no new definitions. All ten step citations have sufficiently long verbatim quotes. Every non-elementary input has a cited node; all proof dependencies are exactly the union of step uses. No proof step exceeds 2000 characters (lengths 559, 936, 708, 446, 706). In particular no hidden recognition lemma is proved inline: co-Yoneda recognition is an existing cited leaf. Empty X, empty P, identity f and non-etale f all satisfy the same argument; the empty object's identity and the Yoneda evaluations still exist, and no nonemptiness, Noetherian, finiteness or properness hypothesis is introduced. There is no statement dispute or source error. No compiler or Lake command was run.

## Unfinished work

None in the split. The required server dry run and delivery are the final mechanical checks.
