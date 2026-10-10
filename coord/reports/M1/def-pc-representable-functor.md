Files written:

- `dag/nodes/sec-picard-framework/def-pc-representable-functor.json`: definition, no new Mathlib leaf; marked `split`.
- `citations.json`: empty because the definition has no proof steps.

Attachments:

- None. No sorry-free slopmaster2 declaration carries the exact project definition or the blueprint tag.

WANTED:

- None.

What was checked:

- The imported node statement was retained. Its scheme notion is supplied by the existing `def-pc-scheme`, its uniqueness reference is the existing `lem-pc-representable-unique`, and its explicit Categories Lemma 4.3.5/Tag 001P citation is supplied by the existing `lem-pc-yoneda`; no duplicate node was created.
- The blueprint search for `representable functor` and `001P` found the item itself and the existing Yoneda node, but no alternate blueprint node stating this definition.
- The source checkout was searched for the item id, its blueprint tag, and representability declarations. It contains generic `RepresentableBy` uses and no exact declaration for this project definition.

## Review by M1

I read the imported node and its blueprint source metadata, then checked every notion in the statement against the cited dependencies: `def-pc-scheme` supplies schemes and scheme morphisms, `lem-pc-representable-unique` is the stated uniqueness reference, and `lem-pc-yoneda` supplies the explicitly named Categories Lemma 4.3.5/Tag 001P. I also made Categories Lemma 4.3.5 explicit in the node's external source metadata so preflight can verify the citation. There are no proof steps, so `citations.json` correctly contains no entries. I searched the full DAG for the item, its Stacks tag, and the key words; the Yoneda node states the cited lemma rather than this definition and therefore is not a duplicate. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the hits were generic `RepresentableBy`/`IsRepresentable` declarations (or unavailable services), not an exact project-level declaration. I checked the small conceptual cases implicit in the definition: for `F = h_X`, representability is witnessed by `X`; an arbitrary natural isomorphism `F ≅ h_P` is exactly the stated representability condition. The dry run's citation check led to the added `lem-pc-yoneda` dependency and explicit source entry.

What could not be finished:

- Nothing; the dry-run verification is the remaining check.

## Second reading by M1

- Item statement: checked against Schemes, Definition 26.15.1 (Tag 01JG) in `schemes.tex`, lines 2764--2796; the functor-of-points and representability clauses agree hypothesis by hypothesis, including the base scheme specialization.
- New nodes: none; the delivered file is the item definition itself, so there are no new-node statements or proof steps to audit.
- Dependencies: `def-pc-scheme` supplies schemes and morphisms, `lem-pc-representable-unique` supplies the uniqueness reference, and `lem-pc-yoneda` states Categories Lemma 4.3.5 (Tag 001P); each dependency says exactly what the definition cites.
- Edge cases: the zero/empty scheme gives its ordinary empty Hom functor, a field base is a scheme base, and the definition is vacuous for any functor only when an actual representing scheme and natural isomorphism are supplied; no additional hypotheses are introduced.
- Blueprint and source metadata: retained the required null provenance for this imported blueprint item, set its `same_as` list to empty, and added the missing Stacks definition source tag `01JG` alongside the existing Yoneda citation.
- Delivery checks: the dry run passed preflight after these repairs.
