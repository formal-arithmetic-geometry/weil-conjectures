# Worker report: lem-coef-connected-tate-line-endomorphisms

## Files written

- `dag/nodes/sec-six-functors/lem-coef-connected-tate-line-endomorphisms.json`: statement, split; no new nodes, no new Mathlib leaves.
- `citations.json`: verbatim portions of every cited statement, indexed by proof step.
- `searches.jsonl`: retained the four earlier Q98 searches; their actual logged results have now also been added to the item's inherited search records. No searches were invented or repeated.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id and for connected Tate lines, scalar endomorphisms and Tate endomorphisms found no project declaration stating this item. General field-valued Schur lemmas do not apply to its arbitrary coefficient algebra.

## WANTED

None.

## What was wrong or incomplete

The repository item is still unsplit and has no proof; its statement agrees with the existing sandbox item. I retained the earlier sandbox split, citations, report content and logged searches, then tightened the argument and corrected an attribution in that report. In both the archived master parent and the current main-20261015 parent (now under `sec-smooth-purity/sk-lem-sp-tower/`, with a separate `.proof.md`), the paragraph beginning “The Tate rank-one object” motivates this item but does not contain the claimed connected-scalar proof. This proof is therefore explicitly agent-written. Its substantive external inputs are existing DAG statements, not a supposed scalar argument in the parent. No statement correction or route change is needed.

The existing `lem-pur-lisse-rank-one-aut` is related but concerns ordinary small-pro-etale sheaves over the finite stage A_{E,n} on separated finite-type schemes. It neither covers arbitrary commutative Z/N-algebras nor the shifted derived setting of this item; I did not apply it with missing hypotheses. The local-basis calculation here is a few-line consequence of module-line trivializations and the sheaf axiom, so it is written in the proof rather than made a new node.

## What I could not finish

Nothing remains in the mathematical stage-1 split. Delivery validation and push are performed through the required delivery tool.

## Review by Q98

I resumed the pre-existing sandbox by starting its required dry run before making repairs. I compared its item with the current shared item, read the chapter and unit records, the archived master parent, and the main-20261015 statement and separate proof. The parent places remain motivation for the extracted item; they do not justify attributing this new proof to a document. I also read the relevant Stacks text: `derived.tex`, Tag 06XS (`lemma-negative-exts`, part (2)); `etale-cohomology.tex`, Tag 03P5 (`remark-constant-locally-constant-maps`); and the internal-Hom section of `sites-modules.tex`, Tag 04TT. No SGA source is used. There are no new nodes requiring further source reviews.

Step 1 cites `lem-asd-etale-finite-twist-pullback` precisely for the locally free rank-one clause. I opened its statement and checked that it permits arbitrary commutative rings, not just finite rings: NB=0 follows from the Z/N-algebra structure, and invertibility on Y follows from its k-scheme structure. The nonnegative integer r is within its range. The Mathlib leaf `lem-weil-pbc-derived-single-fully-faithful` says exactly that ordinary abelian-category Hom maps bijectively to degree-zero derived Hom; I read both its statement and the source of Mathlib's full/faithful single-functor instances. The new explicit citation of `def-weil-abstract-derived-category` supplies the shift construction. Applying opposite integer shifts gives inverse correspondences and preserves scalar multiplication, without an extra geometric assumption. Finally, if f(e_i)=a_i e_i and e_j=u_ij e_i, linearity gives a_j u_ij=u_ij a_i. Commutativity and the inverse change of basis give a_j=a_i, and the sheaf axiom glues these coefficients. Conversely a section acts everywhere, so surjectivity and uniqueness are both accounted for. This calculation also proves ring compatibility; I have not cited a definition as a theorem supplying it.

Step 2 cites `lem-weil-pbc-constant-sheaf-sections-connected`. Its statement explicitly treats an arbitrary abelian group on the small etale site of any nonempty connected scheme, so it applies to (B,+) without quasi-compactness, noetherianity or finite-type assumptions. Its canonical constant-section map respects multiplication and 1 by the coefficient-sheaf construction; the local basis formula identifies these operations with composition and identity. Thus the displayed scalar map itself, not just some abstract identification, is bijective.

Step 3 cites the B-bilinear composition rule of `def-weil-linear-category`; functor B-linearity is also explicitly assumed in the item. Accordingly G(b id)=b id. Conjugation by the chosen isomorphism to B on Spec k preserves that scalar because composition is B-bilinear. Steps 1 and 2 specialize to Spec k with r=d=0, using the cited connected constant-section theorem there. Hence the inverse of G(v) is a scalar c, and the two inverse equations give bc=cb=1. This specialization uses a previously proved assertion, not the conclusion currently being established. Step 4 then checks directly that c id_L is the two-sided inverse of v; it is correctly elementary.

I checked the zero ring (the only map of the zero object is its identity), N=1 (which forces B=0), r=0 and arbitrary positive or negative shifts. The empty scheme is excluded as required for injectivity; disconnected schemes would allow different scalars on components, so connectedness is used exactly where needed. No field, reducedness, faithfulness or exactness hypothesis on B or G was inserted.

I searched the whole DAG and the blueprint index for endomorphisms, scalar endomorphisms, rank-one statements and connected constant sections, then opened the pertinent candidates. All non-elementary ingredients already exist: the Tate-line node, the derived-single Mathlib leaf, and the connected-section node. The last is declared as a generic off-unit tool in `split_report.tool_uses`; it supplies the connected etale site calculation without replacing the biduality route. I read the earlier `searches.jsonl` results and the pertinent Mathlib Schur/global-sections source: Schur assumes a field, simplicity and finite dimensionality, while the global-sections constructions do not prove this connected Tate-line result. The four real Q98 query/result records were retained and added to the node without fabricating searches. Every proof step's citations have a verbatim statement quote in `citations.json`, proof_deps is exactly their union, and all steps are shorter than 2000 characters. The local basis computation is elementary once rank-one local triviality is supplied and hides no additional comparison lemma.

On the continuation after the provider interruption, I rechecked the current shared item and every cited statement: the statement is unchanged and all six step/node quotes are still verbatim. The four step lengths are 1334, 589, 528 and 193 characters. I also opened `WeilConjectures/AlgebraicGeometry/Modules/Endomorphism.lean`: `AlgebraicGeometry.Scheme.Modules.exists_eq_smulHom` and `eq_of_smulHom_eq` concern invertible structure-sheaf modules on the Zariski site, so they do not attach this small-etale constant-coefficient derived assertion. The saved searches and proof remain intact. No prior delivery process was active; the required dry run was resumed as a single delivery invocation.
