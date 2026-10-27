# Stage-1 delivery: lem-sfb-split-reductive-local-gauss-atlas

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-reductive-local-gauss-atlas.json: item, statement unchanged, split into five steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-split-root-data-weyl-lifts.json: new statement-only structural lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-root-product-open-cell.json: new statement-only relative multiplication-cell theorem; no Mathlib match.
- citations.json: verbatim statement quotations for each use in each item step.
- searches.jsonl: actual msearch.py query records, retained unaltered.

Two new nodes, zero Mathlib leaves. No Lean, repository files or launcher scripts were written, and no compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and reductive, Bruhat, Gauss and big-cell notions. Results were polynomial Gauss lemmas, linear algebra and Lie-algebra reductivity, not relative reductive group schemes. No sorry-free declaration states this item or either new structural input.

## Wanted literature

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, as literature/conrad-reductive-group-schemes.pdf, Section 4 introduction p.107, Theorem 4.1.4 p.110, Definition 5.1.1 p.136, Proposition 5.1.6 p.138, Corollary 5.1.11 pp.142-143, Theorem 5.1.13 pp.143-144; for both new nodes and item steps 1-2. The PDF is missing locally; I read these places online and have not downloaded to the read-only repository. Milne's Algebraic Groups (2017) is present locally and I read pp.445-449 with pdftotext. No SGA source is cited or used. No Stacks tag supplies this relative reductive-group structure; the existing definition-node dependencies give the scheme and morphism notions.

## Defects and corrections

The imported item has no proof and does not explain how a split torus over a local ring supplies relative root coordinates or lifts of Weyl representatives. Its proposed geometric-cover justification also needs more than existence of finitely many translates over an algebraically closed field: arbitrary such translating points need not lift to A. The proof now chooses the finitely many Weyl representatives over A and proves that those particular translates cover, by ordering the root factors inside each conjugate positive radical. This avoids assuming point lifting or applying field-only structure directly over A. The statement is unchanged and no STATEMENT-DISPUTED issue arose.

The blueprint ancestor tool reports `blueprint.from.node = None`. The item already has that value; new nodes retain that nearest-ancestor convention and prepend the item to the inherited via chain. The current blueprint was read only through literature/blueprint/latest, in sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. Its (3) is the inherited direct-image route. This atlas is a supporting relative-group prerequisite on that route, not a replacement of a unit or chapter argument. No unit realization fields need change for this non-key item.

## Not duplicates

Whole-DAG statement/concept searches and blueprint_refs.py searches for `big cell`, `split reductive`, `root datum`, `root subgroup`, `normalizer` and `open cell` found no imported blueprint node stating these relative inputs. Also checked sources for Conrad 5.1.1, 5.1.11 and 5.1.13: only the item and its parent quote those places. Searches in the current blueprint and Lean agree. The following candidate statements were opened, not inferred from titles.

lem-sfb-local-split-root-data-weyl-lifts vs lem-sfb-relative-torus-centralizer-normalizer: the latter represents and proves smoothness of centralizers/normalizers of a split torus in a smooth affine group; it gives neither root subgroups, free root lines nor global representatives of every geometric Weyl element.

lem-sfb-local-split-root-data-weyl-lifts vs lem-sfb-reductive-root-subgroup-parametrizations: the latter is over an algebraically closed field; the new lemma supplies groups and normalizer points over a possibly nonreduced local ring and their identification on every geometric fibre.

lem-sfb-local-split-root-data-weyl-lifts vs lem-sfb-reductive-rank-one-reflections: the latter constructs rank-one reflections and coroots over an algebraically closed field; it supplies no relative normalizer sections.

lem-sfb-local-split-root-data-weyl-lifts vs lem-sfb-weyl-reflection-realization: the latter identifies the field normalizer quotient with a reflection group. It does not lift representatives over a local base or trivialize relative root lines.

lem-sfb-relative-root-product-open-cell vs lem-sfb-borel-root-product-coordinates: the existing lemma is over an algebraically closed field and gives one unipotent radical's coordinates; the new theorem constructs closed relative subgroups and an open multiplication cell over A.

lem-sfb-relative-root-product-open-cell vs lem-sfb-longest-weyl-open-cell: the existing lemma is a dense cell over an algebraically closed field; the new lemma is the relative Gauss cell U-minus times S times U-plus over a local ring.

lem-sfb-relative-root-product-open-cell vs lem-sfb-bruhat-longest-cell-charts: this field theorem supplies the geometric stratification used in step 3, but no relative chart over A or base-ring Weyl representatives. It is reused, not recreated.

lem-sfb-relative-root-product-open-cell vs lem-sfb-integral-chevalley-weyl-atlas: the existing statement concerns a particular matrix closure over Z from a rational Lie representation and integral Chevalley lattice. The present input applies to an arbitrary reductive group over A with a specified split maximal torus, and asserts only the one relative cell, not exhaustion.

lem-sfb-local-split-root-data-weyl-lifts vs lem-sfb-split-reductive-local-gauss-atlas: root subgroups and normalizer representatives are structural inputs, not an open atlas. The new statement does not assert open immersions or a covering.

lem-sfb-relative-root-product-open-cell vs lem-sfb-split-reductive-local-gauss-atlas: the new statement supplies a single cell with its ordered subgroup coordinates; it does not assert a cover. The item's nontrivial exhaustion argument remains in steps 3-5 and uses the independent Bruhat theorem. Neither new lemma is a relabeling of the item or one of its conclusion clauses.

## Mathlib search assessment

Every search added to the item or a new node ran through the mandated msearch.py command and is recorded with its exact tool and query in searches.jsonl. Both relative inputs and the item were searched with LeanSearch, Loogle, grep and two semantic phrasings. All services responded. No search result was declared a match without reading its meaning.

RootPairing results concern abstract root pairings, and RootPairing.weylGroup (Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean:56) is the abstract subgroup generated by reflections, not the scheme normalizer or global sections thereof. LieAlgebra.IsKilling.finrank_rootSpace_eq_one (Mathlib/Algebra/Lie/Weights/Killing.lean:608) concerns a characteristic-zero field and Killing Lie algebra, not torus-character modules over an arbitrary local ring. RootPairing.nonempty_base (Mathlib/LinearAlgebra/RootSystem/BaseExists.lean:322) supplies combinatorics only after a root pairing is given. General AlgebraicGeometry open-immersion, cover and Laurent-polynomial declarations do not prove that the required multiplication map is open or that its Weyl translates cover. The GeckConstruction hits are Lie matrices, not reductive group schemes. Thus both new statements remain unsplit, not Mathlib leaves.

## Review by Q49

I read the standing brief, stage-1 rules, the three blueprint levels in SETUP, GOAL, the chapter and unit records, and delivery-errors B through E (including the duplicated retired-project sections). I checked self-contained hypotheses, definition references, source places, actual searches, cyclicity risk and the distinction between a proof and new statement-only inputs. The source review used Conrad online as specified above and Milne locally at 21.68, 21.69 and 21.73; the item's source had already named Conrad's relative-cell route. Both new nodes state relative theorems; their root and group notions are explicit. The field-only group-scheme definition is used only for its group diagrams, with the A-base and multiplication/identity/inverse spelled out, not for its finite-field consequences.

Step 1 uses the new local root-data/Weyl-lift statement for the fixed finite roots, additive root groups and base-ring representatives; its hypotheses repeat the item's A,H,S hypotheses verbatim. It then uses the new relative-product theorem for U-minus, U-plus, B and the open immersion. A split torus alone over an arbitrary base would not trivialize root lines: Conrad's p.107 weight subbundles and p.136 discussion show why local A makes the lines free and roots/coroots constant. This issue is part of the first structural input, not silently assumed in the assembly.

Step 2 uses the root/product isomorphisms already obtained in step 1. I verified the cited affine-spectrum statement includes contravariant functoriality, and the cited open-immersion statement explicitly identifies the source with an open subscheme. Coordinate-ring maps give the elementary product identification, and the group diagrams give inverse translations. The step never infers openness of multiplication from its definition.

Step 3 cites lem-sfb-bruhat-longest-cell-charts: I read its entire statement. It supplies the stratification C_w and the isomorphisms V^w times B to C_w, with V^w contained in the positive radical. The new relative statements identify the given fibre B,S,U-plus and W with precisely this theorem's field objects. The algebraically closed field F is arbitrary, not just the closed residue fibre, so the argument covers every geometric fibre.

Step 4 cites lem-sfb-borel-root-product-coordinates: I read its entire statement and its arbitrary-order clause, not just the original Borel's enumeration. Apply it to B-prime=n_w-inverse B n_w. The conjugation formula for root subgroups comes from step 1. Put those roots which are negative for the original Borel first and those which are positive last; the relative subgroup inclusions from step 1 then place their ordered products in U-minus and U-plus respectively. No rearrangement across noncommuting root factors is asserted. Multiplication by b stays in B, and the semidirect-product isomorphism obtained in step 1 supplies its S,U-plus factors. This proves membership in exactly the translated relative cell constructed in step 2.

Step 5 is an elementary point argument: a point h has a geometric point over its own residue field, and its membership in a translated cell projects back to h. This avoids a hidden closed-point/Jacobson or specialization assertion and requires no quasi-compactness extraction. The finite index set is already W, which has an identity. Every citation has a verbatim quotation in citations.json; no cited statement's proof is used as an unstated interface. There are no non-elementary steps over 2000 characters.

I tested H=1 (empty torus/root coordinates), H=G_m^r (no roots, one chart), SL2 (two Weyl charts, the a-invertible and c-invertible loci), and GLn (permutation pivot charts). A may be a field, Z_(p), or k[epsilon]/epsilon^2; the relative inputs are valid without reducedness, normality, henselianity or completeness. The nonzero hypothesis ensures a nonempty base. Nothing assumes characteristic zero or simply connected derived subgroup. Root products remain scheme isomorphisms, not just point bijections. The finite-cover statement is neither weakened nor strengthened in the delivered item.

## Unfinished work

No assembly step remains unresolved. The two new statement-only structural lemmas intentionally await their own one-level splits. Conrad remains WANTED locally; the proof is marked agent-origin, with the actual online places identified. Required server diagnostics and dry-run results follow below.

## Validation

Server srvcheck check_dag: OK, no finding introduced by the sandbox or on its nodes. The first complete deliver.py --no-push invocation exited successfully with server preflight passed (candidate f1bc5f4e4c6). This report-only validation addition is followed by a final complete dry run before the direct push. The delivery preflight includes check_dag.py, review_split.py, exact citation quotations and the recorded Mathlib searches.
