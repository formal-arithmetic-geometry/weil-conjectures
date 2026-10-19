# Q94 report: lem-sf-field-stage-ordinary-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-field-stage-ordinary-realization.json`: statement, split; no new node. The proof constructs the finite-field and common-stage ordinary realizations, proves boundedness, and proves coefficient-extension coherence. Mathlib searches found no direct match.
- `citations.json`: verbatim statement quotations for every node used by every proof step.
- `searches.jsonl`: actual Q94 Mathlib search command records.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, realization/rationalization terminology, and the likely six-functor declarations. No sorry-free declaration states this comparison lemma. The existing source declarations concern finite-level constructibility and adic realization, but do not state the ordinary constant-field functor from the raw rationalized/common-stage categories.

## WANTED:

None. The Stacks source, Bhatt–Scholze paper, and blueprint proof are present locally.

## What was wrong or incomplete

The imported node was a statement-only comparison obligation. Its source correctly identified Stacks Tag 09C2 as the boundedness ingredient and Bhatt–Scholze Proposition 6.8.14 as the finite-field descent comparison, but the two blueprint sentences did not specify the restriction-of-scalars functor, the scalar-localized morphism action, or the common-stage independence argument. I supplied those arguments as five proof steps without changing the statement or its hypotheses.

The boundedness step needs the quasi-compact hypothesis of the existing completed-residue bound. I therefore apply that result after restriction to each affine open of (Y), where the restriction of the derived-complete tower and its uniform reduction interval is immediate, and then use locality of cohomology sheaves. This avoids silently assuming that the original scheme (Y) is quasi-compact. The parent item's earlier type correction (naming the ordinary realization (J_F(K))) is retained; this node does not identify completed coefficients with discrete constant coefficients.

No statement dispute was found for this item. No new node was created: the finite-free completed comparison, the K-flat resolution, the scalar-localization laws, and the constant-field tensor cohomology statement already exist in the DAG.

## What could not be finished

Nothing remains unfinished in this split. The comparison statement is proved at the natural-language DAG level; no Lean code or compiler/build tool was used.

## Review by Q94

I read the copied item node, the chapter `dag/chapters/sec-six-functors.json`, the unit record `dag/units/sk-prop-sf-rf-shriek-preservation.json`, the current main-20261015 blueprint node and its proof, and the source files named in the item's source field. I also read every statement cited below rather than relying on a declaration's proof.

Step 1 uses `def-pc-sheaf-restrict-scalars` for the unchanged underlying abelian sheaf and the induced module action, `def-weil-completed-integral-coefficients` for (B_E), `def-weil-pbc-constant-sheaf` for ((\mathcal O_E)_Y), and `def-weil-pbc-proetale-site` for the ordinary target derived category. The restriction-of-scalars exactness assertion is the elementary kernel/cokernel calculation on the unchanged underlying sheaf; the ring map is the (u_E) in the item statement.

Step 2 uses the Hom formula and triangulated structure of `def-weil-rationalization-karoubi`, the (mathcal O_E)-linearity of the integral category from `lem-weil-integral-constructible-linear`, and the induced linearity of derived categories from `lem-weil-linear-abelian-derived-category`. `def-weil-derived-tensor`, `lem-weil-derived-tensor-functorial`, and `lem-weil-derived-tensor-resolution-independent` say exactly that the ordinary derived tensor is functorial and independent of a K-flat choice. These hypotheses give the scalar-localized formula (J_E(f\otimes a)=aJ_E(f)), so no representative-dependent map is used.

Step 3 uses the uniform reduction interval in `def-weil-derived-complete-integral-detailed` and the conclusion of `lem-sf-complete-residue-cohomology-bounds`. I checked the latter's hypotheses: on an affine open (V\subseteq Y), the restriction is quasi-compact, derived completeness is inherited by restriction, and the (n=1) reduction has residue-field Tor amplitude in the same interval because every module over that field is flat. The cited cohomology-sheaf definition justifies checking vanishing on the affine cover. Restriction of scalars leaves cohomology unchanged, and tensoring with the flat field extension (E/\mathcal O_E) preserves the interval. The interval is chosen before any test sheaf, as required for a uniform Tor bound later.

Step 4 uses `lem-weil-finite-free-completed-scalar-comparison`: the completed (R\to S) change is finite free and its canonical completion map is a natural isomorphism. `lem-weil-integral-scalar-extension-constructible` verifies that the integral transition object remains in the bounded constructible category, while `lem-weil-scalar-extension-well-defined` verifies independence of an integral representative. The two derived-tensor nodes supply the naturality and resolution independence used in the comparison. Every finite-field hypothesis is the inclusion (E\subset L\) from the statement; no quasi-compactness or extra finiteness of (Y) is introduced.

Step 5 uses the common-stage definition `def-weil-algebraically-closed-coefficients`, whose finite-field-of-definition clause supplies a common field for every morphism, and `lem-weil-scalar-extension-composition` for identity and composition coherence. The same finite-free comparison and tensor functoriality from Step 4 make the comparison square commute under further enlargement. Thus the (\Qlb)-formula is independent of representatives and common fields, and boundedness is inherited by flat scalar extension. The final sentence follows directly from the constant-sheaf definition.

I tested the zero object, a shifted one-term complex, an integral torsion object (which becomes zero after inverting the uniformizer), the empty scheme, identity coefficient extension, a two-step finite tower (E\subset L\subset M), arbitrary degree-zero test sheaves including infinite-dimensional ones, and a common-stage morphism represented over two different finite fields. All proof steps are below 2000 characters and contain no hidden auxiliary lemma. The only off-route tools are the generic K-flat-resolution and finite-free completed-scalar comparison, declared in `split_report.tool_uses`; neither replaces a step of the field-stage route. There is no cycle, no SGA citation, no Lean edit, and no compiler/Lake/build invocation.

## Not duplicates

- `lem-sf-field-stage-ordinary-realization` vs `def-pe-etale-constructible-module`: the existing definition concerns discrete Noetherian étale modules; this node constructs ordinary constant-field realizations of raw rationalized and common-stage adic objects.
- `lem-sf-field-stage-ordinary-realization` vs `def-weil-pbc-tower-preservation`: the existing definition records a tower-preservation condition; this node constructs (J_E), its boundedness, and its finite-field comparisons.
- `lem-sf-field-stage-ordinary-realization` vs `def-weil-pbc-witness-compatibility`: the existing definition records witness compatibility; this node supplies an ordinary realization functor.
- `lem-sf-field-stage-ordinary-realization` vs `lem-weil-pbc-tower-compatibility`: the existing statement concerns compatibility of a coefficient tower; this node additionally constructs the ordinary constant-field target and common-stage functor.
- `lem-sf-field-stage-ordinary-realization` vs `prop-weil-pbc-preservation-constructible`: the existing proposition concerns preservation before constructible restriction; this node concerns rationalization and ordinary constant coefficients.
- `lem-sf-field-stage-ordinary-realization` vs `prop-weil-pbc-restriction-direct-image`: the existing proposition concerns direct-image restriction; this node concerns scalar localization and realization.
- `lem-sf-field-stage-ordinary-realization` vs `thm-weil-pbc-amplification-proper`: the existing theorem concerns proper base-change amplification; this node has no proper morphism or base-change square.
- `lem-sf-field-stage-ordinary-realization` vs `lem-fix-residue-lisse-projective-models`: the existing lemma gives local projective residue models; this node constructs (J_E) and its coefficient descent.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sf-complete-residue-cohomology-bounds`: the existing lemma bounds a completed complex under a quasi-compact hypothesis; this node also defines ordinary field realizations and handles arbitrary (Y) by affine localization.
- `lem-sf-field-stage-ordinary-realization` vs `det-lem-int-integral-heart-triangulated`: the existing statement concerns the integral heart; this node concerns rationalized field-stage functors.
- `lem-sf-field-stage-ordinary-realization` vs `det-lem-integral-models-stacks`: the existing statement compares integral models with Stacks categories; this node gives an ordinary constant-field realization.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sfb-adic-constructible-finite-reductions`: the existing statement gives compatible finite reductions under Noetherian hypotheses; this node starts from the rationalized/common-stage category and proves field realization.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sfb-adic-finite-stratification-pullback`: the existing statement concerns finite stratification and pullback; this node concerns scalar localization and coefficient-field descent.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sfb-adic-residue-lisse-perfect-lift`: the existing statement gives local perfect lifts; this node constructs (J_E) on arbitrary schemes.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sfb-integral-cohomological-adic-criterion`: the existing criterion characterizes integral adic constructibility under Noetherian assumptions; this node concerns ordinary field realization.
- `lem-sf-field-stage-ordinary-realization` vs `lem-sfb-proetale-tor-local-global`: the existing statement compares local and global Tor dimension; this node constructs the realizing functor and finite-field comparisons.
- `lem-sf-field-stage-ordinary-realization` vs `sk-lem-int-integral-heart`: the existing statement describes the integral heart; this node concerns raw rationalization and common-stage objects.
- `lem-sf-field-stage-ordinary-realization` vs `prop-weil-pbc-levelwise-truncations`: the existing proposition concerns truncations of adic towers; this node concerns restriction and inversion of coefficients.
- `lem-sf-field-stage-ordinary-realization` vs `def-weil-derived-complete-integral-detailed`: the existing definition specifies the integral category and uniform reduction bounds; this node adds the ordinary constant-field realization and its coherence.
- `lem-sf-field-stage-ordinary-realization` vs `def-weil-proetale-tor-amplitude`: the existing definition specifies a Tor-amplitude predicate; this node constructs the field-stage object to which that predicate is later applied.
- `lem-sf-field-stage-ordinary-realization` vs `lem-weil-pbc-condensed-e-realization`: the existing comparison targets condensed continuous-field modules for separated finite-type schemes; this node targets ordinary discrete constant-field sheaves for arbitrary (Y).
- `lem-sf-field-stage-ordinary-realization` vs `lem-exc-constant-field-sheaf-tensor-cohomology`: the existing lemma computes cohomology after tensoring an already ordinary constant-field complex; this node supplies the missing realization of adic-category objects.
