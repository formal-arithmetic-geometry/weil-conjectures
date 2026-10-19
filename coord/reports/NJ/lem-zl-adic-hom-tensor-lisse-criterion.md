# Worker report

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-adic-hom-tensor-lisse-criterion.json: statement unchanged, now split in five proof steps.
- dag/nodes/sec-zeta-weil/lem-zl-rational-realization-tensor-comparison.json: new statement-only node; no Mathlib match.
- dag/nodes/sec-zeta-weil/lem-zl-t-admissible-dualizable-truncations.json: new statement-only node; no Mathlib match.
- citations.json: verbatim statement quotes for every node used by each numbered proof step.

## Attachments

None. I searched WeilConjectures in the slopmaster2 source both for the exact blueprint tag and for lisse, dualizable and evaluation/internal-Hom terminology. The pro-etale Derived/Perfect.lean theorem isDualizable_iff_isLocallyPerfect has sorry and concerns discrete coefficient sheaves; its consequence isLocallyPerfect_of_isDualizable is not an attachment of this continuous adic assertion. The adic Constructible, Abelian and Lisse files concern sheaves already known lisse or stratified lisse, not this converse for arbitrary constructible complexes. The exact upstream master was treated as reference material only.

## WANTED

None. Both source PDFs needed for this split are present and were read.

## Problems found and repaired

The item was unsplit, with no earlier sandbox proof or report. Its statement is mathematically sound and is retained verbatim. It carefully avoids assuming a lisse integral lattice globally, and this distinction is necessary: Hemo--Richarz--Scholbach Remark 5.7 warns that localization of the integral lisse category is not generally essentially surjective. The proof instead creates duality maps in the rational category and realizes them in continuous coefficient modules.

The blueprint's final sentence about passing from the integral tower to rational lissity is the location this helper repairs, as specified by its existing ancestry. I read the current main-20261015 Step 1, the chapter record and unit sk-prop-smooth-proper-purity. The unit and its realization record are unchanged: this item is not the unit's key node. No unit step is replaced.

During self-review I folded the general evaluation-representability criterion back into Step 1: constructing eta and checking the second triangle by injectivity is a short explicit categorical calculation, not a new node. Its executed searches remain in searches.jsonl. I also added the existing finite-type affine noetherian-topology and finite irreducible-component lemmas so that the geometric hypothesis of the truncation theorem is actually justified. Neither an internal-Hom comparison for continuous realization nor descent of the universally quantified hypothesis is asserted.

## Not duplicates

lem-zl-rational-realization-tensor-comparison vs lem-per-continuous-rational-derived-realization: the existing node gives the t-exact equivalence, coefficient-ring identification and pullback compatibility; it does not assert tensor/unit comparisons or their monoidal coherences for the completed tensor used here.
lem-zl-rational-realization-tensor-comparison vs lem-fd-rational-coefficient-category-comparison: the existing node identifies the two raw rationalizations and their coefficient extensions, not completed tensor with ambient continuous-field tensor.
lem-zl-rational-realization-tensor-comparison vs lem-tw-lisse-rational-realization: the existing tensor comparison is restricted to lisse heart objects; here the two inputs are arbitrary bounded constructible complexes, before lissity has been proved.
lem-zl-rational-realization-tensor-comparison vs lem-zl-point-realization-coefficient-comparison: the latter is a point comparison with finite-matrix realization, not a tensor comparison on an arbitrary finite-type scheme.
lem-zl-rational-realization-tensor-comparison vs lem-zl-normalized-coefficient-unit-realization: the latter supplies units and pullback normalization, not the two-variable tensor comparison.
lem-zl-rational-realization-tensor-comparison vs det-lem-int-tensor-product: the latter proves ordinary integral tensor constructibility and a local duality statement, not comparison of completed/rational tensor with continuous-field tensor.
lem-zl-rational-realization-tensor-comparison vs det-prop-scalar-six-tensor-hom: the latter is ambient coefficient extension, not comparison with the completed-integral raw-rational operations.
lem-zl-rational-realization-tensor-comparison vs lem-weil-pbc-condensed-e-realization: the latter gives equivalences and pullback/direct-image compatibility, not tensor compatibility.
lem-zl-t-admissible-dualizable-truncations vs lem-zl-adic-hom-tensor-lisse-criterion: the new node is the general t-admissible condensed-ring truncation/heart theorem, with no evaluation-comparison hypothesis, no raw rationalization, and no adic finite-field descent. The item derives its own implication using that theorem.
lem-zl-t-admissible-dualizable-truncations vs sk-def-perfect: the latter defines dualizability and states a local perfectness equivalence; it gives no t-admissible-ring truncation theorem or description of the restricted heart.

The DAG and whole blueprint were searched for dualizable, t-admissible, regular coherent, lisse truncation, continuous rational, rational tensor, completed tensor and tensor realization, and statements of the candidate nodes above were opened. None of the new statements is already an imported blueprint node. No new Stacks tag occurs in these nodes: these precise assertions use Bhatt--Scholze and Hemo--Richarz--Scholbach rather than a numbered Stacks result. All same_as lists are empty.

## Review by NJ

I read Hemo--Richarz--Scholbach Definition 3.3, Definition 6.1, Theorem 6.2(2), Corollaries 6.3 and 6.11, Proposition 5.5, Remark 5.7, Theorem 7.7 and Lemma 7.9 in the local PDF. I read Bhatt--Scholze Proposition 6.8.14(2) and Remark 6.8.15, with the surrounding coefficient conventions. Proposition 6.8.14(2) explicitly gives equivalence of the raw localization without passing to an etale cover; HRS's notation Dbc(X,E), by contrast, includes idempotent completion. The report and proof therefore do not silently replace the project's raw category by that completion.

For the tensor-comparison node I checked its domain against the two existing realization statements: T is separated finite type over the algebraic closure of a finite field, ell is invertible, the ring is the completed coefficient sheaf localized at a uniformizer, and the source is the raw category. Its source is BS's rational comparison/operations together with HRS's coefficient-extension comparison. The extra assertion is monoidality for the specified completed operations, isolated as an unsplit lemma rather than hidden in a proof step. A future proof can compare ordinary integral tensor with completion (using the constructibility theorem), then apply the symmetric monoidal coefficient extension; the normalization on localized arrows and finite extensions is part of its statement. Its statement contains no proof sketch.

For the truncation node I checked every hypothesis of HRS Theorem 6.2(2): a commutative condensed ring with regular coherent underlying ring, flatness over extremally disconnected profinite sets, and a scheme with locally finitely many irreducible components. The conclusion includes preservation by both standard truncations and the exact description of the heart as local scalar extensions of finitely presented underlying-ring modules. Dualizable here means evaluation/coevaluation in the ambient derived category, not constructible with an assumed lattice. This general ring theorem is substantively different from the item's adic evaluation criterion.

Step 1 uses the actual statement of lem-coef-completed-tensor-hom-transpose, which supplies the rational evaluation-formula bijection. The specified canonical c gives the displayed Phi, not an arbitrary isomorphism with the same objects. At the common stage the pair-category equivalence relation and common-stage operations allow the filtered-colimit bijection. The first triangle is the definition of eta. For the second, r and the identity have the same image under the injective Phi(D,1): interchange moves the two disjoint evaluations and the first triangle reduces the composite to e. These are the only extra categorical calculations, written explicitly and not hidden in a new lemma. K-dual is in the given category by hypothesis; the assumed internal Homs supply all the pairs needed by the transpose node.

Step 2 cites the pair-category statement, which actually says every arrow has a finite common-stage representative and equality holds after a finite further extension. There are two triangle equalities, so a compositum makes both true at once. The operations statement supplies the finite-stage product and scalar comparisons. The finite-stage identity comparison identifies the PBC and framework models on their shared integral representatives and localized arrows. No claim about all test objects descends; only the finite duality data descend. This is elementary from those definitions.

Step 3 cites the tensor-comparison node precisely for its strong monoidal comparisons, and the two existing equivalences for the category identification and t-exact continuous realization. It applies the realized evaluation and coevaluation inside the full ambient derived category, so their triangle equations also hold there. Nothing uses an unproved claim that internal Hom commutes with rational realization.

Step 4 verifies the coefficient hypothesis explicitly: a finitely presented vector space is finite free, and every vector space is flat, so the field coefficient ring is t-admissible. The field's spectrum is a point; the finite-type affine noetherian-spectrum lemma gives noetherian topology on each affine chart, and a finite affine cover gives global noetherian topology. The finite irreducible-components lemma says exactly what is then required by HRS. The new truncation node gives local finitely presented F-modules; taking bases gives finite free F_T-modules. This is where finite rank, including zero and ranks varying between components, is obtained.

Step 5 uses the existing realization's actual t-exactness and the identity-on-integral-objects equivalence to commute cohomology with J. The lisse-realization statement gives exactly the essential image of locally finite free sheaves and full faithfulness for the same coefficient-extension functor. The existing truncation theorem explicitly commutes with finite scalar extensions at a common stage, which justifies the Qbar conclusion; a theorem merely about cohomology of vector-space complexes would not suffice and is not cited.

I tested the empty scheme, the zero object, shifted units, disconnected schemes with different ranks and an arbitrary finite coefficient extension. The heart theorem permits rank zero and varying local modules. The truncation lemma is not claimed for arbitrary schemes such as a profinite space with infinitely many components: HRS Remark 6.4 explains the failure in that case, and its local finiteness hypothesis is retained. Torsion integral objects disappear after localization, and the tensor comparison sends them to zero as it should. None of the new statements assumes that a rational lisse object has a global integral lisse lattice.

All new nodes have statements only, empty proof/proof_deps and null proof_origin, plus complete blueprint ancestry and exact executed searches. All three search kinds were used with second semantic phrasings. The returned Mathlib declarations concern ordinary module completion, generic monoidal structures, t-structures on arbitrary derived categories, or finite-presentation predicates; none proves either new assertion. There are no new Mathlib leaves. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual statements: no new clause restates the item, no route change, no source error, no SGA citation, no hypothesis added to the item. Each proof step is below 2000 characters; the tensor comparison and geometric truncation theorem are the two non-elementary inputs isolated as nodes. Generic off-unit tools are declared in split_report.tool_uses. The statement dependencies are retained; proof_deps is exactly the union of uses. citations.json contains one verbatim statement per cited step/node pair.

## Unfinished work

None within the one-level stage-1 split. The two new nodes intentionally remain unsplit for their own future items. No Lean file or compiler/build tool was used, and all writes are confined to this sandbox. Delivery validation is recorded below after running the required remote tools.

## Delivery validation

The required remote dry run exited successfully: `OK (not pushed) deliver/NJ/lem-zl-adic-hom-tensor-lisse-criterion at 730aee20d0: preflight passed`. This includes the server DAG and split checks. The item statement remains verbatim equal to the current shared repository statement; the final proof step lengths are 1418, 1442, 1025, 1255 and 1063 characters. The only subsequent change before pushing is this validation record.
