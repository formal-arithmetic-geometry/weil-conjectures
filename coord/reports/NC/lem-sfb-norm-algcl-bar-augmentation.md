# Stage-1 report: lem-sfb-norm-algcl-bar-augmentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-bar-augmentation.json: statement, split into eight steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-profinite-cech-exact.json: one new statement-only analytic input, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.

The helper write_split.py and searches.jsonl are sandbox working records, not proposed project changes. No Lean file, repository file, launcher file, compiler or build was touched.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, bar augmentation and procyclic terminology found discrete-module procyclic computations, not the ordinary internal all-continuous norm-scalar comparison. No sorry-free project declaration states this item. No Mathlib hit states either proposed statement.

## WANTED

WANTED: a proof of positive profinite Cech exactness for the actual norm-topological algebraic closure of Q_ell, for lem-sfb-norm-algcl-profinite-cech-exact. The blueprint paragraph (3) only supplies the surrounding direct-image route. Its text does not prove this new analytic assertion. Neither the complete finite-extension input nor the definition of condensed continuous cohomology proves it. This input is deliberately a new unsplit statement, not a claimed established theorem or a hidden proof inside a definition.

WANTED: an exact external reference for the original noncomplete bar comparison, as already requested in the item's source record. The formal reduction now identifies an explicit sufficient lower-level analytic assertion.

## What was wrong or missing

The item was unsplit and explicitly lacked its noncomplete analytic reference. Its statement is unchanged, including all continuous functions, the ordinary derived category, the actual specified augmentation, resolution independence, and the degree-zero identity. No statement dispute or counterexample to the imported statement was established.

The complete finite-field lemma lem-sfb-normed-scalar-profinite-hom-acyclic cannot be applied to Omega: it explicitly assumes a finite extension and completeness. Its Cech input has the same restriction. The new input states the Omega-valued Cech problem separately instead of treating the missing completeness hypothesis as supplied. This sufficient analytic assertion is stronger than what the total comparison alone asks for; the split proves termwise acyclicity as an intermediate consequence, without adding it to the item's conclusion or identifying the two assertions as equivalent. The new assertion's full noncomplete case remains for its own stage-1 item; no infinite approximation series or completion argument is claimed here.

The inherited nearest-blueprint-ancestor chain is broken: tools/blueprint_refs.py ancestor prints None. I retained that computed null and the inherited via chain, with the explicit main-20261015 source paragraph; the new node prepends this item to via. I changed no ancestor or unit record. The unit JSON still records the historical sec-six-functors location, whereas the live source is under sec-six-functors-basics; I read both the unit record and the current unit and proof files. Their shared paragraph (3) is the direct-image route served here.

## Not duplicates

lem-sfb-norm-algcl-profinite-cech-exact vs lem-sfb-normed-scalar-profinite-cech-exact: the existing statement fixes a complete finite extension E; the new statement uses the noncomplete norm algebraic closure Omega with all continuous maps. The latter is not a specialization of the former.

lem-sfb-norm-algcl-profinite-cech-exact vs lem-sfb-normed-scalar-profinite-hom-acyclic: the existing statement is a derived internal Hom comparison for complete finite-extension scalars; the new statement is the additive continuous-function Cech complex of an arbitrary profinite surjection, with noncomplete Omega coefficients.

lem-sfb-norm-algcl-profinite-cech-exact vs lem-sfb-procyclic-scalar-cochain-evaluation: the existing statement computes an inhomogeneous additive-group cochain complex for Z_ell, locally in a parameter; the new statement concerns fibre powers of arbitrary profinite surjections, with no group action or procyclic computation.

lem-sfb-norm-algcl-profinite-cech-exact vs lem-sfb-norm-algcl-bar-augmentation: the new assertion has no group, action category, derived Hom, totalization or map j_A. Steps 1 and 3–8 give the formal argument from this independent analytic Cech input to the particular actual total augmentation. This is not the conclusion relabelled as a new node.

Whole-DAG searches covered 03F9, continuous-functions/Cech combinations, noncomplete or incomplete surjections, and the proposed new id. Blueprint searches were run for procyclic bar, Cech continuous, normed scalar, continuous function and 03F9. Existing finite-coefficient Cech results do not assert the new noncomplete case. Lean searches used the project's source rather than sorry declarations as proof evidence. Mathlib searches used only msearch.py and are recorded verbatim from searches.jsonl. Second phrasings found finite approximation and locally constant integer-function exactness; reading the Nobeling successor statement confirms that this is not the new assertion. The online continuous-cohomology hits define topological-module complexes, not ordinary condensed derived invariants; the named ContinuousCohomology file is absent from this pinned local Mathlib, so it is not recorded as a local match.

## What is unfinished

No part of the requested one-level split is intentionally omitted. The new analytic statement is unsplit, as required for a new non-Mathlib node. In particular its general noncomplete exactness is not claimed proved by the small-case checks below. The item's proof is agent-written and depends explicitly on that statement. This preserves the unresolved analytic work in the DAG instead of presenting a complete-field argument as a proof for Omega.

## Review by NC

I read AGENTS.md, the stage-1 brief, stage-1 specification, the three-level contract in SETUP.md, GOAL.md, the worker role, and delivery-errors B–E (including the retained copy). I read the chapter and unit records and the current main-20261015 unit statement and direct-images proof, especially paragraph (3). The source does not contain the desired noncomplete analytic proof; that absence is explicitly recorded above and in the new node. I read the new node and the item together rather than claiming the source supplied hypotheses it does not state.

For step 1 I checked the statements of the continuous-ring sheaf definition, sheafified tensor/closedness theorem, internal/sectionwise module equivalence, exact tensor comparison and module tensor/Hom adjunction. Their hypotheses are the small site and the ordinary sheafified abelian tensor. The sheaf-tensor theorem supplies the monoidal local equivalences and Grothendieck condition, not merely a tensor definition. The exact monoidal equivalence supplies the matching right adjoints. The last inference about preserving injectivity is the extension-property argument written in the step. Stacks sites-modules.tex Tag 03EO, lemma-internal-hom-adjoint-tensor, was read for the sectionwise adjunction.

For step 2 I checked the new analytic statement and the full statement of def-weil-pbc-site-cech-complex. The new input asserts exactness for precisely T_V^{n+1}, with the same signs and all continuous Omega-valued functions. A finite covering family is converted to its single finite disjoint-union surjection; the componentwise formula identifies the entire complex, not just its endpoints. No finite-field-valued replacement of a function occurs.

For step 3 I read Stacks sites-cohomology.tex Tag 03F9, lemma-cech-vanish-collection, and Tag 03FD, lemma-cohomology-modules-abelian-agree, and opened the two cited nodes. The criterion requires a cofinal system of covers and closure under every iterated fibre product. The full set of defining finite jointly surjective families has both properties on the profinite site. Step 2 supplies positive Cech vanishing. I also read the module-Grothendieck and enough-injectives statements: the closed monoidal category required by the former was supplied in step 1. The evaluation-comparison statement uses the actual ring sheaf A, has the common-universe assumption, and does not assume that A is constant or its underlying abelian sheaf injective. These checks are why this step cites the comparison theorem, rather than assuming underlying injectivity.

For step 4 I read def-pur-sheaf-hom and Stacks 08J7, section-internal-hom. The slice-Hom formula is the statement of that definition. Evaluation on the tautological generator and pullback along (v,p) give the two inverse maps; the argument is included explicitly and uses the free adjunction already specified by the item. For a general module N its value is N(S times P), rather than C(S times P,Omega) unless N=A. The maps are A(S)-linear through the S-coordinate and are natural for every continuous P' to P. Thus I did not cite a definition as a substitute for an unproved internal-Hom acyclicity theorem.

For step 5 I checked exactness at all section groups J(S times P), which step 3 gives for every profinite S times P. Equality of presheaf images and kernels here makes the images sheaves, so passage to sheaf cohomology is justified explicitly. Derived localization is the meaning of def-weil-abstract-derived-category, whose statement I read. This is a consequence of the separate analytic premise, not a claim that noncomplete acyclicity follows from the complete-scalar node.

For step 6 I read the entire statement of lem-sfb-condensed-derived-invariant-bar: it explicitly supplies the compatible nonnegative derived-Hom model, but does not supply the underived comparison. Step 5 supplies that comparison. I read def-sp-double-complex-total and lem-sc-first-quadrant-total-column-comparison, and Stacks homology.tex Tag 0133, lemma-double-complex-gives-resolution. Every H^q is profinite, face maps are continuous, and trivial action makes the first face exactly deletion. Both double complexes are first-quadrant, the source columns are in resolution degree zero, and each total degree is a finite sum. Consequently the comparison theorem applies to the actual augmentation whose components come from A to I^0, rather than to an arbitrary isomorphism of its source and target.

For step 7 I read the statements of the injective-resolution lift lemma, the normalized derived-resolution naturality lemma, and uniqueness up to homotopy. The first gives augmentation-preserving lifts, the second compares the actual resolution models, and the third supplies the homotopy between two choices. I checked its sign after totalization: in bar degree q use (-1)^q times the resolution homotopy, so horizontal terms cancel and vertical terms retain the required sign. I did not assume a comparison chain map between arbitrary complexes merely because their cohomology is isomorphic.

For step 8 I checked H^0 equals A using the invariant inclusion in the bar node and the identity normalization of the resolution augmentation. The q=0 inhomogeneous differential is zero for trivial action. Empty parameter sets give zero section groups, and there are no negative-degree or infinite-diagonal exceptions.

I tested the new analytic assertion on the empty surjection (all groups zero), the identity cover, finite surjections, and every continuously split surjection q. In the split case choose a continuous section sigma and define (hf)(t_0,...,t_{n-1})=f(sigma(q(t_0)),t_0,...,t_{n-1}); insertion of the first coordinate gives dh+hd=1 in positive degrees. For n=1 the cocycle identity gives f(t_0,t_1)=f(a,t_1)-f(a,t_0), with a=sigma(q(t_0)), so the sign in dg=f is correct. Finite surjections admit such a section. These cases use finite evaluations only and are valid without completeness. I also checked the finite-subextension-valued cocycle subcase against the existing complete finite-extension Cech node, which applies to that fixed field and gives a primitive there. None of these checks proves arbitrary noncomplete exactness, and the new node remains unsplit.

Against B–E: the new node has a self-contained statement, fixed coefficient topology, explicit fibre powers and differential, no embedded proof, empty proof/dependency fields, exact logged searches and blueprint provenance. Every cited step/node pair appears in citations.json with a verbatim statement quote. Formal tools of other units are declared in split_report.tool_uses, not installed as top-level tool_uses. No new node is elementary, a duplicate or a clause of the item. No step exceeds 2000 characters. No SGA source was used. No route or target statement was weakened.

## Validation

The preliminary remote review_split check passed. The required full deliver.py dry run and final push are recorded by the delivery tool after this report.
