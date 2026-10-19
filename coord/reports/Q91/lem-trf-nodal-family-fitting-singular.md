# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-family-fitting-singular.json`: item, split in four steps; statement unchanged, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-dth-fitting-smooth-locus.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-curve-lci-criterion.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-fibre-unramified-criterion.json`: new statement, unsplit; no Mathlib match.
- `citations.json`: verbatim statement evidence for every use in every proof step.

## Attachments

None. I searched `WeilConjectures/` in slopmaster2 for the blueprint tag, nodal, Fitting and the unramified geometric-fibre concepts. The nodal hits are examples in docstrings, not proofs of this item. I also checked the master reference, without treating its declarations as completed work.

## Wanted

None. All sources used are available locally in the Stacks checkout.

## Faults and corrections

The item was a statement-only node created in the reviewed projective nodal-family split. There was no earlier sandbox split or report. Its statement agrees with the cited Stacks result and is unchanged. Its source mentions 0C3J, but the zero-Fitting unramified-locus theorem alone does not imply that a first-Fitting singular subscheme is unramified: that needs 0C4E and the fibre criterion 02G8. The split makes this distinction explicit. The only added statement dependencies are the smooth-morphism and geometric-fibre definitions already used in its text. The source, creator, unit and all other maintainer fields are preserved.

I initially considered a separate Fitting-base-change node, but did not create it: the affine tensor quotient/minor argument belongs in an elementary step. The field input is the independent, bidirectional nodal/local-complete-intersection characterization 0C4E, not a renamed relative-family conclusion. The geometric-fibre criterion applies to every locally finite type morphism, not only to singular subschemes. The smooth-locus criterion applies in every dimension and without nodality. Their combination, the affine formation argument, the local-finite-type check, and the arbitrary base-change argument remain in the item's proof.

## Unfinished work

The three new lemmas intentionally remain statement-only stage-1 work. No part of the item's proof is left as a sketch. No Lean was written or compiled. Delivery validation is recorded below when complete.

## Searches and route

I read AGENTS.md, the worker brief, the stage-1 document, SETUP's three blueprint levels, GOAL, coord/dag-sync, the entire delivery-errors B–E, the unit sk-i-curve-zero and the Trace Formula chapter. I read the current main-20261015 local-term-locality proof and the existing projective nodal-family parent. This is below the unit's normal-cone specialization input; no chapter or unit statement is changed and no SGA route is used.

I ran blueprint_refs ancestor and whole-blueprint searches for nodal family fitting singular, Fitting, 0C3I, dth Fitting, smooth Fitting, nodal complete intersection, 0C4D, unramified fibres and unramified geometric fibres. There is no blueprint node stating the new inputs. I searched the whole DAG by the tags 0C3I/0C3K/0C4D/0C4E/02G8/02VM and their concepts, opened the overlaps listed below and reused the existing differential base-change, affine fibre-product, flat base-change and finite-presentation base-change nodes.

Every new node has actual msearch.py LeanFinder, Loogle, LeanSearch and grep queries, plus a second semantic phrasing, copied from searches.jsonl. I read the returned signatures. Fitting hits are Lie Fitting decompositions, nodal hits are Lagrange polynomials, and the second nodal query returns only specialized Weierstrass nonsingularity facts. Differential base change itself is already present and is reused. General formally-unramified and local-ring results, including the forward residue-field base-change lemma in RingTheory/Unramified/Locus, do not state the geometric-fibre criterion. No new Mathlib leaf is claimed. Unknown Loogle identifiers are recorded as returned zero-hit query errors, not as successful mathematical evidence on their own.

The off-unit tool declarations in split_report are generic algebraic differential base change and generic local-finite-presentation base change; they do not replace a step of the unit's route. The other off-unit results used are Mathlib leaves.

## Review by Q91

I read curves.tex at 0C59, 0C5B, definition-nodal, 0C4D and 0C4E; divisors.tex at 0C3I and 0C3K and the Fitting presentation conventions; algebra.tex at 00P4 and the differential base-change statement; and morphisms.tex 02G7/02G8 and descent.tex 02VM. The item is the forward nodal-family argument of 0C59 together with the smooth-support and formation results. Neither projectivity nor a Noetherian base is needed.

For the dth-Fitting node I checked every hypothesis of 0C3K: flatness, local finite presentation and pure fibre dimension. Its geometric formulation is equivalent to the ordinary fibre formulation by the pointwise dimension invariance of 00P4 on affine charts. The ideal uses n-d minors, unit ideal for d at least n, including d=0; no assumption of smoothness is built into its definition. For the nodal criterion I checked the full equivalence against 0C4E and the completed-local-ring description against definition-nodal and 0C4D. Local complete intersection is explained using the existing algebraic definition, rather than left undefined. For the geometric-unramified node I checked the locally finite type hypothesis in 02G8(2): 02VM descends unramifiedness of a geometric fibre along Spec of the algebraic closure to the ordinary fibre; 02G7 gives the separable-spectrum description required by 02G8. Flatness is not required here. These are three genuine source lemmas or their general geometric formulations, not elementary conveniences or a new statement of the whole item.

Step 1 uses exactly the affine spectrum fibre-product statement to identify the tensor-product ring, the existing Kahler base-change statement to identify the differential module, and the first-Fitting definition to identify the ideal. I opened all three statements: the Kahler node explicitly gives the A'-linear isomorphism required here, not merely an R'-linear map. The remaining argument is the elementary quotient universal property and determinant multilinearity, written out. It works with an infinitely generated relation module; no finite presentation of that kernel or flatness of S' over S is assumed. This is why I removed the proposed extra formation node.

Step 2 takes the open smooth locus and support equality from the general dth-Fitting statement at d=1 and identifies its ideal using the existing first-Fitting definition. The statement does assert the support equality; I do not cite a definition for a smoothness theorem. Every hypothesis of that criterion is present in the item.

Step 3 first checks local finite type using the finite-presentation affine polynomial-quotient definition and the quotient description of the first-Fitting closed subscheme; the quotient is generated by the images of the original algebra generators regardless of whether its defining ideal is finitely generated. I added the explicit finite-presentation base-change citation here after noticing that local finite type of C over Omega also needs it. Step 1 identifies the actual scheme-theoretic geometric fibre of Z, so 0C4E applies to that subscheme, not to its reduction. The new nodal criterion's statement gives unramifiedness in the (1) to (2) direction. The geometric-fibre criterion's statement then gives global unramifiedness after the local-finite-type check. Empty fibres are treated separately and cause no omitted case.

Step 4 uses precisely the flat base-change theorem and clause (3) of qcqs-morphism-permanence, which I read rather than inferring finite presentation from the node's title. Its clause (3) allows every base morphism. Associativity identifies the fibre over any algebraically closed geometric point with the corresponding fibre of X; the pure dimension hypothesis therefore persists. Applying the general dth-Fitting criterion to f' supplies its nonsmooth support, while step 1 supplies the scheme equality. Neither a finite-type base change nor reduction commuting with base change is asserted.

For small cases I checked: X empty (both loci empty); a smooth relative line (Omega free of rank one, Fit_1 unit, singular scheme empty); xy=0 over an algebraically closed field (presentation row (y,x), first Fitting ideal (x,y), singular scheme Spec k, including characteristic two); xy=t over k[t] (singular scheme Spec k); and t=s^2 (singular scheme Spec k[s]/(s^2), unramified over k[s] as a closed immersion). The last case is why the nonreduced Fitting scheme must be retained. For the general criterion d=0 gives Fit_0; a smooth pure d-dimensional family has Fit_d unit. For the unramified test an identity morphism passes even over a nonreduced base, whereas Spec k[epsilon]/epsilon^2 over k fails, and a nontrivial purely inseparable field extension fails after algebraic closure. These cases check the absence of unwanted reducedness, perfection, nonemptiness and Noetherian hypotheses.

I checked B1–B10: every new object is introduced, notions are cited or defined inline, the unsplit nodes have no proof or proof dependencies, tags and labels match the local sources, and no leaf or attachment is claimed without evidence. I checked C1–C8 against the cited statements and wrote citations.json by copying their actual statements. The relative singular-subsheme argument is not moved wholesale into a new node (D1–D5); the formation computation and the passage from field-level information to the family are in the item's steps. I checked E1–E7, especially arbitrary nonflat base changes and empty fibres. No statement dispute or source error was found. No proof step exceeds 2000 characters, and no hidden comparison has been left in a long step.

## Not duplicates

lem-trf-dth-fitting-smooth-locus vs lem-trf-fitting-ideal-independence-base-change: the existing node proves presentation independence and arbitrary ring base change for Fitting ideals of a finitely generated module; the new node identifies the smooth locus with the d-th Fitting support for a flat locally finitely presented family and adds the geometric-fibre dimension hypotheses.

lem-trf-dth-fitting-smooth-locus vs lem-ag-rational-point-local-dimension-base-change: compares local-ring dimensions at rational sections after a field extension; it has no Fitting smooth-locus assertion.

lem-trf-dth-fitting-smooth-locus vs lem-ag-rational-point-topological-local-dimension-base-change: compares dimensions at rational points only; it has no smoothness or differential ideal criterion.

lem-trf-dth-fitting-smooth-locus vs def-trf-first-fitting-singular-subscheme: defines only the first-Fitting subscheme and its localization convention; it does not identify the nonsmooth locus.

lem-trf-dth-fitting-smooth-locus vs lem-trf-nodal-family-fitting-singular: is the current d=1 nodal-family package; the new input is the general all-d smoothness criterion without a nodality hypothesis, and does not prove unramifiedness or formation.

lem-trf-dth-fitting-smooth-locus vs new-zdbp-geometry: proves finiteness and discreteness of a zero-dimensional finite-type scheme over an algebraically closed field, not a smooth-locus criterion.

lem-trf-dth-fitting-smooth-locus vs lem-weil-pbc-polynomial-presentation-height-field-extension: gives a height identity under field extension, not a Fitting ideal or smooth locus.

lem-trf-dth-fitting-smooth-locus vs lem-weil-pbc-discrete-field-base-change-artinian: asserts discreteness/Artinianness after field extension, without any smoothness criterion.

lem-trf-dth-fitting-smooth-locus vs new-zdbp-fibres-homeomorphism: asserts a homeomorphism for zero-dimensional field base change, not Fitting support or smoothness.

lem-trf-dth-fitting-smooth-locus vs lem-weil-pbc-zero-dimensional-base-change-points: describes points of zero-dimensional field base changes, not differential ideals or a smooth locus.

lem-trf-dth-fitting-smooth-locus vs new-zdbp-fibres-topology: preserves dimension at most zero under field base change, without a smooth-locus criterion.

lem-trf-dth-fitting-smooth-locus vs lem-weil-pbc-dimension-at-point-field-extension: is the dimension-invariance input underlying the geometric formulation; it does not state the Fitting/smoothness assertion.

lem-trf-geometric-fibre-unramified-criterion vs lem-sc-etale-local-ring-faithfully-flat-descent: descends pointwise etaleness under a field extension for finitely presented algebras; it does not test unramifiedness on fibres of an arbitrary base.

lem-trf-geometric-fibre-unramified-criterion vs lem-weil-pbc-unramified-over-field-discrete: only deduces discreteness from unramifiedness over a field; it has no converse fibrewise test for a family.

lem-trf-geometric-fibre-unramified-criterion vs lem-weil-pbc-unramified-fibre-point-isolated: only deduces an isolated fibre point from an already unramified point; it does not infer unramifiedness from geometric fibres.

lem-trf-geometric-fibre-unramified-criterion vs lem-weil-pbc-etale-residue-field-extension-separable: only gives separability of residue fields of an etale morphism; it has no geometric-fibre criterion.

lem-trf-geometric-fibre-unramified-criterion vs lem-weil-pbc-unramified-algebra-over-field-product: decomposes an already unramified affine field scheme as a product; it has no test on all fibres of an arbitrary-base morphism.

lem-trf-geometric-fibre-unramified-criterion vs lem-galois-fpqc-descend-unramified: descends along an fpqc cover of the base; the collection of geometric points is not such a cover, and the new node additionally uses the independent fibrewise test 02G8.

lem-trf-geometric-fibre-unramified-criterion vs lem-sc-etale-units-stalk-evaluation-overfield-bijective: concerns bijectivity of evaluation of units at an etale stalk, not unramifiedness of scheme morphisms.

lem-trf-geometric-fibre-unramified-criterion vs lem-sc-etale-residue-field-map-etale-tool: only gives the etaleness of a residue field map for an already unramified morphism; it has no geometric-fibre converse.

lem-trf-geometric-fibre-unramified-criterion vs lem-galois-fpqc-descend-etale: descends etaleness along fpqc covers, not unramifiedness from geometric fibres, and requires different hypotheses.

lem-trf-geometric-fibre-unramified-criterion vs lem-sc-etale-units-stalk-evaluation-overfield: constructs the units-stalk evaluation equivalence, not an unramifiedness test.

lem-trf-geometric-fibre-unramified-criterion vs lem-sc-etale-evaluation-separable: only concerns separable values of global functions on etale field schemes, not a fibrewise criterion.

## Validation

Required server dry run exited successfully: `OK (not pushed) deliver/Q91/lem-trf-nodal-family-fitting-singular at a127e224c8: preflight passed`. The remote preflight included the required DAG and split review checks. Three new statement-only nodes, zero Mathlib leaves. The direct-delivery brief authorizes the following push after this successful dry run.

## Repair of returned delivery

The prior delivery was returned because the reviewed base node `def-trf-first-fitting-singular-subscheme` changed. I re-read its current statement in the shared DAG. It now explicitly records the finite-generation input as `[lem-weil-pbc-lft-affine-pairs]` and the localization input as `[lem-trf-fitting-ideal-independence-base-change]`; its Fitting-minor definition, n≤1 convention, gluing, and singular closed subscheme are otherwise the same. I updated all three `citations.json` entries that cite this node to the exact current statement. Steps 1–3 still use only claims present in that statement, and no statement, hypothesis, dependency, or proof step needed mathematical alteration. The three new nodes and their citations were re-read against the current shared DAG and remain unchanged.
