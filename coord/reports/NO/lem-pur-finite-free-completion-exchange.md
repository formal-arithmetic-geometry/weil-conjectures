## Worker report

Group NO, item lem-pur-finite-free-completion-exchange, stage 1, 2026-10-21.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-finite-free-completion-exchange.json: split into nine proof steps. No Mathlib match for the item.
- citations.json: twenty entries, one for each step/node pair, quoting the statement actually used.
- report.md: worker report and direct-delivery review.

No new nodes; no new Mathlib leaves. searches.jsonl retains the five searches run with the required msearch command. write_split.py is sandbox-only working material, not a delivery file.

### Attachments

None. I searched the live read-only WeilConjectures source both for the exact blueprint tag and for finite-free/completion, scalar extension, tensor/product and adic comparison terminology. I read SixFunctors/ProEtale/FiniteCoefficient/Derived/CompletedExchange.lean and ScalarExtension.lean. The former defines completion/exchange for fixed scheme coefficients; the latter compares scalar extension with geometric operations. Neither states this arbitrary-ringed-site quotient-completion comparison with its arithmetic subsequence map and unit equation. No complete attachment was found. A sorry declaration would not have counted as one.

### WANTED

None. Stacks sites-cohomology.tex and the main-20261015 blueprint are present. The finite-free and augmentation details are explicitly agent-written, rather than attributed to the statement of Tag 0941.

### Changes and unfinished work

The input had no proof. The argument now verifies exactness and the canonical product map using finite-free coordinates, constructs the strict quotient tower comparison by balanced tensor formulas, applies the existing additive Roos comparison, and then inverts the general arithmetic restriction. It checks the augmentation equation on both product coordinates, proves descent from K-flat representatives by roofs, and explains basis independence. The limit complex is not assumed K-flat: exactness of scalar extension is what permits its direct use.

Nothing remains unfinished in this one-level split. Existing cited lemmas retain their own proof obligations. This delivery does not attempt stage 2 or stage 3, write Lean, compile, invoke Lake, or modify the shared repository.

## New nodes

None. Before contemplating any new node I searched all DAG statements/titles for Roos, exact products, finite-free scalar coordinates, tensor products, K-flat change of rings and localization. I also ran blueprint_refs.py ancestor on the item and blueprint searches for completion, finite free completion, finite free and arithmetic. The exact generic prerequisites already exist. In particular lem-pur-roos-additive-comparison supplies a general additive product-cone comparison; lem-sp-strict-tower-arithmetic-restriction supplies arithmetic restriction for arbitrary ring sheaves. I did not create a special-purpose lemma restating the item, its unit clause, its quotient balancing calculation or finite tuple/product reindexing.

## Not duplicates

No new-node/existing-node pairs arise. Existing nodes were reused rather than duplicated. The closest existing conclusion, lem-weil-finite-free-completed-scalar-comparison, is restricted to completed local-field coefficient sheaves and derived-complete input. It does not give the present assertion for arbitrary ring sheaves and arbitrary unbounded input. lem-pur-compact-support-roos-cofinality has the right coordinate formulas but assumes constant coefficient rings, so it cannot supply the general argument by itself.

## Statement corrected

STATEMENT-DISPUTED: the original specification referred to lem-pur-compact-support-roos-cofinality for arbitrary sheaves R and S, whereas that node assumes a constant ring sheaf associated with one commutative ring A. This is a hypothesis/type mismatch in the cited specification, not a counterexample to the exchange theorem. For an explicit test, on the opens of a discrete two-point space take the ring sheaf with stalks Z and Z[x]. It cannot be a constant ring sheaf, since the stalk rings are not isomorphic. Take S=R, t=v=2, e=1 and u=1. Multiplication is injective and products are exact (the module category is the product of the two ordinary module categories). All hypotheses of the item hold, but the constant-ring-only node does not apply.

I replaced that citation in statement and stmt_deps with lem-sp-strict-tower-arithmetic-restriction, whose statement covers an arbitrary sheaf of commutative rings and specifies the same coordinate selection and finite weighted block maps. I also made the exact-product normalization explicit by citing lem-weil-strict-roos-comparison where the units are specified. No object, map formula, mathematical hypothesis or conclusion has been weakened or added. The statement's scope remains arbitrary unbounded complexes. The original constant-ring formula is recovered on its actual domain.

## Source error

No error is asserted in Stacks Tag 0941. I read lemma-derived-limit-is-ok and its proof in sites-cohomology.tex: it constructs the inverse-limit triangle from K-injective towers and derived products. It does not itself state the finite-free scalar comparison. The error was the imported item's use of a constant-ring cofinality node under more general hypotheses; the preceding section records its correction and a concrete example detecting the mismatch.

## Mathlib searches

I used only the prescribed msearch.py wrapper for Mathlib searches, and read the returned hits. The five queries are recorded verbatim in searches.jsonl and appended to the item's inherited search history:

1. leanfinder: Finite free extension of sheaves of rings commutes with derived inverse limits of quotient towers on unbounded complexes with completion unit compatibility
2. loogle: "AdicCompletion", "ofTensorProduct"
3. grep: Roos|roos|completion.*tensor|tensor.*completion
4. leansearch: An exact additive functor preserving countable products commutes with derived inverse limit of towers of complexes of sheaves
5. leanfinder (second phrasing): An exact product preserving functor on module sheaves commutes with homotopy inverse limits and the canonical augmentation of a quotient tower

All services answered. Ordinary AdicCompletion.ofTensorProduct and its finite-Noetherian/Pi variants do not treat derived module-sheaf quotient towers. I read Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean, including ofTensorProduct at line 57 and its finite-Pi construction. The exact-functor hits include Functor.mapDerivedCategory, which I read in Algebra/Homology/DerivedCategory/ExactFunctor.lean at line 36; it supplies ordinary exact-functor localization, not the entire completion exchange. The second phrasing returned SheafOfModules.createsLimit and evaluationPreservesLimit (read in Algebra/Category/ModuleCat/Sheaf/Limits.lean at lines 62 and 70), ordinary sheaf limits rather than this derived result. The recorded verdicts are no match, never unavailable masquerading as absence.

## Review by NO

I performed the direct-delivery self-review with the item and all cited statements open, following delivery-errors B through E. The nearest blueprint ancestor is def-weil-derived-pullback-tensor-hom; I read the actual main-20261015 file, order 1826, in sec-proetale-coefficients/sk-def-sf-operations. Its final paragraph defines integral operations using compatible finite reductions and their derived inverse limit. I read the item's chapter record and sk-thm-sf-compatibility unit record: coefficient compatibility is its clause (7). This is the coefficient/limit part of that route, without using a purity, trace or SGA argument. I read Stacks sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok), Tag 06YS (lemma-K-flat-resolution), Tag 06YT (lemma-derived-tor-quasi-isomorphism-other-side) and the construction immediately following 06YT. Because the finite-free quotient and unit calculations are our refinement of these models, proof_origin.by is agent. There are no new-node sources to audit.

Step 1 uses the statement of lem-sfb-finite-free-scalar-coordinates, which gives the natural underlying-module isomorphism for every module sheaf, including rank zero. It is not being used merely as an existence of a basis on the ring. The statement of lem-weil-pbc-module-sheaves-colimits-forgetful supplies faithful exact forgetful functors and sectionwise products. Its exactness and faithful detection of zero kernels/cokernels justify reflecting the coordinate calculation. Reindexing a finite tuple of sequences is written explicitly, and the map is the canonical product-projection map; no abstract tensor-preserves-products lemma is hidden.

Step 2 uses lem-sf-exact-functor-derived-triangulated for termwise localization of the exact functor, and the computation clause of lem-pur-derived-change-of-rings to identify it with T. I checked that lem-pc-kflat-resolution permits arbitrary unbounded complexes and gives flat terms. The statement of lem-pur-kflat-change-of-rings gives both K-flatness and flat terms after scalar extension, so it applies to Y without assuming S/v^m flat. def-pur-sheaf-tensor-product actually defines sheafification of the sectionwise tensor and change of rings. In particular no equality of tensor-sheaf sections with a sectionwise tensor is presumed.

Step 3 uses that tensor definition and writes two inverse balanced maps. It checks local lifts modulo the ideal, the equality a(t)^n S=v^(en) S, and strict transition compatibility by reducing the same formulas. This is the elementary quotient calculation needed here; it is not a new lemma restating a clause of the item. Neither multiplication by t on Q nor multiplication by v on Y is assumed injective. Only invertibility of u is used in comparing ideals.

Step 4 uses precisely the general statement of lem-pur-roos-additive-comparison: additive F plus invertible canonical product comparisons implies the actual cone isomorphism with fixed coordinates. Step 1 verifies its hypothesis. lem-weil-strict-roos-comparison is stated for a small site, an arbitrary commutative ring sheaf, and exact countable module products; it gives natural normalization and the augmentation map, not just an unspecified distinguished triangle. Both module-product hypotheses are present in the item. The point where the possibly non-K-flat limit complex is tensored is justified by step 2's exact functor computation.

Step 5 uses lem-sp-strict-tower-arithmetic-restriction, not the constant-ring specialization. I checked its statement: it asserts a natural isomorphism of total derived limits, identifies the selection and weighted block maps, and preserves strict cone units. Under exact products, normalization identifies the formula with the actual termwise-product cone map. The transition composite s_(en,i), the range en through e(n+1)-1 and the inverse direction are all explicit. Step 6 uses its augmentation assertion and the normalization assertion of lem-weil-strict-roos-comparison; the source coordinate is the quotient of p tensor s and the other coordinate is zero along both routes. This proves the full unit equation rather than checking only its projections in the derived category.

Step 7 uses the first assertion of lem-pe-kflat-roos-representative-invariance. I checked that its statement is for an arbitrary ring sheaf R, arbitrary quotient-algebra towers, exact countable products, and flat-term K-flat representatives, so it applies to both X and Z. I did not use its weaker later existence assertion to claim naturality. K-flat change of rings supplies the needed flat-term S-models. Chain-map naturality is immediate from the displayed tensor and coordinate maps, and the proof states how homotopies are carried. Step 8 opens the actual statements of lem-pc-quasi-isomorphisms-multiplicative-system and lem-pc-right-fraction-representation, which give the calculus and roofs on the homotopy category. Resolving a roof's intermediate complex and a common refinement using lem-pc-kflat-resolution proves full faithfulness on the K-flat subcategory. The natural-transformation clause of lem-weil-pbc-localization-universal-property then gives descent and representative independence. This is not an appeal to an uncited universal derived quotient diagram.

Step 9 checks that the chosen basis was used only to verify an isomorphism; the actual maps were defined by projections, balancing and the arithmetic coordinates. I tested d=0 (S is the zero ring), Q=0, e=1, and t a unit (then v is a unit and both quotient towers vanish). For a nontrivial arithmetic test take R=Z[t], S=Z[v] with t mapping to v^e for e>1; the rank is e, and the quotient level is en, not n. For non-flat input, Q=R/t is computed by its two-term free resolution; I checked that the construction retains its derived quotient tensors rather than replacing them by ordinary Q/t^nQ. Shifts and unbounded sums of such inputs introduce no truncation or boundedness assumption. The two-point nonconstant-ring test above detects the corrected citation mismatch.

Every proof-dependency statement was read for the actual clause used, and citations.json quotes those statements verbatim. I checked the chosen dependencies' transitive statement/proof closures for a return path to the item: none exists. All nine steps are below 2000 characters. The only facts kept as elementary steps are balanced tensor/quotient formulas, the explicit augmentation-coordinate equation and basis independence; the general K-flat, cone, arithmetic, localization and representative-invariance facts are cited. There are no hollow definitions, new-node proof sketches, duplicate nodes, added hypotheses, omitted edge cases or route replacements. The concrete correction during this review was replacing the constant-ring-only cofinality citation before constructing the proof.

Generic tools from other units, if the route checker requires maintainer recording, are finite-free scalar coordinates, module-sheaf limits/forgetful exactness, K-flat resolutions/change of rings, normalized Roos comparison, K-flat Roos representative invariance, exact-functor localization, and the three calculus/localization lemmas. They serve only the ambient algebra of the specified strict quotient towers; no alternate geometric route is introduced. The maintainer, rather than this worker, decides any tool_uses record.
