## Worker report

Files written: dag/nodes/sec-deligne-laumon-a1/lem-per-rational-stratum-finite-free-model.json (statement, now split; nine steps, no complete Mathlib match), citations.json, and this report. Searches are recorded by msearch.py in searches.jsonl. The PDF text extract and write_split.py are sandbox research aids only.

## New nodes

None. Zero Mathlib leaves created. Every required non-elementary input already has a DAG node; the scalar associativity and specified block-cokernel calculations are short elementary arguments, not new nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for rational models, finite free models and continuous coefficients. ContinuousSheafPullback.lean addresses continuous sheaves and geometric pullback; PadicIntModuleRationalizationRegular.lean proves the regular integral-coefficient rationalization formula. Neither states this item's arbitrary finitely presented stratum model, its two constant-scalar comparisons and its presentation-matrix clauses. No exact project attachment was found.

## WANTED

None. The cited literature is present locally.

## Corrections and scope

No statement correction or STATEMENT-DISPUTED issue was needed. The initial node had a statement and searches but no proof. I retained its statement, source, provenance, blueprint ancestry and earlier searches, and added the proof and fresh logged searches. No repair note for this item or return entry for Q97 was present. No Lean was written or compiled, and no repository or launcher file was changed.

The rational coefficient sheaf is not the constant E-sheaf. Step 4 uses the constant sheaf only as an intermediate scalar ring and then extends to the continuous coefficient sheaf. Restriction to a covering object is restriction on a slice site, with the restricted coefficient ring; it does not assume continuous coefficients commute with arbitrary scheme pullback. Tensor sections need only admit local pure-tensor representatives. No objectwise tensor-sheaf equality, left exact tensor assertion, or flatness of N is used.

## Not duplicates

No new nodes, hence no new/existing-node pairs. Whole-DAG title and statement searches covered scalar extension, inverse-image tensor, tensor cokernels, constant exactness, finite presentations, finite bases and matrix normal form. blueprint_refs.py searches covered scalar extension, finite presentation, rational stratum, rational finite free, sheafification tensor, continuous field, Gaussian and finite basis. Existing general nodes were reused, including the exact sheafification/tensor theorem rather than creating a constant-tensor specialization, and continuous-field matrix elimination rather than creating another field elimination node.

## Mathlib searches

I ran the required msearch.py LeanFinder, Loogle, grep and LeanSearch commands, then a second LeanFinder phrasing and further Loogle/grep searches. The two semantic queries returned generic finite-presentation and local-generator declarations. LeanSearch returned instFinitePresentationTensorProduct, ModuleCat.extendRestrictScalarsAdj and localization tools. One Loogle query reported that SheafOfModules.changeOfRings is unknown; the next query found SheafOfModules.pullbackComp and its coherence lemmas. Source grep located PullbackContinuous.lean:167 and colimit-preserving presentation machinery in Quasicoherent.lean and Generators.lean. I read the pullbackComp source and the local finite-presentation definitions: these are useful general tools, but do not state the continuous coefficient model and every matrix clause here. All fresh queries and actual hits are appended to mathlib_searches and match searches.jsonl; no service failure was turned into a negative mathematical result.

## Review by Q97

I read Bhatt--Scholze section 6.8, especially Lemma 6.8.2, the paragraph before Definition 6.8.6, Definitions 6.8.3/6.8.6/6.8.10, Proposition 6.8.11(3) and the construction of Proposition 6.8.14(2). These distinguish locally finite free rational sheaves from integral local models by arbitrary finitely presented modules. The proof below makes the finite-presentation algebra explicit; it is marked agent-written, since the paper does not spell out these matrices. I read Stacks sites-modules.tex at Tag 03EI (lemma-sheafification-exact), Section 03EK (section-tensor-product), Tag 0GMW (lemma-sheafification-tensor), Tag 03EL (lemma-tensor-product-pullback) and Tag 03EP (lemma-tensor-commute-colimits). There are no new node statements whose sources require a separate audit.

Step 1 uses exactly the coefficient and immersion isomorphisms in lem-weil-pbc-continuous-coefficients-immersion-restriction. Its noetherian and finite-field-extension hypotheses are present; S is a locally closed subscheme, and the coefficient maps are those in the statement, not an arbitrary ring isomorphism.

Step 2 uses the actual pure-tensor formula and invertibility of lem-pur-proetale-inverse-image-tensor-comparison. The specialization has O=B_X, F=E_X and G=M. Step 1 supplies the required ring identifications. Substituting e=1 checks the unit, rather than inferring it just from existence of an isomorphism. The slice restriction is covered by the statement of lem-weil-pbc-ringed-topoi-module-pullback-tensor, which allows arbitrary ringed topoi and does not impose finite coefficients.

Step 3 uses the stated bilinear universal property of lem-pc-sites-sheaf-tensor-bilinear-universal. The two displayed maps respect precisely the B_S and A^c_S balancing relations; evaluating the two composites on pure tensors proves they are inverse. This is the elementary scalar reassociation calculation, with its maps supplied explicitly.

Step 4 uses the full presheaf-ring form of lem-pc-sites-module-sheafification-tensor, with constant presheaves A,E,N. Its conclusion really identifies the sheafification of their tensor with the tensor of the sheafifications. The second reassociation is checked on e tensor (a tensor n), using multiplication ea. The cited bilinear universal property supplies sheaf maps and uniqueness; this is not an appeal to an undefined constant tensor comparison.

Step 5 uses ordinary right exactness from lem-weil-pbc-tensor-right-exact, exact constant sheafification and matrix/finite-power coordinates from lem-sfb-constant-finite-free-presentation-extension, and cokernel preservation from lem-weil-pbc-independent-sheaf-tensor-colimits. I checked the statements individually: the constant-presentation node gives its exactness and matrix coordinates independently of flatness; only its additional left-injective short-exact assertion assumes flatness, and that assertion is not used. A cokernel is a finite colimit, within the size permitted by the last node. In particular this proof never asserts that A^m to A^n is injective.

Step 6 is the elementary quotient calculation for a supplied pair P,Q. Ring homomorphisms send their inverses to inverses. The maps on cokernels are [v] to tail(Pv) and w to [P^{-1}(0,w)]; PD=JQ^{-1} proves that relations vanish and that their composites agree with the identity. These formulas work with local representatives in the sheaf cokernel. On re-reading I corrected the wording for m=0: for arbitrary supplied P the resulting free-module map is induced by P, not necessarily the identity.

Step 7 cites only the statement of lem-weil-pbc-continuous-field-matrix-elimination, not an unexposed part of its proof. Taking its topological space to be one point gives an ordinary factorization over the normed field E, since the point's neighbourhood is the whole space. Inverting its invertible factors and absorbing reindexings gives PD_EQ=J. The statement explicitly includes empty index sets and rank zero. This is a specialization of an existing generic tool; it changes none of the unit's perverse-category route.

Step 8 uses the same general ringed-topos tensor comparison for slice restriction, and checks compatibility by the actual multiplication, constant-section and matrix formulas. Step 9 uses the witness clause of def-weil-pbc-continuous-constructible-module: the finite stratification and covers are already supplied, and the local E-module E^{n-rho} is finitely presented. The rational interpretation agrees with Bhatt--Scholze Definitions 6.8.3 and 6.8.6; over a field its finite-presentation models are finite free by Steps 5--7.

I tested N=0, N=A^r, N=A/(varpi^a), and N=A^r plus a finite torsion module. The torsion example rationalizes to zero because varpi^a is invertible over E; the free part has its expected rank. Empty schemes/strata introduce only vacuous local conditions. For m=0 one obtains a free cokernel of rank n; for n=0 or full row rank one obtains zero, and for the zero matrix one obtains rank n. None of these tests adds flatness or a common rank. The argument is local on each original covering object, so no global trivialization or uniform denominator is hidden in it.

Against delivery-errors B--E: there are no redundant new nodes, statement-only node faults, unlogged invented searches, duplicated notions or new statement hypotheses. Every proof citation has been read in its node statement and is quoted verbatim in citations.json. The two scalar maps and the block-cokernel argument are written out rather than moved into restatements of the item. Every non-elementary input is cited, no self-dependent realization functor is used, and all steps are under 2000 characters. Generic off-unit tools are declared in split_report.tool_uses for the maintainer's judgement; none replaces the unit's proof route. The statement dependencies and all inherited blueprint/import metadata are retained.

## Unfinished work

None in this stage-1 split. Its existing dependencies retain their own independent proof obligations. Server dry run and delivery are the final checks.
