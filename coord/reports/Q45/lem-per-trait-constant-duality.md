## Worker report

1. Files written:
   - dag/nodes/sec-deligne-laumon-a1/lem-per-trait-constant-duality.json: item, statement unchanged, nine proof steps, status split.
   - dag/nodes/sec-deligne-laumon-a1/lem-per-localization-dual-boundary-pairing.json: statement, unsplit; no Mathlib match. This is the only new node and has no proof or proof dependencies.
   - report.md and citations.json: direct-delivery self-review and verbatim step citations.
2. Attachments: none. Searched the entire project WeilConjectures tree for the exact blueprint id and for trait/strict-henselian/duality notions. Read SixFunctors/Etale/Derived/Dualizing.lean: its general theorems are sorry and are over finite-type schemes over a field, so are neither finished proofs nor statements of this trait assertion. The boundary-duality source supplies no exact attachment either. The upstream master is not used as proof evidence.
3. WANTED: none. The ILO PDF and Stacks sources required below are available locally.
4. What was wrong: the item was statement-only, with its nontrivial dimension-one duality argument not exposed. Its statement agrees with the intended finite-field trait assertion and is preserved byte for byte. Excellence is retained although the tame model does not require it. No completeness, mixed-characteristic or finite-type-over-a-field hypothesis was added. No source error or statement dispute was found.
5. Unfinished: the new boundary-comparison lemma is deliberately unsplit, as required for a one-level split. The item has a full argument conditional on exactly its named smaller inputs. No Lean was written and no compiler or Lake tool was run.

## Searches and route

Read the chapter sec-deligne-laumon-a1, unit sk-p-dl-a1-perverse, item and the parent lem-per-complete-trait-constructible-biduality. This is the dimension-one tame-inertia base case recorded in the item's ancestry, not a proof via potential dualizing objects or absolute purity. No SGA source is used. I read the current blueprint ancestor relation with blueprint_refs.py ancestor and searched the whole blueprint for trait, duality, biduality, open/closed, support and localization/evaluation; searched the whole DAG for inertia, cohomology pairing, boundary transposition and relevant source tags. The existing trait-residue-model and prime-power-trait-generic-boundary-model are reused, the latter at exponent one. Their statements give a coefficient-independent natural sign for the localization boundary and the actual crossed-homomorphism comparison. The finite-dimensional perfectness calculation is a step, not another node.

Mathlib queries were made exclusively with the authorized msearch.py wrapper, whose exact log is searches.jsonl. The item's fresh queries return constant-sheaf declarations, FGModuleCat.exactPairing, valued fields/DVRs or algebraic etale loci, not sheaf duality on a trait. The new lemma's two semantic phrasings, LeanSearch, Loogle and source grep return abstract Ext connecting maps, triangle constructors, derived adjunctions, or ordinary algebraic localization. I read these displayed signatures: the Ext boundary formulas do not compare sheaf internal-Hom localization with cup followed by a support boundary. No one-line specialization states either requested result. Existing searches imported on the item were preserved; they are not claimed as fresh Q45 calls. All fresh entries match the tool and query strings in this item's actual log. No unavailable service was recorded as no match.

Off-unit uses are explicitly declared in split_report.tool_uses: ordinary field-site classification, preservation of injectives, stalk exactness/conservativity, internal Hom restriction, and the generic exact/truncation triangles. They are categorical or sheaf-theoretic infrastructure. None replaces a geometric step of the unit.

## Review by Q45

I read ILO Expose XVII 1.2.1–1.2.3, printed pp.259–262 (PDF pages 265–268), including the free augmentation ideal, the three-column model and the generator normalization. This text provides the actual complex, not a general biduality theorem, so the item's proof_origin is agent. I also opened Stacks sites-cohomology.tex lemma-RHom-triangulated, Tag 08JC (line 8948), and the nearby evaluation construction, including lemma-internal-hom-evaluate, Tag 0A97 (line 8965). Tag 08JC only says Hom takes triangles to triangles; it is not misrepresented as the new boundary comparison. The new lemma isolates the further formal comparison of specified arrows. Its source place and this report explicitly distinguish that agent-supplied comparison from a verbatim Stacks theorem. It is not a duality theorem, assumes no perfect boundary pairing and concludes no invertibility.

Step 1: I checked trait-sheaf-gluing really states triples, componentwise kernels/cokernels and the closed-stalk global-section identification. The field G-set classification supplies the finite covering orbit trivializing a finite continuous representation. The constructible-complex definition gives exactly the two finite locally closed strata. Finite-dimensional kernels, cokernels and extensions supply the elementary closure argument here; no unrelated pro-etale closure statement is substituted.

Step 2: The prime-power generic-boundary node states C(K), its cohomology interpretation, and RΓ(T,K)=K_s. Its n=1 specialization has exactly this coefficient ring. The residue-model node states the three-term F and its exactness; for the constant representation its first map is identity and second zero. The closed-sheaf internal adjunction states the support-kernel right adjoint and preservation of injectives. Thus on the separably closed closed point its derived value is precisely the supported complex. The general injective-preservation node applies because open inverse image is exact; using an injective resolution gives i*Rj*L=RΓ(eta,L) without silently assuming proper base change. I checked boundedness of Rj* before the bounded-K Hom localization theorem is ever applied to it.

Step 3: I opened both the generic-boundary statement and augmentation-cocycle statement. They say respectively epsilon_0 times the degree-two column and f_c(1-sigma)=-c(sigma). Their combination gives the stated negative sign. Only its being a unit is used. This step does not cite the Gysin-residue node or a purity-normalized equality. It is an elementary specialization of exactly those two statements.

Step 4: The residue-model statement provides the canonical wild averaging projector, and the generic model is natural for coefficient maps. The inverse between invariant duals is restriction versus precomposition with this projector. Cup with a degree-zero invariant is the coefficient map on degree-one cocycles, so no unproved multiplicative comparison between arbitrary resolutions is assumed. For a finite W the annihilator of (1-t)W is ker(1-t^{-tr}) on W-duals, and rank-nullity identifies im(1-t^{-tr}) with the annihilator of ker(1-t). These two elementary linear-algebra identities prove both required perfect pairings. A bounded finite-dimensional complex splits by complements, so this also proves the claimed derived-map invertibility. This step is under 2000 characters and has no hidden geometric duality input.

Step 5: The Hom-localization statement applies to bounded i_*W and degree-zero A_T, with no constructibility or ambient-dualizing hypothesis. The generic term vanishes, giving its displayed closed Hom. The gluing statement identifies i*i_*W=W. I checked that the line A(-1) and the shift -2 cancel on taking the double dual, and that the map being tested is evaluation, not merely an arbitrary isomorphism. Choosing a basis proves evaluation invertible, also after either shift sign. The exact/conservative stalk statements test this on cohomology.

Step 6: The same Hom triangle for j_!L has i*j_!L=0 by the extension-by-zero stalk statement. The ringed-site exact restriction theorem says internal Hom on any slice is its restricted internal Hom, without extra finiteness hypotheses. A finite free local presentation makes its higher Ext vanish and gives L-dual. The resulting Rj_*L-dual is bounded constructible by step 2, including ramified L; no assumption that L extends lisse over T occurs.

Step 7: I checked every input of the new comparison at K=Rj_*L: A is finite, L is finite locally free over the field A, K was proved bounded in step 2, and N=A_T is bounded below. Its conclusion identifies i*u with precisely the transpose of cup/evaluation/b, up to a single convention sign. Step 4 proves that map invertible; the restricted triangle then kills the closed stalk of D(Rj_*L). Open restriction identifies its generic object. The open/closed sequence extended to complexes (using the cited short-exact-complex triangle) identifies the resulting object with j_!L-dual. I did not assume this object or any dualizing complex a priori. The extra lemma is strictly smaller: it only identifies two maps on arbitrary X and asserts no nondegeneracy, no preservation and no biduality, so does not restate the item or one of its substantive conclusions.

Step 8: The natural evaluation bidual map has zero closed source and target and ordinary double-dual evaluation on the generic slice. The cited relative-bidual theorem specifies this actual map and its naturality. Stalk exactness and conservativity imply it is an isomorphism. An abstract isomorphism D²j_!L ≅ j_!L alone would not have sufficed; the proof explicitly tests eta.

Step 9: The open/closed short-exact statement explicitly includes modules over every commutative ring, so applies to A, and the complex-ses triangle statement gives the extension triangle. The truncation statement provides the finite cohomological induction. The relative-bidual theorem states the natural transformation is compatible with the connecting arrow as well as shifts and that its isomorphism locus is triangulated. This is the exact compatibility used; I have not taken compatibility from a definition. The same finite-stalk argument proves bounded-constructible closure of all D-images during induction. Thus the three clauses defining dualizing are all covered.

For the new node I checked B1–B7: statement only, every object introduced, finite locally free defined inline, scheme/immersion/ordinary coefficient categories and Hom/tensor definitions cited, source tag with actual label, single-escaped TeX, and no Mathlib match claimed. The comparison is meaningful also with zero C or E, no perfectness assumption, and boundedness of Rj_*L explicitly stated rather than inferred in arbitrary dimension. I have read the named internal-Hom localization statement; it constructs its arrows from the open/closed extension triangle, which is why this new arrow comparison is the required missing assertion rather than a duplicate of that statement.

Small cases: L=0 and W=0 give zero maps between zero objects. For V=A with trivial inertia, C(V) has A in degrees 0 and 1, and its pairing has exactly the two off-diagonal nonzero evaluations, so the shift is [-1] in E[1], not [-2]. For ell=2 the unit signs coincide and perfectness is unchanged. For a nontrivial unipotent tame action t=[[1,1],[0,1]] on A² in characteristic ell, kernel and cokernel are both one-dimensional and both evaluation pairings remain nonzero. For a tame scalar t≠1 both kernel and cokernel vanish. If the wild-invariant part is zero, the averaging dual also has zero invariant part, so both generic cohomology complexes vanish. The new comparison with U empty has L=K=C=C'=0; with Z empty both sides are zero on Z. None of these cases requires perfect residue field, completeness or mixed characteristic.

Corrections during self-review: retained the negative sign in augmentation-to-cocycle coordinates; distinguished the support right adjoint from the statement's internal-Hom dual; established boundedness before applying Hom-localization to Rj_*L; added explicit scheme and image-functor definition dependencies to the new statement. Kept the canonical evaluation-map test and isolated the non-elementary boundary comparison. All nine proof steps are below 2000 characters. citations.json contains an exact verbatim statement quotation for every node listed in every step's uses, so each use can be checked against the actual public statement.

## Not duplicates

lem-per-localization-dual-boundary-pairing vs lem-coef-etale-hom-thick-locus: the existing node states Triangulated compatibility of the evaluation-defined scalar Hom comparison; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-coef-integral-hom-reduction: the existing node states Integral internal Hom and reduction; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-coef-rational-bidual-triangle-compatibility: the existing node states Coefficient biduality map is compatible with shifts and triangles; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-coef-rational-retract-evaluation: the existing node states Evaluation on retracts and extension of a perfect pairing; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-per-bounded-above-rhom-hyperext: the existing node states Finite-diagonal hyper-Ext spectral sequence in the bounded-below second argument; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-per-constructible-ext-filtered-colimit: the existing node states Sheaf Ext from a bounded-above constructible etale complex commutes with filtered colimits; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-per-etale-internal-hom-localization: the existing node states Etale internal Hom localization triangle for arbitrary coefficients; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-per-relative-bidual-triangles: the existing node states Relative evaluation biduality respects distinguished triangles; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-pod-coefficient-dual-perfect: the existing node states Perfectness is preserved by coefficient duality; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-pur-external-rhom-cone-pairing: the existing node states External global derived Hom evaluation respects coefficient cones; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-pur-supported-product-localization: the existing node states Supported exterior products respect localization triangles; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-double-hom-cone-comparison: the existing node states Signed double-Hom comparison with a mapping cone; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-etale-generic-exchange-algclosed: the existing node states Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-etale-generic-hom-triangle: the existing node states Internal-Hom comparison respects the finite stratification triangles; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-etale-local-dual-interval: the existing node states Uniform local models and Tor interval for a twisted coefficient dual; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-even-line-hom-shift: the existing node states Signed first-variable shift compatibility of the internal-Hom line comparison; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-hom-triangulated: the existing node states Exactness of the internal Hom in each variable; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sf-rational-thick-evaluation: the existing node states Triangulated closure of the rational evaluation class; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sfb-constructible-internal-hom-continuity: the existing node states Bounded-below continuity of constructible derived internal Hom; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-sfb-finite-field-internal-hom-finiteness: the existing node states Finite-field internal Hom finiteness over an arbitrary ground field; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-trf-external-hom-thick-reduction: the existing node states Exactness and shift compatibility for the external Hom thick reduction; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-duality-pairing: the existing node states The duality pairing and the double-dual morphism; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-integral-constructible-triangulated: the existing node states Bounded constructible derived-complete integral complexes form a triangulated subcategory; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-pbc-ringed-complete-element-addition: the existing node states Sum of complete local sections is complete; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-pbc-ringed-complete-element-multiplication: the existing node states Multiples of complete local sections are complete; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-pbc-ringed-derived-complete-elements-ideal: the existing node states Vanishing localizations form an ideal; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing node states Derived internal Hom calculus on small ringed sites; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-zl-lisse-cohomology-derived-dual: the existing node states Cohomology of the coefficient dual of a lisse-cohomology complex; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs prop-sf-dualizable: the existing node states Perfect complexes are dualizable; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs sk-thm-sf-kunneth-verdier: the existing node states Künneth–Verdier isomorphism; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs thm-coef-integral-verdier: the existing node states Integral Verdier biduality; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs thm-sf-dual-perfect: the existing node states The dual of a perfect complex; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs thm-trf-internal-hom-pullback: the existing node states Internal Hom versus pullback for a site-perfect first variable; this new node identifies the dual open/closed connecting map with cup/evaluation followed by the support boundary, and asserts no perfectness or biduality.

lem-per-localization-dual-boundary-pairing vs lem-weil-closed-costalk-duality: the existing node identifies Ri!D with D_Zi*, not the connecting map after closed restriction of the open/closed dual triangle.

lem-per-localization-dual-boundary-pairing vs lem-per-trait-residue-model: the existing node computes supported cohomology and a specialization map on a trait; it does not identify an internal-Hom boundary for arbitrary X with a cup pairing.

lem-per-localization-dual-boundary-pairing vs lem-per-prime-power-trait-generic-boundary-model: the existing node identifies the generic complex and its ordinary localization boundary; it does not identify the transpose of the internal-Hom boundary.

## Validation

Server review_split preliminary check passed. Required deliver.py dry run and final push follow this report; their stdout is the authoritative delivery result.
