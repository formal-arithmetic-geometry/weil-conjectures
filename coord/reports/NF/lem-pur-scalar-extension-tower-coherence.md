## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-scalar-extension-tower-coherence.json` (statement, split; no Mathlib match), `citations.json`, and this report. The original statement, statement dependencies, source and maintainer metadata are retained. Nine proof steps replace the empty imported proof. No unit realization is changed: this item is not the unit's key node.

## New nodes

None. No Mathlib leaves are created.

## Attachments

None. Searches for the exact blueprint tag and for scalar extension, pullback and tensor in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration stating all the strict quotient-system, transition, extension-tower and limit clauses. In particular `AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`, `SixFunctors/ProEtale/ScalarExtension.lean:68`, supplies only the ordinary sheaf comparison. The upstream master tree was searched for the tag too, but its sorry declarations are not proof evidence.

## Sources and blueprint

Read the chapter record `sec-smooth-purity`, unit `sk-def-purity-conv`, the current main-20261015 definition `def-weil-derived-pullback-tensor-hom` (integral operations and compatible coefficient constructions), and the actual ancestor `def-weil-frobenius-coefficient-twists` (last sentences, compatibility with reduction and scalar extension). The item is an agent-extracted supporting calculation for former step 6 of `lem-pur-derived-pullback-tensor-iso`; the ancestor's much shorter statement is not presented as a published proof of this strict tower assertion.

Read Stacks `sites-cohomology.tex`, Tag 07A4, label `lemma-pullback-tensor-product`, including its K-flat totalization proof and its ordinary constituent `sites-modules.tex`, label `lemma-tensor-product-pullback`. These give the finite tensor-pullback construction, not the whole integral tower argument. Read Bhatt--Scholze, *The pro-etale topology for schemes*, PDF pp. 22--24, Definition 3.4.10, Lemma 3.4.12 and Proposition 3.5.1, for completion and compatible quotient systems. The proof is marked agent-written because its strict representatives and equations are the explicit refinement of those constructions, rather than a verbatim theorem of these sources. No SGA source is used.

WANTED: none. Nothing remains unfinished in the one-level split; cited unsplit statements remain tasks of the DAG, as intended.

## Searches and reuse

Read all five new `msearch.py` results in `searches.jsonl`: LeanFinder and LeanSearch for strict quotient models and scalar extension, Loogle `ModuleCat.extendScalars, TensorProduct`, grep for base-change composition/tensor/towers, and a second LeanFinder phrasing on inverse quotient systems and towers of ring extensions. Preserve the item's inherited searches; append only these actual queries with their results and verdicts. All five services returned successfully.

Read the relevant Loogle candidates in Mathlib: `ModuleCat.extendScalarsComp` and `extendScalarsComp_hom_app_one_tmul`, `Algebra/Category/ModuleCat/ChangeOfRings.lean:984,1006`, and `ModuleCat.extendScalars_δ`, `extendScalars_δ_tmul`, `Algebra/Category/ModuleCat/Monoidal/Adjunction.lean:101,109`. They concern ordinary modules, not coherent quotient towers of sheaf complexes with their derived-limit interpretation. The semantic hits for `SheafOfModules.pullbackComp` and algebra pushouts likewise omit the actual finite tensor square and completed coefficient construction. Thus the whole item is not a Mathlib leaf.

Searched the entire DAG by Tag 07A4 and scalar-association/tensor/quotient-coherence phrases. Ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `scalar extension`, `quotient tower`, `coefficient square`, and `successive extension`. No blueprint statement states the whole item in another form, so `same_as` remains `[]`. Existing general nodes are reused, especially `lem-pur-cochain-pullback-tensor-coherence`, `lem-pur-coefficient-extension-reduction-model`, and `lem-pur-completed-operation-tower-substitution`. There are no new-node duplicate pairs.

## Corrections and limitations

No statement correction or dispute was needed. The previously empty proof concealed several distinct requirements: K-flat derived interpretations; honest quotient maps rather than arbitrary isomorphisms of reductions; the finite scalar/tensor square; strict compatibility of inverses with transitions; further-extension coherence; and identifying the limits with completed operations. They are now separately addressed. During self-review, the last identification was strengthened by explicitly citing `lem-pur-completed-operation-tower-substitution`; definitions of completed operations alone do not justify substitution of arbitrary normalized systems.

The scalar-extension comparison of the existing integral-operations theorem is used with its canonical scalar-association normalization; its existential assertion does not imply uniqueness of all natural isomorphisms. The proof constructs the canonical maps here, and makes no such uniqueness claim. Identity assertions are under the action unitors, not literal syntactic equality of distinct tensor representatives. The original text already has this usual categorical meaning.

The off-unit tools are declared in `split_report.tool_uses`: preservation of K-flat complexes under ringed-topos pullback, the derived-limit functor on strict towers, and the integral scalar-operations comparison. They do not replace any geometric purity route. The unit directly cites the coefficient-operations unit; definitions remain definitions, not sources of uncited non-elementary facts.

## Review by NF

I read the node and its cited statements against the sources named above. There are no new nodes whose sources or hypotheses need a separate review. The statement retains arbitrary scheme morphisms with the prime invertible and allows ramified finite coefficient extensions. Every complex is interpreted in the ambient derived module category; a K-flat representative is not required to have constructible terms.

Step 1 uses exactly the preservation statement of `lem-pur-kflat-change-of-rings`, the flat-term K-flat total-tensor assertion of `lem-pur-kflat-total-tensor-model`, and the ringed-topos pullback preservation theorem. I checked the latter needs a morphism of ringed topoi and a flat-term K-flat input, which the inverse-image definition and the hypotheses provide; it does not require flatness of the coefficient map. None of these dependencies reaches this item.

Step 2 uses the actual quotient maps in the integral scalar-extension definition, tensor balancing from the sheaf tensor definition, and the exact scalar-association formula and normalization assertion in `lem-pur-coefficient-extension-reduction-model`. Its displayed inverse and the reduction calculation show that these are the theorem's simultaneous maps, not newly chosen level isomorphisms. That theorem permits arbitrary derived input and ramification.

Step 3 writes both directions of kappa using the ring maps in `def-weil-proetale-inverse-image`. Naturality in a coefficient ring follows directly from the constant-section prescription in that statement and uniqueness in its sheafification adjunction. The scalar relation is checked by balancing in the cited tensor definition. This step is elementary: no new pullback base-change theorem is hidden here.

Step 4 uses the chain-level isomorphism in `lem-pur-cochain-pullback-tensor-coherence`, specialized both to a change of rings on the identity topos and to f. I checked its statement applies to arbitrary unbounded complexes, gives both inverse formulas and specifies the signed differential. The separate tensor-complex definition supplies precisely the direct-sum total and sign used here.

Step 5 uses that same lemma's explicit coefficient-square clause, not just its composition clause. I checked it says that the scalar-extension square commutes as chain maps. The proof also calculates each route on a homogeneous pure tensor and explains why balancing and sheafification extend the equality. It does not cite the proof of another node as if it were its statement.

Step 6 proves transition compatibility by reducing the actual coefficients and sections, with products reducing to products. It uses only the coefficient maps of the scalar-extension definition and the cochain lemma's stated strict-transition compatibility. The inverse maps satisfy the same multiplication identity. This is elementary after the established formulas, not a new lemma about derived limits.

Step 7 checks identity under the action unitors and successive extension with the explicit contraction d tensor (b tensor x) mapping to d*j(b) tensor x. I checked that the reduction-model theorem states exactly the coherent counit transitivity used in the last sentence. The rest is the elementary equality of these multiplication formulas; no claim of finite coefficient flatness enters.

Step 8 uses the reduction-model theorem for scalar-extended inputs, and the substitution theorem for the whole pullback and tensor systems. I opened the latter and checked that it explicitly states normalization, naturality in system maps, and identification of coherent reductions including transitions, for arbitrary normalized systems. This repairs the possible gap between a limit definition and a claim about its reductions. The integral-operations definition specifies the actual finite constructions; the integral scalar-operations theorem supplies the named existing interfaces. We select their canonical scalar-association comparison, rather than infer its value from existence of an unspecified isomorphism.

Step 9 uses the strict-tower homotopy-limit theorem's exact functor on D(Tow(Mod(O))). Restriction makes the towers live over the same completed L-ring; compositions, identities and inverse maps are already strict. Functoriality therefore suffices; exactness of ordinary inverse limit or commutation of tensor with arbitrary limits is not asserted.

For edge cases I checked zero complexes, f the identity, the unit object in degree zero, and generators of arbitrary degrees p,q (including negative degrees and unbounded totals): no factor is permuted, hence the only sign remains (-1)^p. For E=L possibly with a different chosen uniformizer, powers generate the same ideals and the canonical quotient identifications give the same unitors. For a ramified extension with varpi_E a unit times varpi_L^e, e>1, the map at the same index exists because (varpi_E^m) is contained in (varpi_L^m); all calculations use that actual map and allow its kernel. No step identifies B_m with a flat A_m-algebra. Taking one of the further extensions to be the identity leaves the multiplication formulas unchanged. Each non-elementary step is below 2000 characters; none hides a new supporting claim beyond the existing cited statements.

The citation file contains a verbatim excerpt for every cited node at every step. The dependency union is exactly the union of `uses`. All changes are in this item's sandbox, no Lean was written or compiled, and no agents were started. Mechanical dry-run and push outcomes are recorded below when obtained.

Repair revalidation (2026-10-17): the delivery was returned because the reviewed dependency `lem-pur-cochain-pullback-tensor-coherence` had since acquired its explicit `epsilon`, `kappa`, and `tau` coefficient-square and quotient-transition formulas. I rebased the citation view against the current DAG statement, replacing the stale generic quote at steps 4--6 with verbatim excerpts of the current statement: step 4 quotes its unchanged total-complex comparison, step 5 quotes the named scalar-association/transition maps and displayed equations, and step 6 quotes the final strict quotient-tower transition sentence. I re-read the current dependency statement and checked every citation quote in `citations.json` as an exact substring of its cited node; no proof text or dependency list needed alteration.
