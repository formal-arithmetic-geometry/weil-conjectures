# Stage-1 report: lem-weil-pbc-flat-scalar-restriction-kflat

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-scalar-restriction-kflat.json: statement item, split into six proof steps; no Mathlib match for arbitrary sheaves of rings on a small site.
- citations.json: verbatim statement excerpts for every step/node citation.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and scalar restriction/K-flat terminology found no declaration giving both clauses for arbitrary ring sheaves. The proved ModuleCat.kFlat_restrictScalars_of_isLocalization concerns ordinary modules over a localization, not general sheaf modules; CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat concerns scalar extension of ordinary complexes. Neither attaches to this item.

## WANTED

None: the Stacks sources used are present locally.

## Corrections and provenance

The statement and both its clauses are unchanged. The unused statement dependency def-weil-abstract-derived-category was removed: this statement is about complexes, not derived categories. The original reference to 06YY supplies context for K-flat scalar change, but it does not itself state the flat-restriction assertion. The proof is therefore explicitly agent-written, using the literature-backed interfaces below, rather than attributed wholesale to 06YY. No imported blueprint field or unit/chapter record was changed.

The blueprint search used blueprint_refs.py ancestor and searches for K-flat, scalar restriction, restriction of scalars and tensor product, together with a whole-DAG statement/title scan. No blueprint node states the full assertion. The nearest blueprint ancestor is def-weil-pbc-completed-pullback, current main-20261015 order 1329. I read its current source statement and the chapter and unit records: this item supplies the restriction of K-flat representatives inside the constant/completed coefficient comparison; it does not replace any unit step.

The existing ordinary-module lem-pc-tensor-restrict-extend-scalars cannot be applied to sheaves. The completed finite-coefficient lem-weil-restriction-of-scalars-exact is also too specialized. I instead use the general module-sheaf forgetful theorem and write out the balancing construction with existing sheaf universal properties. The more recent lem-weil-pbc-scalar-tensor-comparison-universes gives naturality for a fixed R-module sheaf; the split does not silently take two-variable naturality from that statement.

## Mathlib searches

All six additional searches were run with the prescribed msearch.py and are in searches.jsonl. The original item searches are retained. LeanFinder was queried with two different descriptions, Loogle with the KFlat/restrict pattern, LeanSearch with the sheaf-algebra formulation, and grep with the K-flat/restrict pattern and a second search of Algebra/Category/ModuleCat/Sheaf. All services answered. The hits Module.Flat.trans, flat ordinary scalar extension and exact tensor for ModuleCat concern ordinary modules. The sheaf grep returned no flatness/K-flatness declarations. These do not make the arbitrary ringed-site assertion a one-line Mathlib specialization. No search or unavailable service was invented.

## Review by Q22

I read sites-cohomology.tex definition-K-flat (06YN), the statement and proof of lemma-derived-base-change (06YY), and sites-modules.tex section-tensor-product (03EK), lemma-abelian (03DA), lemma-limits-colimits (03DB), definition-flat item (3) (03ER), and the sheafified tensor discussion at lemma-sheafification-tensor (0GMW). I also read homology.tex lemma-exact-functor (010N). There are no new-node sources to review. I opened the statement of every cited node, rather than taking facts from its proof.

Step 1 uses def-pc-sheaf-restrict-scalars for the unchanged abelian sheaf, lem-weil-pbc-module-sheaves-colimits-forgetful for faithfulness, exactness and small-colimit preservation, and lem-weil-pbc-exact-functor-complex-cohomology for termwise homology. Their statements give exactly these facts for a general site with abelian sheafification. The small-site hypothesis guarantees the usual sheafification in a module universe large enough for the site, and the diagonal sums are small. Detection of zero objects is written as faithfulness applied to the identity. This supplies exactness and acyclicity detection without assuming that the site has enough points.

Step 2 uses lem-weil-pbc-extension-tensor-comparison, whose statement is the natural restricted scalar-extension/tensor isomorphism for an arbitrary map of ring sheaves; lem-pc-sheaf-modules-tensor-closed supplies symmetry for its order. def-pc-flat-sheaf-modules is precisely exactness of the sheaf tensor functor, not sectionwise flatness. The cohomology node then applies because E has been proved exact between the abelian sheaf-module categories. This establishes preservation of all acyclic complexes without boundedness. I do not cite only the definition of flatness for preservation of complex cohomology.

Step 3 uses def-pur-sheaf-tensor-product and def-pc-sheaf-restrict-scalars to identify the objects. lem-pc-sites-sheaf-tensor-bilinear-universal gives existence and uniqueness of maps from sheaf tensor, and lem-pc-sites-module-sheafification-bilinear-extension gives extension of bilinear section pairings through the inner sheafification. Both statements apply on a general site; no scheme hypothesis is smuggled in. I explicitly give the B-action on the inverse map's target, both maps, the R- and B-balancing equalities, their composites, and why uniqueness gives naturality in both variables. This is a short calculation from those universal properties, not an unsourced comparison lemma or a new node duplicating a clause of the item.

Step 4 uses def-pc-tensor-complex-sheaves for the direct-sum totalization with differential d_A tensor 1 plus (-1)^p 1 tensor d_P; the colimit-forgetting statement and the scalar-restriction definition justify passing U across each small sum. The exact differential square is written, including its sign. Its verification reduces to the pure-tensor uniqueness established in Step 3. No product totalization, boundedness, or unproved convergence assertion occurs.

Step 5 invokes def-pc-kflat-complex only for its stated acyclic-tensor test. All other inputs are already proved in Steps 1–4: extension preserves the acyclic test complex, restriction preserves acyclicity, and the two total complexes are explicitly isomorphic. Thus this step does not smuggle flat terms into the K-flat hypothesis.

Step 6 uses def-pc-flat-sheaf-modules and applies the three already justified exact functors in order, then uses naturality of the Step 3 isomorphism. The extra assumption on each P^q is used precisely here. The argument verifies the functorial exactness required by that definition, not just vanishing after a single tensor.

The off-unit tools are declared in split_report.tool_uses: generic symmetric closed sheaf tensor, the bilinear universal property, and bilinear sheafification extension. These are general-purpose inputs; they do not replace a route prescribed by the proper-base-change unit. No new nodes exist, so there are no new/same-tag pairs requiring a Not duplicates table. Every citation has a verbatim quote in citations.json. All six steps are shorter than 2000 characters; the longest is the explicit balancing calculation.

I checked identity coefficient maps, zero complexes, the zero coefficient algebra, and the empty site; all constructions and conclusions still apply. Unbounded complexes use direct sums on every total diagonal, as required. Flatness of B is essential: on the one-object site, Z to F_2 with P=F_2 in degree zero is K-flat over F_2, but restriction fails the K-flat test against the exact complex 0 -> Z --2--> Z -> F_2 -> 0. Its tensor with F_2 has nonzero leftmost homology. Thus the split does not accidentally prove a stronger false assertion. No statement dispute was found.

## Unfinished work

None at the requested one-level stage-1 split. No Lean was written and no compiler or build tool was run. Server review_split passed before packaging (0 new nodes); full delivery dry-run results are reported by deliver.py.
