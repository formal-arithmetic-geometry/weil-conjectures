# Stage-1 report

1. Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-source-augmentation-normalization.json (statement, split using seven existing proof dependencies; no Mathlib match), citations.json, report.md, and the required search log. No new nodes and no Mathlib leaves.
2. Attachments: none. The exact blueprint tag and the strictTower/reductionTower/completedExchange notions were searched throughout lean/WeilConjectures; no matching declaration was found. The additive Cech augmentation declarations concern a different construction.
3. WANTED: none.
4. The imported item had no proof. Its citation of reduction-pullback-derived-tower requires an inverse-image coefficient isomorphism, not merely the projection-defined structure map. This is a missing justification, not a false statement: profinite-coefficient-inverse-image gives precisely that isomorphism under the already present finiteness hypotheses. Step 1 now checks it explicitly. No statement or statement dependency was changed, and no additional hypothesis was imposed. The actual strict maps, witness transports and source comparison are retained.
5. Unfinished: none within this one-level stage-1 split. Existing cited statements remain separate DAG tasks where not already finished.

## Source and route

Read GOAL.md, the chapter and unit records, the three-level rules, stages/1-dag.md, the standing worker brief and delivery-errors B--E. The main-20261015 finite-extension proof's integral-lattice paragraph inherits coherence from integral level; the main-20261015 completed-exchange-coherence proof instructs applying derived inverse limit to strict tower equations with the same endpoint identifications. Read Stacks sites-cohomology.tex, lemma-derived-base-change (06YY), lemma-pullback-tensor-product (07A4), and remark-base-change (07A7). These give the ringed derived pullback and tensor comparison and the ambient unit/composition/counit mate. They do not themselves state this strict source normalization; the proof is correctly marked agent-written. No SGA source was used.

## Review by NQ

I read the complete statements of every node used in the five proof steps and checked them against the maps in the item, rather than treating a definition as an unspecified theorem. No new node needs a source review.

Step 1 uses profinite-coefficient-inverse-image for a countable tower of finite commutative rings. Here P_n is finite by the item, its quotient transitions are unital, and the schemes and sites are exactly those of the node. Its characterization by projections identifies its c_g with the structure map in completed-pullback. This supplies the ring-isomorphism hypothesis of reduction-pullback-derived-tower. That node explicitly states the augmentation equation and compatibility with coefficient transitions. This corrects my initial concern that the lemma was being applied without its coefficient hypothesis; no statement correction is necessary.

Step 2 uses completed-pullback's construction of gamma as derived inverse limit of the pulled strict quotient augmentation following the constant-tower map. Rlim-functoriality supplies an actual functor. Combining that definition with the augmented identity in step 1 proves j gamma = u by composition; it does not assert gamma is invertible. S is the specified F(A_bullet), not a replacement chosen from an arbitrary cone.

Step 3 reads completed-base-change-map's displayed definition of s and strict-tower-exchange-mate-normalization's description of H as the pulled diagram-site projection formula map. The former uses the pulled reduction source A_bullet; the latter uses the reduction of M, so their source normalization is exactly tau_g inverse. Consequently H tau_g = h_bullet before applying Rlim. This is composition of the prescribed maps, not the invalid assertion that evaluated maps determine every derived-tower arrow. Rlim-functoriality then gives s = F(H)j. Both nodes use the same witness transports and projection maps.

Step 4 uses adic-coefficient-datum's actual left derived strict quotient functor, hence the derived tensor bifunctor with the fixed quotient-algebra map. Tensor interchange gives naturality of i in arbitrary derived e. The constant-map construction is also natural: the compatible-family map into a functorial K-injective tower resolution commutes with complex maps, and it descends through localization, so it commutes with derived morphisms as well. The functorial resolution in Rlim-functoriality is the one fixed in the item. These are the two explicitly written equations which give F(R(e))u_M = u_N e; no exactness of a countable product or faithfulness of evaluation is invoked.

Step 5 uses the normalization node's actual displayed conjugation formula for v'_bullet, not only its final constant-coefficient mate comparison. Cancel H inverse followed by H, apply the derived-limit functor, and substitute steps 2--4. This proves exactly the last equality. No cancellation of e, v'_bullet or gamma is used. The item assumes completeness of C as well as K, so the definition of its completed source is available. Properness and the retained etale-origin witnesses are precisely the hypotheses of the strict-exchange normalization and the completed map. All derived objects stay in the completed coefficient categories used in the item.

Every proof citation has a verbatim supporting quote in citations.json. The proof has five steps, each shorter than 2000 characters; none conceals a new standard lemma. All arguments are naturality, identification of specified composites, or application of existing statements, so creating separate augmentation/naturality nodes would create elementary or clause duplicates. No off-unit tools are needed.

I tested K=0 (all displayed composites are zero), identity g (tau is the unit-normalized identity comparison), I=0 and I=A (constant or zero quotient diagrams, respectively, with derived completeness interpreted as in the item). For a nonzero test take A=Z_ell, I=(ell): P_n is finite perfect, but gamma need not be assumed invertible on an arbitrary pulled object. The computation still uses only H inverse, already supplied by the projection comparison. Unbounded complexes cause no bounded-resolution step. Finite rings can have noninjective quotient maps on modules; the argument uses naturality, never an injectivity assumption.

## Searches and duplicate check

Reused the existing item's recorded searches as history and added five actual msearch.py calls: leanfinder on derived pullback and quotient augmentation, loogle on SheafOfModules/pullback, grep of CategoryTheory for strict/completed reduction names, leansearch on augmentation naturality, and a second leanfinder phrasing on the completed source comparison. Read all hits: they concern ordinary module pullback, tensor/limit constructions, ordinary adic completion, sheafification naturality or affine-scheme pullbacks. None states the item's strict derived-tower equation. Exact new query texts and returned hit summaries are in mathlib_searches and searches.jsonl.

Searched the whole imported blueprint with blueprint_refs.py for augmentation, reduction pullback, completed source, and quotient augmentation, and searched DAG statements by those notions. The nearby completed-Frobenius-structures and intrinsic/Koszul completion nodes do not state the item. Reused the existing profinite coefficient and strict normalization nodes; no new node was created.

## Not duplicates

No new nodes.
