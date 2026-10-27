# Stage-1 report: def-sfb-ringed-site-module-cup-product

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-ringed-site-module-cup-product.json: definition, split; no Mathlib match for the full ringed-site construction.
- citations.json: empty list, because this definition has no proof steps.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. The definition split is the constituent-notion audit required by stages/1-dag.md section 3(2); it is not a theorem split and does not require invented proof steps.

## Attachments

None. The exact blueprint tag is absent in lean/WeilConjectures. I searched that tree for cupProduct, cup product, and the item id. AlgebraicGeometry.Etale.cupProductAux in EtaleCohomology/PoincareDuality/TraceCup.lean, lines 92–104, is a product of constant-coefficient endomorphism classes on a scheme etale site, not the arbitrary-module relative and global construction here. CategoryTheory.Adjunction.rightAdjointCupProduct in CategoryTheory/Adjunction/ProjectionMapCupProduct.lean, lines 72–75, supplies a generic categorical construction but does not state the ringed-site derived, cohomology-sheaf, and global clauses. Neither is an exact attachment for the item.

## WANTED

None. All sources used are in the repository.

## Findings and changes

The original definition matches the relative cup construction of Stacks Tag 0B6C (sites-cohomology.tex, remark-cup-product) and its global specialization in Tag 0FPJ (section-cup-product). Its implicit derived infrastructure was not fully named in stmt_deps. I added existing owners for the canonical derived adjunction and tensor comparison, K-injective complexes, K-flat tensor descent, global sections, unbounded derived sections, the coefficient-universe convention, and the scheme etale site. The cohomology pairing now specifies the local-cocycle prescription, the previously free letters P,Q are explicitly instantiated, and the map from derived to ordinary tensor is specified using resolution augmentations. This explicates the same maps; it does not change the relative/global product, coefficient rings, module category, or geometric scope. The existing ancestor chain and blueprint.from.node=null are preserved: tools/blueprint_refs.py ancestor reports None for this live item.

The newest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, particularly (3). The item is an auxiliary notion far below the alteration/Picard branch already recorded in its provenance, not the unit key statement. The on-disk chapter and unit records were read; none is edited and no route is replaced.

I searched the entire DAG and imported blueprint with blueprint_refs.py search for cup product and ringed, and inspected related module-cup nodes. def-sc-module-cohomology-cup-product is restricted to schemes and global ringed-space cohomology; it does not own this arbitrary-site relative construction. Constant-coefficient and mixed-support cup products likewise have different domains. No new duplicate nodes are introduced. Mathlib searches were run through msearch.py only and recorded from searches.jsonl: LeanFinder with both relative-adjunction and lax-global-sections phrasings, LeanSearch, Loogle, and grep in both CategoryTheory/Sites and Algebra/Homology. All services answered. Hits provide underived module adjunctions, sheaf modules, global sections, condensed internal Hom or rigid tensor adjunctions, not the full construction. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean around pullbackPushforwardAdjunction and CategoryTheory/Sites/SheafCohomology/Basic.lean: the latter defines abelian Ext cohomology, with no ringed-site cup operation. The old inherited searches with unavailable services were replaced by this run's actual logged searches.

## Not duplicates

No new nodes. The related existing global-scheme definition and constant-coefficient products are discussed above.

## Review by NF

I read Stacks sites-cohomology.tex at remark-cup-product (0B6C), section-cup-product (0FPJ), lemma-adjoint (07A6), lemma-pullback-tensor-product (07A4), the module/global-cohomology definitions at equation-cohomology-modules, and lemma-cohomology-modules-abelian-agree (03FD). These give respectively the precise adjunct composite, global specialization to the point with A=Gamma(O), the needed unbounded adjunction, the direction of mu, and the meaning of the ordinary module and underlying-additive cohomology. No SGA source is used.

There are no proof steps or new nodes to review. For the constituent notions I opened and read every statement dependency, including the nine original definition nodes. def-weil-sheaf-of-modules-category defines actual ringed-site modules; def-pur-sheaf-tensor-product defines their sheafified tensor; def-weil-abstract-derived-category defines the unbounded category and its cohomology; def-pc-kflat-complex and def-pc-tensor-complex-sheaves define the resolving complexes and signed direct-sum total. The added lem-weil-pbc-site-derived-tensor-descent supplies actual K-flat representatives with flat terms, the tensor bifunctor and canonical resolution comparisons. The added lem-weil-pbc-ringed-projection-mate-exact explicitly states the canonical adjunction with counit and the natural mu isomorphism for arbitrary ringed topoi with commutative rings on small sites; I use those clauses, not its perfect-projection-formula consequences. No exactness of ordinary module pullback is assumed. def-pur-kinjective-complex and def-pur-ringed-site-zeroth-hypercohomology supply the K-injective global-sections convention, and def-sfb-coefficient-module-global-sections defines compatible families without a final site object. def-weil-pbc-ringed-topos-morphism has the actual geometric adjunction and structural ring map. The point specialization uses the canonical constant-ring-to-O evaluation map and not an assumption that the source site has a final object. The etale-site, scheme and algebraic-space definition nodes give the final application and its structure sheaf.

I checked the cohomology prescription directly: for closed x in degree p and y in degree q, d(x tensor y)=dx tensor y+(-1)^p x tensor dy=0. Replacing x by x+du changes the product by d(u tensor y); replacing y by y+dv changes it by (-1)^p d(x tensor v). Thus it descends locally to classes and sheafifies. A quasi-isomorphism between K-flat representatives commutes with this prescription and induces the canonical cohomology isomorphisms, so the tensor-descent comparisons give the same definition. Tensoring the resolution augmentations has precisely the direction F tensor-derived G to (F tensor G)[0]. In degree zero the product reduces to the ordinary direct-image section pairing. When f is the identity it reduces to the ordinary coefficient product on modules (higher R^p id vanish); when either coefficient is zero the product is zero. For a one-object point site it is the usual tensor pairing of module cohomology, including rings with torsion; flatness of F or G is never imposed, and derived tensor is not falsely identified with ordinary tensor. For a site without a final object, compatible families still define Gamma and the point morphism. p=0, q=0 and the zero ring cause no type or sign exception.

I checked delivery-errors B–E: no unsplit proof sketches or new clause nodes, no fictional Mathlib searches, no source-section-number citations replacing tags, no reference to an unintroduced P,Q, no smaller-site or flatness hypothesis smuggled in, and no proof step using a cited node's proof instead of its statement. Every constituent citation is an existing definition/infrastructure owner; no new theorem, dependency cycle through a new node, or long proof step is introduced. citations.json is [] because the exact-verbatim proof-step requirement has no instances for a definition. The two global/relative cup clauses retain the original construction. This is my own source and statement-dependency audit.

## Unfinished work

None for the one-level definition split. Existing unresolved infrastructure remains owned by its existing DAG nodes; no Lean was written or compiled.
