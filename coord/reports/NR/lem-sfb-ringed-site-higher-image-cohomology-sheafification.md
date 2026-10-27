# Stage-1 report: lem-sfb-ringed-site-higher-image-cohomology-sheafification

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-higher-image-cohomology-sheafification.json`: existing statement, now split into five complete proof steps; no statement or statement-dependency change. Not itself a Mathlib leaf.
- `citations.json`: one entry for every step/node pair, quoting each cited statement verbatim.
- `report.md`: this report. The required search command maintains `searches.jsonl`.

No new DAG nodes and no new Mathlib leaves. All seven supporting nodes already exist. No unit record was changed: this auxiliary item is not the unit's key statement.

## Attachments

None. I searched the project under `lean/WeilConjectures/` for the item tag and the higher-image, ringed-site and cohomology-presheaf notions. `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf` concerns abelian sheaves on scheme etale sites; the abelian higher-image functor comparison also uses abelian coefficients and scheme sites. The smooth-base-change cohomology-presheaf module concerns scheme etale sites and constant coefficients. They do not state this arbitrary ringed-site, varying-ring module assertion. I did not count sorry declarations as finished proofs.

## Literature wanted

None. All mathematical inputs were available locally. No SGA source was used.

## What was wrong or incomplete

The imported item was a correct statement with no proof. Stacks Tag 072W explicitly works with modules on ringed sites, so replacing the source category by abelian sheaves would have introduced an unnecessary comparison theorem. I retained the statement verbatim, computed in module injective resolutions throughout, and supplied its asserted naturality rather than treating an objectwise isomorphism as a natural one.

The ancestor command reports `blueprint.from.node = None`; the item's existing null ancestor and detailed `from.place` chain were retained. I read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3), and searched the imported blueprint for higher direct images and cohomology sheaves. The module comparison is an auxiliary sheafification input below the recorded filtered-colimit criterion, not a change to the unit or chapter route. Existing abelian or constant-ring comparisons are not exact duplicates of the item.

## Not duplicates

No new nodes. In particular I found and reused `lem-weil-pbc-injective-resolution-lift-exists` instead of introducing a resolution-comparison node. I likewise reused the existing ringed-module exact-sheafification leaf and the general exact-functor homology leaf. The resolution-comparison searches in `searches.jsonl` document this discarded need, not a new statement.

## Review by NR

I read Stacks `sites-cohomology.tex`, Tag 072W, `lemma-higher-direct-images`, statement and proof (lines 747–785): its complex is the direct image of an injective resolution in source modules, and its quotient of evaluated cycles by evaluated boundaries is exactly the item's local cohomology. For the proof's prerequisites I read `sites-modules.tex`, Tag 03CY, `lemma-sheafification-presheaf-modules` (including its adjunction), `lemma-sheafification-exact`, and Tag 03DA, `lemma-abelian`. For resolutions I read `derived.tex`, `lemma-injective-resolutions-exist` and Tag 013P, `lemma-morphisms-lift`. The cited general exact-functor statement is the kernel/image/quotient consequence of Stacks Tag 010N. There are no new-node sources to audit.

Step 1 cites the actual resolution-existence clause (1) of `lem-weil-pbc-left-exact-injective-resolution-degree-zero`, and the actual canonical resolution-computation statement in `lem-weil-pbc-derived-functor-map-via-lift`. The latter is used both for module direct image and for additive evaluation to abelian groups. I read their statements, not their proofs. `def-weil-sheaf-of-modules-category` explicitly says kernels are sectionwise; this justifies left exactness of both functors, since restricting scalars changes neither additive kernels nor biproducts. Enough injectives is an explicit hypothesis in the source module category; no preservation of injectives by module pushforward is needed.

Step 2 writes out the elementary presheaf kernel/cokernel universal properties rather than introducing an objectwise-homology node. The two cited definition statements give exactly module sheaves and presheaves with semilinear restrictions. The formula for multiplication uses the specified map rho, and its naturality proves the required semilinearity. Evaluated differentials are A-linear, so multiplication preserves cycles and boundaries. This is a kernel/quotient construction in source module cohomology, not an identification with cohomology computed from injective abelian sheaves.

Step 3 cites `lem-weil-pbc-ringed-site-module-sheafification-exact` with the target ringed site (D,B), and `lem-sp-exact-functor-preserves-homology`, specifically clause (c), which explicitly asserts naturality and compatibility with cycle inclusions and homology projections. I verified the exactness hypothesis of the second from the first. The presheaf/sheaf module categories are abelian as stated in the first and in the module-category definition. The sheafification definition supplies the module-linear universal property; the step proves directly that it fixes a sheaf and does so naturally, rather than citing the definition for an unstated plus-construction theorem. This yields an isomorphism of B-module sheaves and the requested cocycle map.

Step 4 cites `lem-weil-pbc-injective-resolution-lift-exists` for existence of an augmentation-preserving lift, a clause absent from the derived-map lemma itself. Both resolutions are nonnegative and consist of injective A-module sheaves, as required. The derived-map lemma then computes the two relevant maps with this very lift. The exact-functor homology lemma supplies naturality of the same normalized comparison as in step 3, and the module-sheafification universal property proves equality from the displayed cocycle calculation. Thus the claimed square is for the actual cocycle comparison; no arbitrary choice of isomorphisms is substituted. Derived evaluation functoriality also proves identity and composition for P^q(a).

Step 5 applies those same two resolution statements to the identity of M and different resolutions. The evaluated cohomology maps and the higher-image maps become the identities under their canonical derived comparisons, so the scalar structure and sigma are independent of the choice. No homotopy-uniqueness assertion is silently taken from the lift-existence node. In particular, no new homotopy-comparison node is needed.

I checked B–E of `coord/delivery-errors.md` against every step: no new unsplit node contains a proof; the existing statement is self-contained and its TeX and hypotheses are unchanged; all non-elementary facts used are actual cited statements; citations do not take hidden constructions from proofs; the proof carries the argument instead of moving a clause into a new node; and every morphism direction and coefficient category agrees with 072W. All five proof steps are shorter than 2000 characters. The only elementary step explicitly constructs the objectwise kernel, quotient, action and restriction maps from the cited definitions.

Small cases checked: for q=0 the incoming term is zero and the construction recovers the actual module direct image; for M=0 the complex and both cohomologies are zero. On a one-object site with only identity covers this is the ordinary restriction-of-scalars computation, including a nonflat ring map such as Z to Z/2Z. For the identity site/ring map and q>0 the associated cohomology presheaf is zero because the resolution is exact as a sheaf complex, consistent with R^q(id)=0. Objects admitting empty covers also give zero evaluated sections and zero quotient; no nonempty-cover assumption appears. The argument never uses tensoring or flatness of rho.

Mathlib searches were run exclusively through the required msearch command and logged unchanged. I read its hits, including `CategoryTheory.Sheaf.cohomologyPresheafFunctor` and `cohomologyPresheaf` in `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` (lines 72 and 81): these are Ext cohomology for abelian sheaves, not the ringed-module comparison. A second semantic phrasing found underived module pushforward and sheafification compatibility, also not the item. Supporting comparison searches found `InjectiveResolution.desc` (line 94), `desc_commutes` (102) and `descHomotopy` (169); I read their source and then reused the existing DAG lifting node. No unavailable service was recorded as a negative result.

## Unfinished work

None in the mathematical split. Independent maintainer review remains the delivery workflow's responsibility.
