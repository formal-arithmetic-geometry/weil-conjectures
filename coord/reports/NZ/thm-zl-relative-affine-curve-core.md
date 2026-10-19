# Stage-1 delivery: thm-zl-relative-affine-curve-core

## Files written

- `dag/nodes/sec-deligne-laumon-general/thm-zl-relative-affine-curve-core.json`: statement, split; same theorem, with three checked proof steps and recorded Mathlib searches. No Mathlib match.
- `citations.json`: a verbatim statement quotation for every node used by each proof step.
- `searches.jsonl`: the actual msearch.py output records, preserved as written by the search command.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No unit record changed: the item is an auxiliary theorem, not the unit's key proposition `sk-p-dl-general-relative-line`.

## Attachments

No finished attachment for the item. I searched the blueprint tag, the declared name, and the relative affine-curve notion in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. The matching declaration is `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`, `WeilConjectures/DeligneLaumon/Reduction/RelativeAffineLine.lean:259`. Its body has no literal sorry, but it calls `AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` (line 194), whose current body is sorry. It therefore does not establish a finished proof. The mixedness declaration at line 229 likewise depends on the still-sorried real-factor assertion at line 213. I did not use the archived master as evidence of completion.

The current Lean `RelativeCurve` section at lines 171–186 assumes a morphism over the finite field, smooth of relative dimension one, separated and quasi-compact, with separated finite-type base. The item assumes smooth separated maps between separated finite-type schemes with every nonempty geometric fiber a smooth affine curve. This is the same geometric setting; empty fibers and disconnected fibers are permitted. The Lean theorem is for natural cohomological degrees. The ordinary notation $R^i$ in the item concerns higher direct images; if extended to negative integer degrees, those sheaves vanish.

### Audit metadata discrepancies and existing ownership

I inspected the item's imported `lean_audit.slopmaster2.open` list, searched all its unassigned declaration names against current node statements, sources, lean records and attached declarations, and opened their recorded source modules when those still exist. Much of this list refers to modules absent from the current read-only checkout, whereas the current proof is the short combination of three named existing nodes. I have preserved all maintainer-owned audit data and have not recreated unavailable historical interfaces or inserted them as direct premises of this combination proof.

Existing associations found for entries whose old `nodes` list is empty (these are ownership observations, not claims that their Lean is closed):

- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` belongs to `lem-sf-adic-affine-direct-image-finiteness` (current source line 411, still sorry).
- `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine` belongs to `lem-sc-affine-artin-schreier-vanishing` (current source line 43, still sorry).
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion` is carried in the existing `prop-functor-package` records; its recorded old module is absent.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant` is already recorded by `lem-wf-dense-open-pi1-surjective`; its old module is absent.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_fourierTransform_middleExtension_toComplex` belongs to `prop-a1-fourier-middle-extension` (current line 162, still sorry).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isGeometricallyConstant_of_hasLinearArtinSchreierConstituent_zero` and `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity` belong to the two cases of `lem-a1-unramified-nonexceptional` (current lines 136 and 148, still sorry).
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite` is recorded by `lemma-weil-pbc-finite-direct-image-exact`; its old module is absent.
- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_affineLine` is already recorded by `lem-fd-affine-line-constant-cohomology` and `sk-lem-as-properties`; its old module is absent.
- `AlgebraicGeometry.nonempty_iso_dual_artinSchreier` is already recorded by `lem-fd-as-characters`; its old module is absent.

Other historical unassigned entries refer to absent modules (lisse monodromy, old Weil lower-shriek operations and functoriality, old trace-formula and Grothendieck–Lefschetz interfaces, stalk extension by zero, and Fourier inversion). The still-existing unassigned Poincare pairing and trace-energy constant-twist/envelope declarations remain sorry; their work belongs below the existing curve-estimate and real-sheaf nodes. They are not needed as independent assumptions for this item's three-lemma proof. The stale audit ownership should be refreshed by the maintainer rather than producing duplicate nodes from a historical transitive dependency list.

## WANTED

None for the argument delivered here. Its current blueprint statement and proof, and the three cited lemma statements, are all present. The proof follows the blueprint and is marked `proof_origin.by = agent`; it is not presented as a proof read from an independently authored paper. No SGA source is used.

## Corrections and limitations

The imported proof already named the right three lemmas but compressed their application into one paragraph. I separated the existential mixedness witness, the pointwise upper bound and the cutoff, making all their hypotheses explicit. I did not change the theorem statement.

`def-weil-pbc-constructible-complexes` defines finite-ring sheaves and does not define lisse $\overline{\mathbf Q}_\ell$-Weil sheaves. I removed that direct statement dependency and used the existing `def-weil-weil-sheaf-complex`, `def-pod-lisse-l-adic-sheaves`, `def-weil-integral-rational-qbar-compact-support` and `def-weil-derived-cohomology-sheaves` interfaces instead. The scheme convention collectors and punctual-weight definition are retained. The cited mixedness theorem explicitly supplies a mixed constructible Weil sheaf, so this combination does not require a fresh finiteness theorem or a new coefficient comparison.

The current main-20261015 proof is in the separate `.proof.md` file. I read it and its statement, alongside the current chapter/unit record. The item has no `blueprint_update`; the two subordinate lemmas do, and their current source statements are compatible with this application. In particular the mixedness lemma gives an arbitrary real bound $u_i$, not the bound $w+i$ being proved here. I use its statement only, never its proof as an additional unnamed black box. The punctual lemma's updated formulation assumes smooth relative dimension one, quasi-compactness and affine fibers; these are precisely the relative-curve setting recorded in the Lean section, and its current DAG statement directly accepts the item's hypotheses.

Nothing in the assigned split remains unfinished. Its cited lemmas remain separate DAG work; this delivery does not assert that their proofs are completed.

## Not duplicates

No new nodes. Whole-blueprint searches for `relative affine curve`, `higher direct images`, and `mixed of weights at most` were read, together with the existing same-unit nodes. The first two subordinate curve lemmas cover different data (existence of a mixed filtration and a punctual eigenvalue bound); the cutoff is a general assertion about a sheaf already known mixed. The general direct-image weight theorem was deliberately not used, since that would bypass this reduction and risk circularity. `blueprint.same_as` is empty: no separate blueprint node was found stating exactly this auxiliary theorem in another form.

## Mathlib searches

All six recorded queries were actually executed with msearch.py and the resulting hits read. LeanFinder returned general scheme limits and condensed/derived-category declarations, not a weight estimate. Loogle `"Weil", "weight"` returned zero hits. The exact-name grep and the broader Weil/punctual/mixed-weight/Frobenius-cohomology grep returned zero hits. LeanSearch was available: its first query returned Lie/module/modular-form/sieve weight results, and its second returned finite-field Frobenius, isocrystal and eigenvalue results. Neither states a Weil-sheaf direct-image weight theorem. Both phrasings and their actual queries are in the item's `mathlib_searches` and in `searches.jsonl`.

## Review by NZ

I read `thm-zl-relative-affine-curve-core.md` and its separate proof in the main-20261015 snapshot, the older statement/proof for comparison, the chapter and unit record, and the current Lean RelativeCurve declarations. The source argument is exactly mixedness plus the curve punctual estimate plus cutoff; the unit's fiber estimate and real-envelope route are preserved through their existing nodes. No new lemma was invented and none of the conclusion was transferred into a replacement node.

For step 1 I opened the full statement of `lem-zl-relative-curve-mixedness`. It has the same separated finite-type source/base, smooth separated relative-curve morphism, lisse pure sheaf and coefficient conventions. Its conclusion is an existential real bound $u_i$, precisely what this step takes. I also opened `def-weil-punctual-weights`: its definition of mixedness requires a constructible Weil sheaf and a finite filtration by constructible Weil subsheaves with pure quotients. This justifies using the constructible sheaf as the input of the cutoff; I did not infer constructibility from the definition of a finite-coefficient sheaf.

For step 2 I opened `lem-zl-relative-curve-punctual` and its main-snapshot update. Its displayed estimate is on the stalk of the very same $R^ih_!\mathcal F$, relative to $q^m$ at a degree-$m$ closed point, with the same $\iota$ and weight $w$. Renaming $q^m$ as $q_y$ gives exactly the cutoff inequality. No base-change theorem, restriction-purity theorem or estimate on an individual connected component is used separately at this level: those belong to that existing lemma, whose statement already supplies the complete punctual bound.

For step 3 I opened `lem-zl-mixed-punctual-cutoff`. It requires a constructible $\Qlb$-Weil sheaf on a separated finite-type base, mixed at some real bound $u$, with all closed-point eigenvalues bounded by $q_y^{v/2}$. Step 1 supplies $u=u_i$ and the filtration, and step 2 supplies $v=w+i$. These are all its hypotheses. Its conclusion is the exact bound in the item. The quotes in citations.json were copied from these node statements and locally checked as substrings.

I checked B–E against the files and sources: there are no new statement-only nodes to audit, no tag standing in place of a cited result, no relabeling of the goal, no uncited non-elementary argument, and no newly introduced statement or definition. All three proof steps are marked non-elementary because they use named theorems. They are each below 2000 characters; none hides an inline comparison or standard lemma. Empty source/base and the zero sheaf are allowed by the same hypotheses: mixedness admits the empty filtration and the eigenvalue condition is vacuous on zero stalks. Empty fibers are explicitly permitted, and disconnected fibers have not been silently assumed connected. No assumption of lissity of the direct image or surjectivity of $h$ is made. I also checked that all three proof citations are in the item's own unit and that the statement did not change. No compiler, Lake command, live-project mutation, or direct git command was run.
