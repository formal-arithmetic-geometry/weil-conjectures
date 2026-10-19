# Worker report: prop-coef-integral-exceptional-adjoint

Repair by Q14, 2026-10-16, of the E2/E7/C4 return on delivery 9e7d5db0cb41. This report supersedes the previous report's mathematical approvals of steps 4 and 6. No delivery is pushed by this worker.

## Files written

- `dag/nodes/sec-six-functors/prop-coef-integral-exceptional-adjoint.json`: split item, seven steps; steps 4 and 6 are rebuilt without internal-Hom base change.
- `dag/nodes/sec-six-functors/lem-coef-derived-system-evaluation-calculus.json`: statement-only unsplit tool; now explicitly includes the enriched reduction/limit adjunction gamma and its actual projection formula. Mathlib: no match.
- `dag/nodes/sec-six-functors/lem-coef-finite-adjunction-diagram-realization.json`: statement-only unsplit tool retained from the previous repair; finite exceptional systems and their enriched adjunction. Mathlib: no match.
- `citations.json`: refreshed verbatim statements for all 42 step/node pairs, including the enlarged calculus statement.
- `report.md`: current repair and review. Searches are recorded in `searches.jsonl`; scratch scripts remain under the item's sandbox.

Two new statement nodes, zero Mathlib leaves. Neither new node is claimed proved. The item is not the unit's key statement, so no unit file changes.

## Attachments

None. I searched the project source by the item id and exceptional-adjoint name and read `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint` at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/Etale/Derived/IntegralCoefficients.lean:298–366`. Its proof has direct sorry terms at line 359; it also works on ordinary-etale categories with compactification and right-adjoint-instance hypotheses, and therefore is not a finished attachment of this unconditional pro-etale item. The exact upstream master is reference material, not proof evidence. The new coherent/enriched system tools have no exact declarations in the project source searches retained from the preceding reading.

## WANTED

None for this repair. The shared checkout does not contain the untracked blueprint/Stacks sources, but I read their existing read-only copies under `/home/ubuntu/weil-launcher-nt/literature/`; no literature was downloaded. The new coherent tools are agent-formulated obligations; their sources say explicitly that the cited Stacks tags supply resolution foundations, not their whole statements.

## What was wrong and what changed

The returned step 4 used `lem-coef-integral-hom-reduction` to make beta invertible, reconstructed the integral internal Hom, and interchanged sections and limit. Step 6 again used that theorem for transposes. Both direct uses have been removed, as has the now-unnecessary use of `cor-coef-integral-internal-hom`. The replacement does not silently substitute the narrower corollary or add perfectness hypotheses to the item. It follows the item's blueprint paragraph 2: reconstruct the second Hom input Q using the actual unit from step 2, then apply the enriched scalar-extension/limit adjunction gamma. No tensor of an integral mapping complex with A_n is taken. Gamma's specified projection sends h to e_n h_n, and the unit/counit identity gives e_n (u_Q)_n=1. Thus lambda's actual projection sends h to h_n. Step 6 now computes finite adjuncts from this formula, including the explicit c_K inverse and c_L target comparison.

This adds a precise enriched clause to the existing general coefficient-calculus obligation rather than moving an integral exceptional conclusion into a new node. The clause concerns arbitrary schemes, arbitrary first inputs and normalized coefficient systems; it has no exceptional functor, no constructible preservation assertion and no reconstruction invertibility assertion. The parent still proves reconstruction invertibility, geometric preservation, the dual formula, its interval, and the integral adjunction. The finite-system realization tool is unchanged. Existing nodes on fixed-ring strict limits, scalar-extension degree-zero adjunction, or nonfunctorial evaluation lifts do not already state the simultaneous enriched comparison and its projection normalization.

## Source and return dispute

The return's displayed residue-field counterexample does not refute the cited theorem as it is actually stated. Let R be a complete DVR, t its uniformizer, and k=R/t. From the free resolution [R --t--> R], k tensor^L_R k is k[1] plus k, not k in degree zero. Likewise RHom_R(k,k) is k plus k[-1]. Therefore BOTH sides of the alleged counterexample, with the stated derived reductions of both inputs, have cohomology k in degrees -1 and 1 and k^2 in degree 0:

    RHom_R(k,k) tensor^L_R k = (k plus k[-1]) tensor^L_R k,
    RHom_k(k tensor^L_R k, k tensor^L_R k) = RHom_k(k[1] plus k, k[1] plus k).

The review instead computes RHom_k(k,k), which replaces both derived reductions by underived ones. Also R/t is not free or flat over R, but it IS perfect, presented by the displayed bounded complex of finite free R-modules. Perfectness of a coefficient complex and flatness of its degree-zero quotient are different assertions. I read the current `lem-coef-integral-hom-reduction` statement: it uses the derived inputs F_nK,F_nL, and its finite-free model is two-term, rather than claiming the quotient is free. Consequently this calculation establishes no false imported statement requiring a weakened item. I report the discrepancy explicitly rather than inventing a source counterexample or changing someone else's node. The repair independently avoids the questioned base-change theorem altogether.

The item's own source has a separate previously reported typing issue: STATEMENT-DISPUTED: the integer interval [a-2 dim X,b+2 dim Y] is not defined for an empty scheme whose topological dimension is minus infinity. The delivered statement retains the corrected nonnegative integer dimension-bound form, with 0 for empties and the original dimensions for nonempty finite-type schemes. No constructible-adjunction conclusion is weakened.

## Review by Q14

I read delivery-errors B–E in full, the worker and stage-1 rules, the three blueprint levels in SETUP, GOAL and dag-sync, the current chapter/unit records, both maintainer review files, the complete three delivered nodes, and the statements of every direct proof dependency. I read both proof paragraphs of the master `prop-coef-integral-exceptional-adjoint.md` and the full master `lem-coef-finite-exceptional.md` under the general-biduality unit. The chapter/unit route remains finite duality and coefficient transport; only the disputed lower-level mapping-limit inference is replaced. The input is completed sheaf coefficients on the small pro-etale site, and finite coefficients are ordinary constant quotient-ring sheaves. I did not substitute a condensed category or assume a pro-etale ambient exceptional adjoint.

1. Step 1 uses exactly integral Verdier's constructibility, evaluation-defined dual reductions and interval [-b-2d_Y,-a], the integral-operation theorem's completed-pullback preservation/reductions, and finite pullback's Tor preservation. Each object is constructible before the next duality application. Substitution gives [a-2d_X,b+2d_Y]. No claim that a finite constructible module is flat is made.
2. Step 2 uses the calculus's actual adjunction unit/counit, normalized effectivity's canonical counit isomorphisms and completeness, the integral-category definition's uniform reduction supports, triangulated closure, exact derived change of rings, the completeness Roos triangle, and the cone-zero criterion. I read all those statements. Effectivity identifies the reductions of T(P), so they have the same uniform interval as P; the triangle identity inverts the actual unit's reductions. Its complete cone has zero reductions and hence is zero. No isomorphism of cones is chosen to manufacture a natural unit.
3. Step 3 uses only the beta MAP from the calculus, integral Verdier for invertibility on the particular pairs (P,omega), normalized effectivity for the completed-pullback and dualizing counits, the finite-system tool's actual dual formula, the finite-exceptional normalization, and the definitions/properties of completed pullback and omega. The contravariant middle map D_X(q_L^{-1}) has the correct direction; both factors of q_L are inverted. The written counit-naturality identity proves compatibility of the resulting actual integral map with its specified finite maps. No arbitrary-input beta isomorphism is invoked here.
4. Step 4 is new. Its cited calculus now states precisely gamma, its naturality, its compatibility with composition, and its projection e_N,n h_n. Q is integral constructible, hence its actual u_Q is invertible by step 2. N=R_W Q and R_W P are normalized by derived tensor associativity. Composing RHom(P,u_Q) with gamma is therefore a specified natural isomorphism, and e_N,n (u_Q)_n=1 proves the reduction projection formula. The separately cited existing scalar-extension/restriction statement has exactly P over the completed ring and a second input over B_n; it does not assert Hom base change. The H^0/global-Hom statement gives the categorical Hom interpretation. All three cited statements say what is taken from them. There is no use of a complete internal Hom, a perfect first input, or an isomorphism between independently selected Roos cones.
5. Step 5 uses integral Verdier to obtain a common Tor interval for K_n BEFORE applying integral compact-support preservation; finite-dimensionality provides the bound required there. I checked the compact-support statement supplies both constructibility and canonical finite reductions. Finite enriched adjunction uses etale representatives, Noetherianity over the field, Nagata compactification, the ordinary-etale internal-adjunction statement, compact-support comparison and fully faithful site comparison on bounded-below objects and all shifts. Derived-pushforward composition justifies R-Gamma Rf_* = R-Gamma. For coherent systems the actual A is stated by the finite-system tool, not inferred merely from compatible evaluated maps. Both inputs lie in its normalized ctf domain by integral Verdier; effectivity makes c_K and c_L isomorphisms. H(c_K^{-1},1), then A, then H(1,c_L^{-1}) has the correct variance. These citations are unchanged and their statements were reread.
6. Step 6 is rebuilt. The natural system isomorphism from step 5 and the exact total-limit functor give the mapping isomorphism, and the lambda of step 4 provides both ends. The naturality identities for Phi and its inverse yield both triangles by substituting identities. For every actual u, projecting sends it first to u_n, then to u_n c_K,n^{-1}, then to its finite adjunct, and finally to c_L,n^{-1} of that adjunct. This is the displayed equality c_L,n(Phi(u))_n=adj_n(u_n c_K,n^{-1}). The finite-system tool identifies the evaluated A with the finite adjunction, and the existing finite-exceptional statement supplies the unit/counit normalization. Taking u=1, or taking v=1 under the inverse bijection, gives the finite units and counits. No faithfulness of the family of reduction functors is assumed. The formal composition/adjunct calculations are elementary after these cited system constructions.
7. Step 7 uses the dualizing proposition's actual defining tower and projections, read in full, and specializes the constructed adjunction to the structure morphism and L=R. The finite-system tool already chooses that same coherent dualizing tower. It claims equality of the defining object and equips it with this adjunction; it does not infer equality with an independently unspecified mapping isomorphism.

For the coefficient-calculus tool I read Stacks `sites-cohomology.tex` Tag 06YS, `lemma-K-flat-resolution` (3207ff); Tag 0A95, `lemma-RHom-well-defined` (8754ff); Tag 0941, `lemma-derived-limit-is-ok` and its proof (5067ff); and `injectives.tex` Tag 079P, `theorem-K-injective-embedding-grothendieck` (1807ff). I also read the sections/global-Hom lemma `lemma-section-RHom-over-U` (8874ff) and `lemma-RGamma-commutes-with-Rlim` (5126ff) to check the mapping notation and the fixed-input limit route. They provide resolutions, total-limit and Hom foundations, not the whole enriched coherent statement. Gamma is explicitly a remaining general tool obligation on system resolutions. It applies fixed-input Hom to a limit and then ordinary scalar adjunction; it contains no Hom/tensor interchange. Its statement specifies the actual maps, not a preferred lift inferred from evaluations.

For the finite-system tool I read the full finite-exceptional blueprint, including finite dual-formula, enriched adjunction, coefficient cocycle and unit/counit paragraphs, together with the same four resolution sources. Its finite normalized ctf hypothesis is retained; n=1 and n>1 are not conflated. Both new nodes have self-contained objects/quantifiers, direct notion dependencies, one TeX escape layer, empty proof and proof_deps, exact blueprint ancestry, no claimed Mathlib match, and no dependency back to the item. The new gamma clause is a general coefficient comparison, not an integral exceptional adjunction clause in disguise. Existing degree-zero scalar adjunction and strict-limit computation lack precisely this coherent enriched map and projection identity. The Not duplicates section records the source-tag collisions.

Small cases checked beyond the corrected residue-field calculation above: P=R and N=(A_n) gives the ordinary completed quotient limit and standard projections; P=Q=k on the point has the genuine two-term derived reductions, and gamma projects the identity to identity on that two-term object. Zero inputs and empty schemes give zero mapping complexes and units/counits in the zero category. For f=id the finite A is identity adjunction and the integral formula is biduality. For a smooth line over the point, R(1)[2] has interval [-2,-2] inside [-2,0]. The finite-system tool assumes no uniform bound in n; the parent obtains the bounds it uses from steps 1 and 5. Every index starts at 1.

The return's E2/E7 concern is handled by removing the disputed inference, documenting exactly why its proposed small case does not show falsity, and adding no unverified claim of quotient flatness. C4 is handled by explicit gamma and projection clauses and the refreshed verbatim citations. Earlier coherence repairs remain: the unit, finite-system maps and A are actual specified transformations, never arbitrary lifts from evaluation fullness. No remaining non-elementary use is hidden under an elementary flag. No other worker's node or maintainer-owned field was changed, and no agent, Lean writing, compiler, Lake or build was used.

## Mathlib and reuse searches

I reran whole-DAG and blueprint searches for coefficient adjunction, derived inverse limit, enriched/mapping-complex and scalar-extension terms. I opened the existing scalar-extension/restriction adjunction, strict-limit theorem/computation, reconstruction-with-equipped-models and sequential-evaluation-fullness statements. The last explicitly disclaims functorial choices; none already supplies gamma and its coherent projection identity. The old fixed-coefficient results and finite-exceptional statement are reused where they apply.

The enlarged calculus was searched again with msearch.py: LeanFinder using two distinct phrasings for Hom into a coefficient-system limit, Loogle `"DerivedCategory", "Adjunction"`, grep `derivedHom.*[Ll]imit|[Ll]imit.*derivedHom|derived.*[Ss]calar.*[Aa]djunction`, and LeanSearch for derived tensor/restriction adjunction and inverse limits. Exact requests/results are appended to its mathlib_searches and the tool log. This time LeanSearch succeeded and returned ordinary ModuleCat scalar-extension/restriction/coextension declarations. I read `ModuleCat.extendRestrictScalarsAdj` and its hom-equivalence/unit/counit at `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:885–930`. I also read the returned ordinary presheaf limit construction at `Mathlib/Algebra/Category/ModuleCat/Presheaf/Limits.lean:65–150`. They do not state enriched derived varying-coefficient systems, so are not one-line specializations. The second semantic search returned local-cohomology diagrams, condensed solidification and Tor infrastructure, also not matches. Earlier recorded HTTP-500 searches remain labelled unavailable; the successful fresh search does not retroactively change those results. The unchanged finite-system tool retains its already logged searches and no-match verdicts. No fabricated query or unrun search is recorded.

## What remains

No part of this item's one-level split is intentionally left unfinished. The two new general tools remain unsplit statement nodes for later workers. The required dry run is recorded below after execution; the sandbox is handed to a fresh second reader and is not pushed by this worker.

## Not duplicates


The following source-tag collisions concern the generic resolution foundations; a common tag is not an identical statement. Each pair below contrasts the statement, not merely its title.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-single-tensor-representative: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-model-shift-gauge: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-flat-truncation-telescope-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-complex-hocolim-colimit: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-derived-single-hom-evaluation: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-derived-tensor-upper-bound: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-bounded-flat-replacement: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-resolution: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-sc-bounded-flat-shift-representative: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-derived-hom-pushforward-kflat-model: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-bounded-above-flat-tensor-acyclic: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-normalization-morphisms: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-kflat-localized-cone-presentation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-shift-gauge: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-hocolim-truncations: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-bounded-below-injective-resolution: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-bounded-normalization-extension: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-arrow-diagram: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-bounded-above-flat-kflat-site: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-hom-complex-resolution-shift-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-normalized-flat-telescope-stage-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-pc-derived-tensor-cohomology-vanishes: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-normalization-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-normalized-flat-telescope-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-tensor-counit-coordinate-equation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-normalization-unshifted-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-bounded-flat-model-normalization: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-sum-comparison-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-pc-open-module-derived-sections: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-derived-system-evaluation-calculus vs new-v4-homology-evaluation-roof-comparison: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs def-pc-kflat-complex: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-stage-map-refinement: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-cone-normalization-descent: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-sc-derived-tensor-augmentation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-pc-derived-tensor-complex-cohomology-vanishes: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-sc-flat-telescope-stage-map: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-derived-internal-hom-single-comparison: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-sum-models: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-closure: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sc-flat-telescope-stage-naturality: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pc-kflat-cone-direct-sum: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-pbc-ringed-cech-koszul-dual-limit: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-derived-limit-existence: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-derived-system-evaluation-calculus vs def-weil-pbc-ringed-koszul-system: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-pbc-sequential-tower-evaluation-full: the existing node only supplies nonunique lifts and explicitly no functorial choice; it does not supply natural system transformations.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: the existing node constructs total Rlim on supplied constant-ring coherent towers; it does not construct varying-ring reduction/Hom systems or their adjunction.

- lem-coef-derived-system-evaluation-calculus vs prop-weil-pbc-rlim-functoriality: the existing node gives total Rlim for already supplied coherent tower maps; it does not produce any coherent reduction/Hom/exceptional comparison.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-pbc-site-derived-tensor-descent: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs prop-weil-pbc-derived-inverse-limit-computation: the existing node computes a supplied derived tower limit; it does not supply coherent finite operation or internal-Hom transformations.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-kinjective-degreewise-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-hom-complex-sections-quasi-iso: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-quasi-iso-of-sections: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-rhom-well-defined: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-integral-operations-well-defined: the existing node descends completed pullback and tensor from K-flat complexes; it does not construct the varying-ring Hom system or its reduction/limit adjunction.

- lem-coef-derived-system-evaluation-calculus vs prop-pur-kinjective-resolutions-exist: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-acyclic-kflat-tensor-arbitrary: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-kun-flat-resolution-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-sp-completion-mate-comparison: the existing node compares a completed pullback/direct-image mate for constant coefficient towers and a supplied square; it has neither varying-ring fiberwise Hom nor finite exceptional system realization.

- lem-coef-derived-system-evaluation-calculus vs def-pur-derived-internal-hom: the existing node defines fixed-ring derived internal Hom; it does not give its coherent varying-ring realization.

- lem-coef-derived-system-evaluation-calculus vs lem-sp-proper-open-tower-comparison: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-derived-system-evaluation-calculus vs def-weil-integral-derived-reduction: the existing node defines derived reduction of an integral complex; it does not supply a derived coefficient-system adjunction or Hom comparison.

- lem-coef-derived-system-evaluation-calculus vs lem-pur-hom-complex-hypercohomology: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-compact-support-reduction-tower-functor: the existing node lifts compact supports of integral inputs to constant completed-coefficient towers; it has neither finite exceptional operations on arbitrary normalized varying-coefficient systems nor their enriched adjunction transformation.

- lem-coef-derived-system-evaluation-calculus vs prop-weil-pbc-kinjective-resolutions-exist: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs lem-weil-pbc-kinjective-functorial-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-derived-system-evaluation-calculus vs def-weil-integral-reduction-tower: the existing node defines the integral reduction tower; it does not give the derived reduction/limit adjunction or simultaneous fiberwise Hom maps.

- lem-coef-derived-system-evaluation-calculus vs lem-coef-integral-hom-reduction: the existing node asserts evaluated internal-Hom base-change isomorphisms; the calculus only specifies beta as a map and its enriched gamma compares Hom into a limit, without tensoring Hom. Neither new node assumes that existing isomorphism.

- lem-coef-derived-system-evaluation-calculus vs lem-coef-finite-exceptional: the existing node gives finite dual formulas and coefficient cocycles; it does not supply the natural transformation in the derived category of strict varying-coefficient systems.

- lem-coef-derived-system-evaluation-calculus vs prop-asd-internal-adjunction: the existing node gives an ordinary-etale fixed-ring enriched adjunction; it does not give a varying-coefficient system map before Rlim.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-single-tensor-representative: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-model-shift-gauge: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-flat-truncation-telescope-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-complex-hocolim-colimit: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-derived-single-hom-evaluation: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-derived-tensor-upper-bound: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-bounded-flat-replacement: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-resolution: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-sc-bounded-flat-shift-representative: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-derived-hom-pushforward-kflat-model: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-bounded-above-flat-tensor-acyclic: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-normalization-morphisms: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-kflat-localized-cone-presentation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-shift-gauge: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-hocolim-truncations: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-bounded-below-injective-resolution: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-bounded-normalization-extension: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-arrow-diagram: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-bounded-above-flat-kflat-site: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-hom-complex-resolution-shift-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-normalized-flat-telescope-stage-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-pc-derived-tensor-cohomology-vanishes: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-normalization-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-normalized-flat-telescope-comparison: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-tensor-counit-coordinate-equation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-normalization-unshifted-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-bounded-flat-model-normalization: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-sum-comparison-is-iso: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-pc-open-module-derived-sections: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-finite-adjunction-diagram-realization vs new-v4-homology-evaluation-roof-comparison: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs def-pc-kflat-complex: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-stage-map-refinement: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-cone-normalization-descent: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-sc-derived-tensor-augmentation: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-pc-derived-tensor-complex-cohomology-vanishes: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-sc-flat-telescope-stage-map: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-derived-internal-hom-single-comparison: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-sum-models: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-closure: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sc-flat-telescope-stage-naturality: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pc-kflat-cone-direct-sum: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-pbc-ringed-cech-koszul-dual-limit: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-derived-limit-existence: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-finite-adjunction-diagram-realization vs def-weil-pbc-ringed-koszul-system: the existing node concerns a supplied inverse system or a Koszul/limit construction; it does not construct the specified varying-coefficient reduction/Hom or finite exceptional maps.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-pbc-sequential-tower-evaluation-full: the existing node only supplies nonunique lifts and explicitly no functorial choice; it does not supply natural system transformations.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: the existing node constructs total Rlim on supplied constant-ring coherent towers; it does not construct varying-ring reduction/Hom systems or their adjunction.

- lem-coef-finite-adjunction-diagram-realization vs prop-weil-pbc-rlim-functoriality: the existing node gives total Rlim for already supplied coherent tower maps; it does not produce any coherent reduction/Hom/exceptional comparison.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-pbc-site-derived-tensor-descent: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs prop-weil-pbc-derived-inverse-limit-computation: the existing node computes a supplied derived tower limit; it does not supply coherent finite operation or internal-Hom transformations.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-kinjective-degreewise-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-hom-complex-sections-quasi-iso: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-quasi-iso-of-sections: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-rhom-well-defined: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-integral-operations-well-defined: the existing node descends completed pullback and tensor from K-flat complexes; it does not construct the varying-ring Hom system or its reduction/limit adjunction.

- lem-coef-finite-adjunction-diagram-realization vs prop-pur-kinjective-resolutions-exist: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-acyclic-kflat-tensor-arbitrary: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-kun-flat-resolution-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-sp-completion-mate-comparison: the existing node compares a completed pullback/direct-image mate for constant coefficient towers and a supplied square; it has neither varying-ring fiberwise Hom nor finite exceptional system realization.

- lem-coef-finite-adjunction-diagram-realization vs def-pur-derived-internal-hom: the existing node defines fixed-ring derived internal Hom; it does not give its coherent varying-ring realization.

- lem-coef-finite-adjunction-diagram-realization vs lem-sp-proper-open-tower-comparison: the existing node concerns fixed-ring complex constructions; it does not state either the varying-coefficient derived adjunction and Hom calculus or finite exceptional coherent realization.

- lem-coef-finite-adjunction-diagram-realization vs def-weil-integral-derived-reduction: the existing node defines derived reduction of an integral complex; it does not supply a derived coefficient-system adjunction or Hom comparison.

- lem-coef-finite-adjunction-diagram-realization vs lem-pur-hom-complex-hypercohomology: the existing node supplies a fixed-ring Hom resolution/evaluation or cohomology comparison; it does not give simultaneous varying-ring system maps and their natural identities.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-compact-support-reduction-tower-functor: the existing node lifts compact supports of integral inputs to constant completed-coefficient towers; it has neither finite exceptional operations on arbitrary normalized varying-coefficient systems nor their enriched adjunction transformation.

- lem-coef-finite-adjunction-diagram-realization vs prop-weil-pbc-kinjective-resolutions-exist: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs lem-weil-pbc-kinjective-functorial-existence: the existing node supplies fixed-ring flat/injective resolutions, tensor models or telescope comparisons; it does not give the varying-ring derived-system adjunction/evaluation calculus or the finite exceptional system transformation.

- lem-coef-finite-adjunction-diagram-realization vs def-weil-integral-reduction-tower: the existing node defines the integral reduction tower; it does not give the derived reduction/limit adjunction or simultaneous fiberwise Hom maps.

- lem-coef-finite-adjunction-diagram-realization vs lem-coef-integral-hom-reduction: the existing node asserts evaluated internal-Hom base-change isomorphisms; the calculus only specifies beta as a map and its enriched gamma compares Hom into a limit, without tensoring Hom. Neither new node assumes that existing isomorphism.

- lem-coef-finite-adjunction-diagram-realization vs lem-coef-finite-exceptional: the existing node gives finite dual formulas and coefficient cocycles; it does not supply the natural transformation in the derived category of strict varying-coefficient systems.

- lem-coef-finite-adjunction-diagram-realization vs prop-asd-internal-adjunction: the existing node gives an ordinary-etale fixed-ring enriched adjunction; it does not give a varying-coefficient system map before Rlim.

- lem-coef-derived-system-evaluation-calculus vs lem-coef-finite-adjunction-diagram-realization: the first is ambient varying-ring reduction/limit and tensor-Hom calculus, while the second constructs geometric finite exceptional/compact-support operations and their enriched adjunction using that calculus.

- lem-coef-derived-system-evaluation-calculus vs prop-coef-integral-exceptional-adjoint: the new calculus has no exceptional functor or invertible reconstruction assertion; step 2 of the parent proves reconstruction from its unit, effectivity and complete-cone vanishing.

- lem-coef-finite-adjunction-diagram-realization vs prop-coef-integral-exceptional-adjoint: the new tool concerns finite-coefficient systems and no integral exceptional adjunction, constructibility or interval; steps 1--7 of the parent supply those integral conclusions and the comparison to the dual expression.


## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q14 prop-coef-integral-exceptional-adjoint --no-push` printed `OK (not pushed) deliver/Q14/prop-coef-integral-exceptional-adjoint at dd3d03b652: preflight passed`. The mathematical files and 42 citation pairs passed together. After adding this validation record, I run the same dry run once more so that the final report is part of the accepted sandbox. No push, Lean compilation, Lake or build is performed by this worker.

## Second reading by Q14

Fresh second-reader audit, 2026-10-16. I read delivery-errors B–E first, then the report, GOAL, dag-sync, worker/stage-1 rules, and the master chapter, unit and item sources. The source copies are read-only under `/home/ubuntu/weil-launcher-nt/literature/`. The shared repository and both Lean source checkouts were read only; no Lean, compiler, Lake, build or agent was started.

- Step 1: checked against blueprint proof paragraph 1 and the complete statements of integral Verdier, integral-operation preservation and finite pullback Tor preservation; PASS, including the sign calculation and constructibility before each dual.
- Step 2: checked every cited statement (system adjunction, normalized effectivity, category definition, triangulated closure, derived change of rings, Roos completeness and zero-cone criterion); PASS: the actual unit has invertible reductions, and its complete cone vanishes.
- Step 3: checked blueprint paragraph 1, the specified system dual formula, evaluation-defined Verdier comparisons, completed pullback, dualizing construction, effectivity and the current finite-exceptional statement; PASS after repairing its stale citation quote. The contravariant middle arrow uses the inverse of the entire map q_L.
- Step 4: checked blueprint paragraph 2, gamma and its precise projection clause, scalar-extension/restriction Hom adjunction and global-Hom identification; PASS. Reconstruction is applied to Q, and e_n (u_Q)_n = 1 makes the projection h_n; no internal-Hom tensor/base-change isomorphism is required.
- Step 5: checked each cited statement, in particular the finite enriched etale adjunction's compactifiable/Noetherian hypotheses, bounded-below site comparison, compact-support preservation, coherent-system realization and effectivity; PASS after repairing the finite-exceptional quote. The two counit comparisons are inverted in the correct Hom variables.
- Step 6: checked against the actual system isomorphism of step 5, lambda's projections in step 4, and current finite-unit/counit equations; PASS after repairing the finite-exceptional quote. Naturality gives both triangle identities, and the displayed adjunct equation includes c_K inverse and c_L.
- Step 7: checked blueprint's final sentence and the whole integral-dualizing statement, including its chosen finite transitions and the diagram-realization node's same-system requirement; PASS. It specializes the constructed adjunction to the coefficient unit.
- New node lem-coef-derived-system-evaluation-calculus: checked all quantifiers and notion references, Stacks 06YS/lemma-K-flat-resolution, 0A95/lemma-RHom-well-defined, 0941/lemma-derived-limit-is-ok and 079P/theorem-K-injective-embedding-grothendieck in their actual TeX files; PASS as a statement-only, explicitly agent-formulated coherent construction obligation. Those tags support its foundations and are not falsely described as stating the entire tool. Fresh whole-DAG/blueprint and Mathlib searches found no duplicate or exact leaf; fixed-ring strict limits and degree-zero scalar adjunction do not supply the simultaneous mapping-system functor and gamma.
- New node lem-coef-finite-adjunction-diagram-realization: checked the complete finite-exceptional blueprint proof, its current DAG statement, the same resolution sources, and every notion dependency; PASS as a statement-only coherent finite-system obligation. Its domain is normalized finite-Tor systems, not arbitrary bounded constructible modules at a nonregular quotient ring. Fresh searches found no duplicate or exact Mathlib leaf; the existing compact-support reduction-tower functor only has integral inputs and fixed completed coefficients, and does not state this finite-system exceptional/enriched construction.

Small cases: zero inputs and the empty scheme give zero mapping complexes; f = id gives biduality and the identity finite adjunction. On the coefficient point P = R and N = (A_n) give the usual completion projections. For P = Q = R/varpi the derived reduction is the two-term complex, not its degree-zero quotient; the stated gamma projection still sends the identity to the identity. The finite tools require n >= 1, and no claim that R/varpi is flat over R is used. The already documented STATEMENT-DISPUTED repair for empty-scheme dimension remains valid: nonnegative integer bounds make the interval well typed without excluding the empty scheme.

Changes made by this second reading:

- Replaced the three citations of lem-coef-finite-exceptional in steps 3, 5 and 6 with its current verbatim statement. The previous quotes were the older blueprint wording; the dry run rejected them even though the current theorem supplies the facts used.
- Ran independent LeanFinder searches using derived-mapping/homotopy-limit and adic extraordinary-image vocabulary, and a Mathlib CategoryTheory grep; appended their actual results to searches.jsonl and each new node's mathlib_searches. The returned derived-functor transformation and underived sheaf/condensed adjunction declarations do not state either tool. Both nodes remain unsplit, with zero Mathlib leaves.
- Checked all 42 citation pairs against the current node statements after the repair; all quotes are verbatim. The mathematical proof, statements, source qualifications and first worker's Review by Q14 section are retained.

The required command is used without a trailing dot: this installed deliver.py accepts only group, item and optional --no-push, and prints usage if given the prose's trailing dot. Validation and delivery results follow below.

Second-reader validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q14 prop-coef-integral-exceptional-adjoint --no-push` printed `OK (not pushed) deliver/Q14/prop-coef-integral-exceptional-adjoint at accc415ee6: preflight passed`. The sandbox contains two new statement nodes and zero Mathlib leaves. I now run the required delivery, which repeats preflight on this final report as well.
