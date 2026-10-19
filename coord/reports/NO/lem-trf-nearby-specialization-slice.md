# Stage-1 repair report: lem-trf-nearby-specialization-slice

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nearby-specialization-slice.json`: item, split into eleven steps; statement unchanged, no Mathlib match.
- `citations.json`: 52 substantive verbatim statement excerpts, covering every citation of every step.
- `report.md`: this repair and self-review. No new node or Mathlib leaf is created.

The retained item, ancestry, original search records and earlier report were compared with the current shared node. The prior report remains in sandbox scratch `work/prior-report.md`; the final mathematical review below supersedes its seven-step gluing argument. The repository, source checkouts and launchers were read only. No Lean was written or compiled, and no agents were started.

## Attachments

None. The exact blueprint tag and nearby-cycle, vanishing-topos and oriented-product notions have no matching project declaration in the read-only slopmaster2 or upstream-master `WeilConjectures/` sources. Upstream declarations containing sorry would not establish an attachment.

## Wanted literature

WANTED: Orgogozo, *Modifications et cycles proches*, section 1, pp. 2–3, for the general-base slice discussion. The local archival PDF is absent. The proof is an agent synthesis using the available ILO volume and existing DAG interfaces; I did not claim to have read the absent PDF.

## What was wrong and what changed

A4 is repaired: `created.item` is `lem-trf-nearby-specialization-slice`, exactly the delivered id. The historical blueprint ancestor and via list remain intact.

C3/C4 and E5 are repaired by replacing steps 4–6 rather than merely expanding their prose. Stalk conservativity cannot construct a global map from a family of stalk isomorphisms and cannot infer equality of derived morphisms from equality on stalks. The first proposed repair still had those defects, although its mechanical dry run passed. It has been superseded by the eleven-step proof in this delivery.

Steps 1–3 now build the map before using stalks. A site triple C=(U→V←W) pulls back along e to components U_(a,v) indexed by compatible v,w. The strict-localization lifts define an actual map ell from E_v×S_(b) to U×V W. Restricting sections along ell and then the closed-fibre inverse-image unit gives a morphism of sheaves on every triple. Its adjoint is chi:e*psi_*F→i* j_* r_b*F. Step 4 applies chi to an injective representative and then the right-derived j_* unit. This constructs the global alpha without assuming that r_b* preserves injectivity. Only steps 5–6 use the point formulas and stalk conservativity, to prove this constructed morphism invertible.

The sliced map in step 7 has distinct, fully specified endpoints:
q_a* i_a* Rj_b,* K_b → i_T* Rj_T,* r_(b_T)* h_tilde* K.
It is i_T* of the mate of j_T* q_A* Rj_b,* K_b ≅ q_B* j_b* Rj_b,* K_b → q_B* K_b. Thus it uses the j_b counit and has the same coefficient pullback as the oriented comparison. The square of strict-local maps need only commute; it is not silently assumed Cartesian.

Step 8 checks the underived compatibility on every triple section: the two routes are pullback along the identical scheme map ell∘k=(D_T→D)∘ell_T, followed by the same closed-fibre unit. Step 9 takes the right-derived units of that section square on injective representatives. The normalized composite adjunctions identify the resulting arrows with the specified ordinary counit mates, giving the typed equality alpha_T∘e_T*beta = gamma∘q_a*alpha∘rho. Step 10 proves successive compatibility using the mate-pasting theorem on the displayed inverse-image squares. It does not use the abelian scheme Leray theorem to infer equality of module-valued maps on an oriented topos.

I also repaired two subsidiary citation gaps. Exactness of e* comes from the arbitrary-geometric-morphism constant-module inverse-image theorem, not from a scheme-only inverse-image theorem or a local projection statement. The stalk calculation now cites ind-etale strict-local invariance and the actual scalar-forgetting comparisons before using the abelian strict-henselization stalk formula. The two affine-morphism statements explicitly justify that j_b is qcqs.

## Searches and blueprint

The existing four logged Mathlib searches were read and retained with their actual results. They concern the whole slice assertion and return unrelated homological-complex restrictions, structure-sheaf specialization maps, or no nearby-cycle identifier. I also ran and read a second LeanFinder query for the concrete triple-generator restriction and mate-pasting construction. Its eight signatures concern open-module adjunctions, general section restriction, open restrictions of sheafed spaces and site-point fibre morphisms; none gives this oriented specialization-slice theorem. The exact new query and returned log record are appended to `mathlib_searches`. No unavailable service is represented as an absence result.

I searched the full DAG and blueprint, including `blueprint_refs.py ancestor` and searches for specialization slice and counit comparison nearby cycles. The ancestor remains `lem-trf-local-term-locality`; no blueprint node states the general assertion. I read the current main-20261015 ancestor proof, chapter and `sk-i-curve-zero` unit. The split stays within their auxiliary nearby-cycle input to normal-cone specialization and does not replace the contracting-correspondence route.

## Not duplicates

No new node is created. `lem-trf-nearby-geometric-slice` has only the trait/geometric-generic case. `lem-trf-oriented-nearby-strict-local-description` fixes a source point and varies the strict-local base, rather than fixing a base specialization and restricting to an entire geometric fibre. `lem-trf-oriented-point-cohomology` supplies pointwise cohomology, not the global morphism or its compatibility. `lem-trf-general-nearby-slice-test` has finite coefficients and bounded complexes, so cannot supply the present arbitrary annihilated ring and bounded-below statement. These nodes are not used to restate the item as a new lemma.

## Review by NO

I read ILO Exposé XI 1.4 and its explicit triple inverse-image formula, 1.9, 2.2–2.3, 2.7 and 4.3–4.5 in the available PDF. In particular 4.3 gives psi*(U→V←W)=U×V W, and the neighbouring argument explicitly constructs maps by restrictions on triples before proving them isomorphisms. I read Stacks sites-cohomology.tex Tag 0D6E (derived pushforward composition), derived.tex Tag 09T5 (derived adjunction), and the cited DAG statements for the strict-local formula, module comparisons, K-injective computation and mate pasting. The parent blueprint is agent-written; no claim is made that a single numbered ILO proposition contains every clause of the item verbatim. There is no new node whose source needs separate verification.

For step 1 I checked the types of d_a, b pi_a, the specialization 2-arrow and the component formula against the full universal-product statement. The exact constant-module theorem applies to arbitrary topoi, hence to e. For step 2 I checked that E_v is a finite limit inside the etale site of X_(a), using the finite-limits statement. The strict-localization limit supplies the lifts; the closed-germ bijection on the strictly henselian S_(b) makes their compatibility an equality of maps. Functoriality supplies strict henselianity and the structural maps. The projections in the definition of ell satisfy exactly the fibre-product equality.

For step 3 I checked that the oriented-point node states the triple inverse-image formula (not merely a formula hidden in its proof), and that the direct-image definition gives evaluation on E_v×S_(b). The scheme module-adjunction node specifies the units after forgetting scalars. The two component arrows are inverse-image restriction followed by the closed-fibre unit, so they are linear and natural for every triple morphism; specifying them on every object is an actual morphism of sheaves. For step 4 I opened the enough-injectives, bounded-below representative, K-injective Hom and right-derived-unit statements. Their hypotheses apply to module sheaves on the small sites, and the resulting chain map and derived-unit construction is natural up to homotopy. No unjustified acyclicity claim for a pulled-back injective is used.

For steps 5–6 I checked the qcqs hypothesis on j_b using the two affine-morphism statements. Strict localizations are affine, and j_b is their base change. I opened the ind-etale invariance statement, including its arbitrary-base-change and closed-geometric-point clauses, before identifying the tube over X_(a) with the tube over X. All module sheaves are killed by m, and the scalar-forgetting nodes compare both derived direct images and derived sections with their abelian forms, preserving the canonical restriction maps. Both stalk formulas therefore compute the stalk of the constructed alpha, rather than provide abstract isomorphic endpoints. The conservativity theorem is invoked only for invertibility of this map; it is not claimed to be faithful.

For step 7 I checked each of q_a,q_A,q_B,i_T,j_T,r_(b_T), their three commutative squares and the coefficient identification q_B* r_b* K = r_(b_T)* h_tilde* K. I read the exact counit-transpose formula defining beta and the module-linear composition statement. For step 8 I checked both projections of the displayed scheme square, then the values of both routes on an arbitrary triple section and compatible component. Thus the ordinary sheaf-mate compatibility is proved on sections, not asserted from naturality of a pointwise formula. For step 9 I checked the resolution map h_tilde*I→J, naturality of chi and of the derived units, the Hom-to-K-injective comparison, and the normalized composite-counit statement. These are precisely the statements used to derive the section square as an equality of the specified ordinary arrows.

For step 10 I opened all four clauses of the existing mate-pasting Mathlib leaf. Its first clause applies to the displayed two j-squares and separately to the two psi-squares. The second and third clauses, together with derived-composition normalization, pin down the composite derived adjunctions. The universal-product uniqueness applies to the projection-preserving identifications rho, so they compose coherently. This supplies successive compatibility without using stalks to test equality. For step 11 I checked that every conservative oriented point factors through one of the slices with a=f(x); exact inverse images commute with every cohomology degree even on unbounded complexes. Sheaf-level conservativity applied to 0→H^i(A) proves the converse vanishing assertion.

I checked the statement on f=id: the slice is RΓ(S_(b),K|), not generally the identity restriction claimed in the earlier report. For a=b it is the usual strict-local stalk situation. Empty X, the zero ring (including m=1), and negative r give zero objects or the same degree criterion with no exceptions. Nontrivial specializations still use S_(b), never the geometric point b as a substitute. Arbitrary base-change schemes are permitted: neither the stalk calculation nor the mate construction assumes they are finite type. The statement and all its original geometric and coefficient hypotheses are unchanged.

I checked B–E against the current files: all non-elementary inputs are actual statement citations, their hypotheses are checked above, proof_deps is the union of uses, every quote is verbatim, no new node is elementary/duplicate/a restated clause, and the largest proof step is 1298 characters. Tool uses from other units are explicitly declared in split_report.tool_uses; the mate-pasting theorem is already a Mathlib leaf. The generic input closures were checked not to reach this item. The remaining checks are run by the required remote tools, not by local checker execution.

## Source error

No error in the item statement was found; no statement change is proposed. The returned proof and the first proposed repair were invalid for the reasons above. This delivery replaces those arguments concretely.

## What remains

No part of the one-level split is intentionally deferred. General input nodes retain their current DAG states; none is silently claimed proved here. The final dry run and delivery command determine the delivery result.
