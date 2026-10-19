## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-marked-strictification.json`: split item, five steps, statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-symmetric-nodal-blowup.json`: new statement-only geometric operation along the whole closure of one node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-smooth-branches-strict-chart.json`: new statement-only chart criterion assuming smooth components in every fibre, unsplit; no Mathlib match.
- `citations.json`: verbatim statement quotations for every cited node of every step.
- `searches.jsonl`: earlier genuine records retained and genuine searches for the replacement statements appended. Earlier searches about the discarded route are retained, but are not presented as searches for the new statements.

The unlanded nodes `lem-trf-valuation-stable-uniqueness-strict-target` and `lem-trf-valuation-strict-pushout-gluing` are withdrawn from this delivery overlay; neither is in the shared repository. Their original files, the returned proof, the prior report and its citations remain in the sandbox's `returned-proposal.json`. No existing DAG node was deleted. The current shared item is unsplit and has the same statement as the returned proposal; its untouched fields were rebased from the shared file. No git command was run in the shared repository.

## Attachments

None. Read-only searches of `WeilConjectures/` for the item id, its blueprint tag, strictification, strict semistability, nodal blowups and branch charts found no exact project declaration for the item or the new local statements. No Lean was written or compiled. Mathlib searches returned standard smooth coordinates, standard etale pairs, Weierstrass good reduction/minimality, Lagrange interpolation polynomials and unrelated charts; these do not state either new input. I also read the grep hit `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean:322`: `HasSplitMultiplicativeReduction` is a Weierstrass reduction property, not a relative nodal chart theorem.

## WANTED

WANTED: local archival copy of `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Section 4.3 and Remark 4.5.2, for this item and its auxiliary statements. The primary arXiv PDF was read online; no document was downloaded and no SGA source is used.

WANTED: a published proof of the all-fibres smooth-branch-to-Zariski-chart criterion in exactly this finite-height, possibly non-Noetherian and nonseparated valuation setting. This is explicitly an agent-reconstructed unsplit local input, not a claimed quotation from Stacks 0CBY. That tag supplies etale neighbourhoods only. No absent document is treated as if it had been read.

## Return repaired, point by point

The return is the Q95 entry of 2026-10-17 21:13 UTC at head `615a09838e`, copied in the brief and `coord/returns/Q95.md`.

1. **C4/E1, invalid open-overlap modification.** The entire stable-model-overlap gluing argument is removed. No step treats `U_ij -> Y_i` as proper and no step applies strict-target stable uniqueness to it. The new proper maps are blowups along specified finite-type ideals and their finite composites. The proof uses an actual integer decreasing under each operation, so does not require stable uniqueness or a gluing cocycle.
2. **B2/C3/C4, undefined pushout.** The unlanded pushout node is withdrawn. Section 4.1 pinches closures of pairs of *generic singular points*, while this item's generic fibre is smooth; it supplies none of the previous Step 6's asserted paired branch closures. The replacement specifies the closed centre `C=closure{z}`, its open neighbourhood W, a global nonzero pi, the local thickness parameters and their inequalities, the ideal on both members of the cover `W, X\C`, the blowup chart rings and their morphisms, and the exact fibre-component conclusion used. Markings are preserved by the isomorphism off C, rather than an unspecified descent operation. The Zariski chart assertion is a separate self-contained node with its full all-fibres hypothesis.

The item statement is not disputed or changed. No hypothesis was added to it. The new argument is below the fixed chapter/unit level (SETUP's third level); no chapter or unit record was changed. Its blueprint ancestry is the historical auxiliary strictification branch of `lem-trf-local-term-locality`.

## Review by Q95

I read Temkin arXiv:0707.3953v3 Section 4.1 (printed pp. 24--25), the definition and nodal blowup calculations in Section 4.3 (printed pp. 27--29), Proposition 4.5.1 and Remark 4.5.2 (printed pp. 32--33). Remark 4.5.2 is the source of the strictification assertion, not a detailed proof. The split's origin is therefore `agent`: it reconstructs the already semistable smooth-generic case by symmetric nodal blowups rather than pretending the remark contains a chart-descent theorem. I also read Stacks 0CBY, `curves.tex`, `lemma-etale-local-structure-nodal-family`, including the actual-equations proof. The new nodes explicitly distinguish their reconstructed assertions from this source's weaker etale neighbourhood conclusion.

For the symmetric-blowup input I checked the three algebras and all maps against `uv=a`. Write `b=a/pi^2`. On the u-chart, `up=pi` and `v=pi b p`, so `uv=pi^2 b=a`; the v-chart is symmetric. On the pi-chart, `u=pi r`, `v=pi t`, and `rt=b`. These are the actual subalgebra blowup charts after cancelling torsion; no relation `u^2 w=a` with a nonreduced fibre is substituted for them. They are finitely presented torsion-free algebras over the valuation base, with one-dimensional reduced nodal or smooth fibres. After etale pullback this addresses flatness and finite presentation even when V is non-Noetherian. The fibre inserted at a centre point is the projective conic `U V = b(s) P^2`: a smooth conic if `b(s)` is nonzero, or two distinct lines otherwise. Its two attachment points separate the old branches, including when both originally belong to one irreducible component. The old component's partial normalization and the new conic/lines are smooth along the inserted fibre. Exceptional components cannot become an old fibre component: they are contracted to a point whereas the old components map onto a curve.

The supporting statement includes the substantial local-data/globalization work explicitly. It assumes a finite singular set and specifies a neighbourhood of the *whole closure* C, not an affine neighbourhood of an arbitrary finite set. W is allowed to be nonaffine and is covered by finitely many affine nodal chart neighbourhoods. Over a separably closed valuation base the unramified singular scheme is locally a closed subscheme of an open of the base: generizations at a given singular point form a chain. For an element pi vanishing exactly at the base specializations of `z|S`, C is an open-and-closed branch of `N intersect V(pi)` after excluding the other branches. This supplies the required neighbourhood W. There are finitely many local nonzero thicknesses along C; the divisible value group allows pi to have sufficiently small positive value in the relevant convex layer so that pi squared divides all of them. This simultaneously controls all specializations, with no discreteness assumption. The intrinsic ideal `J+(pi)` agrees on all these charts, and is the unit ideal off C on W. It therefore glues to the unit ideal on `X\C`. This support and the three chart assertions, not just a tag or informal phrase, are the statement of the new unsplit input. Its future split must prove them.

I changed an initial internal reconstruction after testing a rank-two valuation. A blowup supported only over the most closed fibre can leave an irreducible self-node in a more generic fibre; having smooth components in one closed fibre alone cannot imply a relative Zariski strict chart. The submitted files avoid both assertions: the operation acts on all of C, and the chart criterion requires that the components of *every* fibre are smooth. This higher-rank test is why the statement is phrased as it is.

For the chart input I compared the actual strict-pair definition in Temkin Section 4.3 with 0CBY's neighbourhood diagram. The node does not silently replace an etale neighbourhood of the curve by a Zariski open of the curve. It states that additional assertion as its own local geometric input, under smoothness of the reduced irreducible components of all fibres. A self-node of an irreducible fibre fails this hypothesis. The curve need not be separated or proper. At marked smooth points the input includes the coordinate adapted to the marking. At smooth unmarked points the source marking can be empty, matching Temkin's definition of an etale map of pairs. The valuation ring and its residue fields split the node branches; no arbitrary-base assertion is made.

I opened every cited node statement and checked the five steps individually:

- **Step 1** uses `lem-trf-nodal-family-fitting-singular` for the closed nonsmooth locus, unramifiedness and compatibility with fibres, and `lem-weil-pbc-unramified-over-field-discrete` for discreteness of each singular fibre. A fibre of the curve satisfies the former's nodal and finite-presentation hypotheses; applying it over that field is valid. Each fibre singular set is a closed subset of a quasi-compact finite-type fibre, so is quasi-compact; discrete plus quasi-compact is finite. The base has explicitly finitely many primes, giving finitely many singular points in total. The defect d counts actual points with a nonsmooth reduced fibre component, so is a finite nonnegative integer. The same proof applies to every intermediate curve; no hidden Noetherian assumption is used.
- **Step 2** uses `lem-trf-valuation-symmetric-nodal-blowup` for the exact local parameters, centre, ideal and resulting semistable proper blowup. Its finite-singular-set hypothesis comes from Step 1. The chosen point is nonsmooth, the generic fibre is smooth, and the marking is disjoint from the closed nonsmooth locus, hence from C. The operation does not invoke strict cofinality with a merely semistable target, and does not require any selected branch to descend.
- **Step 3** uses that same node's explicit assertion that *every* fibre component is smooth at points over C. Outside C the morphism is an isomorphism, so the local reduced component rings and their smoothness are unchanged. No bad fibre point is created over C; at least z is removed from the finite count. Thus d drops, and induction on the initial d terminates. This is the global construction, not a child node repeating the item. The marking and generic identity persist at each operation. `lem-weil-pbc-proper-fp-permanence` clause (a) states exactly the composition-of-proper-morphisms fact needed for b.
- **Step 4** uses `lem-trf-valuation-smooth-branches-strict-chart` only after d is zero. A component of a nodal fibre is automatically smooth at a smooth fibre point; the only remaining possible failures were the counted nodes. Its every-fibre smoothness hypothesis is now satisfied, as are the unchanged etale marking and smooth generic fibre hypotheses. The statement supplies actual Zariski pair charts, exactly what the item requires. No all-fibres assertion is inferred from one closed fibre.
- **Step 5** is elementary verification of the definition: the marking map is an isomorphism and the curve map is the proper composite already obtained. The generic map is the identity. On affine opens, a flat algebra over the domain V is torsion-free and injects into its K-localization; hence an isomorphism open containing the generic fibre is schematically dense in source and target. The unchanged etale marking is flat as well. These are the needed density clauses, not a separate unproved flatness/descent lemma.

Each citation in `citations.json` is verbatim from the statement actually used, including hypotheses. The proof steps have lengths 855, 817, 844, 603 and 704, all below 2000. The two genuine local geometric arguments are unsplit nodes with empty proof/dependency lists; the item carries the finite-defect induction. Neither node is an elementary two-line specialization of an existing node, nor a clause of the item repackaged: one describes a particular operation along one specified node closure; the other gives charts under a separately established fibre-component hypothesis and has no modification conclusion.

I searched the whole DAG, source declarations and the entire imported blueprint via `blueprint_refs.py` for node closures, smooth branches, smooth components, strict charts, symmetric/nodal blowups and tag 0CBY. No exact or more general existing statement covers either new input. The tag hits were opened and read: the formal-local statement assumes a Noetherian local base and concludes an isomorphism of completions; the local-model statement concludes etale neighbourhoods; the nodal log-regularity statement concludes log regularity with Noetherian/log-regular hypotheses; the log-chart statement also permits etale curve neighbourhoods and assumes a log-regular base. None concludes the new operation or the all-fibres Zariski criterion. The pairs are distinguished below.

Small cases checked: empty curve and marking; a smooth curve (d=0, identity); height zero (the entire curve is smooth by the generic hypothesis); a node joining distinct components; a self-node; b(s)=0 and b(s) nonzero; characteristic two (the unit-b conic has no projective singular point U=V=0); a node in a more generic fibre of a rank-two base; and several nonseparated specializations of one node. The last case is why W is not required to be affine and C is not assumed a singleton. No statement assumes that restricting a proper map to an arbitrary source open is proper.

## What remains

The two new local geometric lemmas remain unsplit, as required for one-level stage 1. Their proofs, particularly the all-fibres Zariski chart criterion, are future DAG work. No Lean proof or compilation claim is made. The item is a natural-language split with these precisely stated dependencies, subject to the required server checks and independent maintainer review.

## Not duplicates

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valued-curve-etale-parameter: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: An etale rational parameter for a valued smooth function field.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-centred-valuation: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Centred valuation.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-finite-presentation-spread: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite-presentation spreading of a marked modification from a valuation ring.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-strict-semistable-model-normal: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Normality of a strictly semistable model with smooth generic fibre.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-exceptional-closed-image-criterion: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Closed-image exceptional components detect stability.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-riemann-zariski-local-colimit: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Valuation ring as the filtered colimit of centre local rings.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-multipointed-curve: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Multipointed relative curves.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-semistable-marked-base-change: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Arbitrary base change of semistable marked curves and fibrewise stability.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-semistable-dominates-stable: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Valuation comparison from semistable to stable modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-separably-closed-value-group-divisible: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Value group of a separably closed valued field is divisible.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-semistable-stable-contraction: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Contract a given semistable modification to a stable one.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-stability-locus: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Constructible stable locus and dense isomorphism open for a spread modification.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-common-strict-semistable-refinement: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Common strict semistable refinements of curve models.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-prime-convex-correspondence: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Prime ideals and convex subgroups of a valuation ring.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-nodal-dualizing-datum: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Jacobian-normalized dualizing datum of a relative nodal curve.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-reduced-fibre-modification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Reduced-fibre theorem after a separable alteration of an integral base.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-modification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Modifications and generic-fibre modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-formal-local-structure-nodal-family: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node gives completed local rings over a Noetherian local base, not a modification or Zariski chart.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-strict-semistable-cofinality: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Strictly semistable modifications are cofinal over a strict model.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-single-valuation-semistable-extraction: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Extract one residual-dimension-one valuation on a strict semistable model.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-semistable-normal-target-factorization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Factor a semistable marked modification through a finite normal target.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-abhyankar-inequality: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Relative Abhyankar inequality for a valued field extension.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-separable-perturbation-factor-selection: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Separable perturbation and factor selection.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-multipointed-curve-modification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Morphisms, semistability and stable modifications of multipointed curves.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-contracted-component-generic-data: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Generic constancy of numerical data of contracted nodal components.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-height-rank: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Prime-chain length versus valuation rational rank.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuative-domination-eta-normal: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Valuative domination criterion for eta-normal flat schemes.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-curve-finite-normalization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite normalization of a generically smooth curve over a separably closed valuation base.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-nodal-contraction-euler-defect: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Euler defect of contracting a nodal subcurve to a smooth point.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-component-factorization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Factorization of curve modifications detected on contracted components.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-strictly-semistable-curve: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Strictly semistable curve.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-elementary-semistable-chart-globalization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Globalize elementary semistable chart operations.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-convex-chain-rational-rank: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Convex subgroup chains are bounded by rational rank.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-rational-rank-zero-torsion: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Zero rational rank implies torsion.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-marked-nodal-dualizing-degrees: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Marked dualizing line bundle and contracted-component degrees.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-smooth-target-modification-exceptional-tree: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Exceptional fibres over a smooth target are rational trees.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-semistable-multipointed-pair: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Underlying marked pairs, semistability and geometric stability.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-strict-semistable-local-uniformization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Strictly semistable local uniformization along centred valuations.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-exceptional-local-criterion: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Semistable locus and the exceptional-tree local criterion.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-normalized-polynomial-residue-generation: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Residue generation by normalized irreducible factors.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-nodal-log-regularity: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node assumes a Noetherian log-regular base and concludes log regularity, not either of these geometric assertions.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-prime-field-valuation-rank: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Rank of a valuation on a prime field.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-abhyankar-finite-type-field-height: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Abhyankar height bound for valuations of finitely generated fields.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-horizontal-curve-models: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Horizontal curve models and schematic closures of markings.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-modification-proper-completion: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Proper completion of a modification near a nodal fibre.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-exceptional-blowdown: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: One exceptional blow-down over a finite-height valuation ring.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-modification-fibre-centre-finite: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite fibre-generic valuation sets and the modification locus.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-residual-curve-value-group: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Equality of values in a residually transcendental curve extension.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-birational-riemann-zariski-neighbourhoods: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Birational Riemann--Zariski compactness and affine valuation neighbourhoods.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-nodal-polar-section: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: A polar section on a proper valuation curve with one rational component.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-constructibility: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Constructibility of semistable and stable geometric fibre conditions.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-contracted-component-inclusion: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Inclusion of contracted fibre components in a common semistable model.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-finite-fibre-valuation-domination: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite fibre-valuation test for domination of curve modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-marked-curve-finite-type-model: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite-type integral models of multipointed curves.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-stability-field-descent: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Semistability and geometric stability are invariant under field extension.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-geometrically-reduced-eta-normal: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Generic normality of flat geometrically reduced families over normal bases.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-nodal-etale-chart: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node assumes a locally Noetherian log-regular base and allows an etale neighbourhood of the curve, not a Zariski neighbourhood.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-schematically-dense-open: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Schematically dense open subschemes.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-stable-reduction: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Stable reduction over finite-height separably closed valuation fields.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-exceptional-component-specialization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: An exceptional component has an exceptional component in each nonempty specialized closure fibre.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-base-modification-comparison-fibre-image: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Finite image of a projection fibre under a proper comparison after modifying the base.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-uniqueness-normal: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Uniqueness of stable modifications over a normal integral base.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-modification-spreading: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Spreading a prescribed stable valuation model to a quasi-alteration.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-birational-quasi-modification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Birational quasi-modification.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-no-isolated-contracted-fibre-component: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: A curve modification cannot contract an isolated whole fibre component.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-marking-semistable-separation: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Separate the marking on a strictly semistable curve.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-riemann-zariski-finite-refinement: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Valuation neighbourhoods and common finite Riemann--Zariski refinement.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-rational-rank: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Rational rank of an abelian group.

lem-trf-valuation-smooth-branches-strict-chart vs def-trf-strict-semistable-curve: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Strictly semistable relative curves.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-algebraic-height: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Height of a valuation is unchanged by algebraic extension.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-flat-fibre-generic-generalization: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Fibre-generic locus of a flat finitely presented morphism is stable under generalization.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-birational-quasi-modification-common-cover: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Common proper refinement of a finite valuation cover by quasi-modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-nodal-normalization-adjunction: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Normalization adjunction for a component of a nodal curve.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-curve-projective-preparation: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Normal projective preparation and locality for valuation-curve modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-stable-curve-diagram-noetherian-model: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Normal finite-type models of finite semistable modification diagrams.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-rational-valuation-linear-residue: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: A linear rational coordinate with transcendental residue.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-normal-approximation-finite-eta-modification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Noetherian approximation for finite eta-modifications.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-nodal-family-etale-local-model: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node gives etale neighbourhoods of both curve and base for an arbitrary nodal family, not intrinsic blowup data or a chart on an open of the original curve.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-normalized-graph-model: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Normalized graph image as an intermediate valuation-curve model.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-marked-strictification: the new node states Zariski pair charts assuming smooth components in every fibre; the existing node has a different conclusion: Marked strictification of a semistable curve model.

lem-trf-valuation-smooth-branches-strict-chart vs lem-trf-valuation-marked-strictification: the new node is one geometric input with specified centre or all-fibres smoothness hypotheses; the item starts with no such data and constructs a global marked modification by finite decreasing-defect induction.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valued-curve-etale-parameter: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: An etale rational parameter for a valued smooth function field.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-centred-valuation: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Centred valuation.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-finite-presentation-spread: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite-presentation spreading of a marked modification from a valuation ring.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-strict-semistable-model-normal: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Normality of a strictly semistable model with smooth generic fibre.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-exceptional-closed-image-criterion: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Closed-image exceptional components detect stability.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-riemann-zariski-local-colimit: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Valuation ring as the filtered colimit of centre local rings.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-multipointed-curve: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Multipointed relative curves.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-semistable-marked-base-change: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Arbitrary base change of semistable marked curves and fibrewise stability.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-semistable-dominates-stable: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Valuation comparison from semistable to stable modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-separably-closed-value-group-divisible: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Value group of a separably closed valued field is divisible.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-semistable-stable-contraction: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Contract a given semistable modification to a stable one.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-stability-locus: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Constructible stable locus and dense isomorphism open for a spread modification.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-common-strict-semistable-refinement: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Common strict semistable refinements of curve models.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-prime-convex-correspondence: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Prime ideals and convex subgroups of a valuation ring.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-nodal-dualizing-datum: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Jacobian-normalized dualizing datum of a relative nodal curve.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-reduced-fibre-modification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Reduced-fibre theorem after a separable alteration of an integral base.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-modification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Modifications and generic-fibre modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-formal-local-structure-nodal-family: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node gives completed local rings over a Noetherian local base, not a modification or Zariski chart.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-strict-semistable-cofinality: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Strictly semistable modifications are cofinal over a strict model.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-single-valuation-semistable-extraction: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Extract one residual-dimension-one valuation on a strict semistable model.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-semistable-normal-target-factorization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Factor a semistable marked modification through a finite normal target.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-abhyankar-inequality: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Relative Abhyankar inequality for a valued field extension.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-separable-perturbation-factor-selection: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Separable perturbation and factor selection.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-multipointed-curve-modification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Morphisms, semistability and stable modifications of multipointed curves.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-contracted-component-generic-data: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Generic constancy of numerical data of contracted nodal components.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-height-rank: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Prime-chain length versus valuation rational rank.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuative-domination-eta-normal: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Valuative domination criterion for eta-normal flat schemes.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-curve-finite-normalization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite normalization of a generically smooth curve over a separably closed valuation base.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-nodal-contraction-euler-defect: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Euler defect of contracting a nodal subcurve to a smooth point.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-component-factorization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Factorization of curve modifications detected on contracted components.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-strictly-semistable-curve: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Strictly semistable curve.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-elementary-semistable-chart-globalization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Globalize elementary semistable chart operations.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-convex-chain-rational-rank: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Convex subgroup chains are bounded by rational rank.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-rational-rank-zero-torsion: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Zero rational rank implies torsion.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-marked-nodal-dualizing-degrees: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Marked dualizing line bundle and contracted-component degrees.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-smooth-target-modification-exceptional-tree: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Exceptional fibres over a smooth target are rational trees.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-semistable-multipointed-pair: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Underlying marked pairs, semistability and geometric stability.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-strict-semistable-local-uniformization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Strictly semistable local uniformization along centred valuations.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-exceptional-local-criterion: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Semistable locus and the exceptional-tree local criterion.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-normalized-polynomial-residue-generation: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Residue generation by normalized irreducible factors.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-nodal-log-regularity: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node assumes a Noetherian log-regular base and concludes log regularity, not either of these geometric assertions.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-prime-field-valuation-rank: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Rank of a valuation on a prime field.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-abhyankar-finite-type-field-height: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Abhyankar height bound for valuations of finitely generated fields.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-horizontal-curve-models: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Horizontal curve models and schematic closures of markings.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-modification-proper-completion: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Proper completion of a modification near a nodal fibre.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-exceptional-blowdown: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: One exceptional blow-down over a finite-height valuation ring.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-modification-fibre-centre-finite: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite fibre-generic valuation sets and the modification locus.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-residual-curve-value-group: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Equality of values in a residually transcendental curve extension.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-birational-riemann-zariski-neighbourhoods: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Birational Riemann--Zariski compactness and affine valuation neighbourhoods.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-nodal-polar-section: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: A polar section on a proper valuation curve with one rational component.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-constructibility: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Constructibility of semistable and stable geometric fibre conditions.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-contracted-component-inclusion: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Inclusion of contracted fibre components in a common semistable model.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-finite-fibre-valuation-domination: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite fibre-valuation test for domination of curve modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-marked-curve-finite-type-model: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite-type integral models of multipointed curves.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-stability-field-descent: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Semistability and geometric stability are invariant under field extension.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-geometrically-reduced-eta-normal: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Generic normality of flat geometrically reduced families over normal bases.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-nodal-etale-chart: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node assumes a locally Noetherian log-regular base and allows an etale neighbourhood of the curve, not a Zariski neighbourhood.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-schematically-dense-open: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Schematically dense open subschemes.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-stable-reduction: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Stable reduction over finite-height separably closed valuation fields.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-exceptional-component-specialization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: An exceptional component has an exceptional component in each nonempty specialized closure fibre.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-base-modification-comparison-fibre-image: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Finite image of a projection fibre under a proper comparison after modifying the base.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-uniqueness-normal: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Uniqueness of stable modifications over a normal integral base.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-modification-spreading: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Spreading a prescribed stable valuation model to a quasi-alteration.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-birational-quasi-modification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Birational quasi-modification.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-no-isolated-contracted-fibre-component: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: A curve modification cannot contract an isolated whole fibre component.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-marking-semistable-separation: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Separate the marking on a strictly semistable curve.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-riemann-zariski-finite-refinement: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Valuation neighbourhoods and common finite Riemann--Zariski refinement.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-rational-rank: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Rational rank of an abelian group.

lem-trf-valuation-symmetric-nodal-blowup vs def-trf-strict-semistable-curve: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Strictly semistable relative curves.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-algebraic-height: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Height of a valuation is unchanged by algebraic extension.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-flat-fibre-generic-generalization: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Fibre-generic locus of a flat finitely presented morphism is stable under generalization.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-birational-quasi-modification-common-cover: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Common proper refinement of a finite valuation cover by quasi-modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-nodal-normalization-adjunction: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Normalization adjunction for a component of a nodal curve.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-curve-projective-preparation: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Normal projective preparation and locality for valuation-curve modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-stable-curve-diagram-noetherian-model: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Normal finite-type models of finite semistable modification diagrams.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-rational-valuation-linear-residue: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: A linear rational coordinate with transcendental residue.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-normal-approximation-finite-eta-modification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Noetherian approximation for finite eta-modifications.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-nodal-family-etale-local-model: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node gives etale neighbourhoods of both curve and base for an arbitrary nodal family, not intrinsic blowup data or a chart on an open of the original curve.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-normalized-graph-model: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Normalized graph image as an intermediate valuation-curve model.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-marked-strictification: the new node states a prescribed symmetric blowup along one whole node closure, with support, three algebras and fibre-component assertions; the existing node has a different conclusion: Marked strictification of a semistable curve model.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-marked-strictification: the new node is one geometric input with specified centre or all-fibres smoothness hypotheses; the item starts with no such data and constructs a global marked modification by finite decreasing-defect induction.

lem-trf-valuation-symmetric-nodal-blowup vs lem-trf-valuation-smooth-branches-strict-chart: the former constructs the specified local operation and proves component smoothness over its centre; the latter assumes component smoothness in every fibre and supplies Zariski charts, without constructing a modification.
