## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-invariant-local-curve-pencils.json: item, sixteen-step quotient-free proof, retaining the reviewed marking-equivalence correction; no Mathlib match.
- lem-sfb-ample-curve-two-section-pencil.json: new statement-only lemma, now giving orbit-separated section pairs and their finite norm pencils over any field; unsplit, no Mathlib match.
- lem-sfb-separating-pair-open.json: new statement-only lemma, now giving the nonempty separating open for norm pairs on the original smooth curve in every sufficiently high degree; unsplit, no Mathlib match.

Two new nodes, zero Mathlib leaves. citations.json has an exact quotation from the statement of every node used by every step (48 entries). The returned report, item and auxiliary statements are retained in returned-report.md, returned-item.json and the two *.returned.json files. Original searches and their outputs remain intact. Ten additional searches were run because the two auxiliary statements changed; their actual outputs are in *.repair-search-results.json and searches.jsonl. No Lean, compiler, Lake, or agent was started; all writes are in this sandbox.

Attachments: none. Read-only searches of the project's WeilConjectures tree for the item blueprint tag, invariant pencils, separating pencils and orbit pencils found no declaration proving the item or either changed input. The searches in Mathlib were all made through msearch.py. I read the original outputs and the repair outputs: Proj constructions and fraction predicates, zero-locus identities, elliptic-curve coordinate formulas, etale algebra structure, and etale stability do not construct these section pairs or their parameter open. Both new statements received Loogle, grep, LeanSearch and two semantic phrasings. Every repair service answered successfully.

WANTED: de Jong, Families of curves and alterations, Ann. Inst. Fourier 47 (1997), 599–621, §§3.3–3.5, especially printed pp.605–607, for this item and the auxiliary nodes. The local PDF is absent. I read the publisher scan at https://www.numdam.org/item/10.5802/aif.1575.pdf, especially PDF pages 7–9. That source uses the quotient. This repair is explicitly an agent-written replacement of its node-level linear-series construction by products of translates, as requested by the return. It does not attribute the norm lemmas to de Jong. I read the local Stacks coherent.tex lemma-ample-on-fibre (0D2M), lemma-kill-by-twisting (02O1), lemma-proper-finite-fibre-finite-in-neighbourhood (02OH), varieties.tex lemma-generated-by-dim-plus-1-sections (0B3Z) and lemma-separate-points-tangent-vectors, and curves.tex lemma-generically-etale (0C1C). Those support the auxiliary formulations; the parent proof uses only its cited DAG statements. No SGA source is used.

## Repair of C1/F

The return is correct: lem-per-projective-finite-group-quotient is dropped item 1814 of the 2026-10-19 route pivot. The earlier report wrongly called it an available generic tool. The initial mandatory dry run on the retained version passed mechanically at c18106e1376; that did not repair or authorize the dropped dependency.

I removed that node from the proof, proof_deps, tool declarations and citations. There is no quotient Y, quotient morphism q, invariant structure-sheaf identity or quotient function-field identification anywhere in the revised argument or new auxiliary statements. The effective image G of J in Aut_S(N) is a finite group, not a quotient scheme. Products are taken over G to avoid forcing p-th powers from a nonfaithful kernel. The action on the generic curve is faithful because N is integral and separated. The construction uses B = tensor over g in G of g^*L on N and the actual section product N_G(a). Its invariance follows by permuting factors. The parent lifts ordinary sections a,b and only then takes their products; wild invariant-section lifting and averaging are never asserted.

This changes precisely the quotient-dependent construction in steps 2–9 and 15, with the direct-map wording in step 16. Steps 10–14 retain the already checked closed-image, coordinate-change and finite-cover arguments. The original fixed-field norm-of-denominators argument is retained in returned-item.json as historical work but is not needed or cited in this delivery. The unit and chapter routes and their records are unchanged; this is the node-level quotient-free alternative explicitly requested by the return. No un-drop is requested or presumed. The previously used finite-field-action, quotient-dimension, quotient-base-change and relative-very-ampleness inputs also disappear.

## Statement clarification: STATEMENT-DISPUTED

The imported equivalence combined marking avoidance with fibre etaleness. For the identity C=P^1_K and M={0}, the map is etale above 0,1,infinity but those fibres meet M. The corrected statement separates the finite-etale fibre assertion from its additional disjointness assertion. All existence assertions, hypotheses and marking-avoidance conclusions are retained. The return explicitly accepted this correction; it remains the only change to the item's statement.

Nothing remains unfinished at the requested one-level split: the two auxiliary statements intentionally remain unsplit. They isolate the special-fibre and generic linear-series inputs. The relative lifting, simultaneous choice in a fixed residue class, spreading, finite cover, three-fibre avoidance and finite separable descent are all carried by the item's sixteen steps. Neither auxiliary restates those relative conclusions.

## Review by NK

I read the full statements of all the parent proof's cited nodes, including definitions, and regenerated citations.json from those actual statements. I checked C4 by matching each use to the asserted clause, rather than using a node's proof or a tag as an extra theorem. I checked C1 by identifying all non-elementary inputs and naming them in uses. The finite field-action and quotient theorem are absent, not renamed or used through a definition.

Step 1 uses the normal-model theorem's scalar-extension case E=K, L=k(X), including unchanged smooth generic fibre, finite surjectivity, H-projectivity, pure geometric fibres and functorial actions. Normality of S identifies its normalization in K with S on affine charts. Step 2 uses projective-implies-proper, finite-type-over-Noetherian, proper closed image, and injection of affine coordinate domains into their fraction field. The image of N contains the generic point, giving nonempty fibres. For faithfulness on C, the equalizer ideal vanishes in the function field and is zero in every affine domain; separatedness makes that equalizer closed. This explicitly supplies the reduction to the effective group, without a quotient theorem.

Step 3 constructs its tensor line and sections from the definitions of projectivity, module pullback, tensor product and locally free rank one. The composition identification in pullback sends h^*g^*L to (gh)^*L; the group-index permutation preserves both norm sections, hence their coordinate ratio. Local frames also show that pulling the products to a fibre, or taking powers, gives the stated formulas. This is an elementary construction and calculation, not a hollow definition or a new theorem about descent of a bundle.

Step 4 uses the affine function-field identification and the projective-ample theorem on N_U and its fibre embeddings. The domain A and its fraction field are infinite even over a finite ground field: the nonzero maximal ideal at a closed point distinguishes that point from the generic point of positive-dimensional S. The special fibre is a nonempty projective curve, with possibly nonreduced or reducible structure. The action there may have a kernel; the special-fibre auxiliary does not assume faithfulness.

Step 5 applies the orbit-separated auxiliary only to that special fibre. Powers of its ordinary sections give powers of its norm pair. The explicit finite power map on P^1 preserves finiteness, so a multiple of the initial degree reaches both the ordinary lifting threshold and the generic norm-open threshold. The lifting node explicitly supplies each ordinary section on a neighbourhood; intersecting those neighbourhoods and shrinking affinely is legitimate. No invariant functor is applied to a surjection. Step 6 uses the general flat cohomology base-change node at H^0 (localization A to K, proper hence qcqs morphism, invertible hence quasi-coherent module), plus proper coherent cohomology for finite dimension. Clearing denominators chooses actual global basis representatives. The displayed perturbations keep their residue classes and form a dense set in the ordinary section-pair affine space. Step 7 uses the new generic norm-open statement exactly for (C,L_K,G,n); faithfulness, smooth geometric integrality, ampleness and the degree threshold have all been checked. Intersecting the dense set with this open gives the two required fibre behaviours simultaneously.

Step 8 uses the nonvanishing theorem for the closed common-zero set of the norm sections, proper closed image to remove it away from s, and the generating-sections/projective-coordinate construction to obtain an actual morphism on N_U. Proper-to-separated-target applies because P^1_U is proper over U. Step 9 applies the proper-finite-fibre-near theorem at each point of P^1_s, removes the proper image of the complementary closed target set, then uses proper-plus-finite-fibres over the Noetherian target to conclude finiteness. It no longer composes a map with q. Step 10 uses the generic norm-open surjectivity and finite closed image; A[t] embeds in K[t] on both target charts, proving the generic target fibre is dense.

Steps 11–13 retain the reviewed avoidance argument. The generic norm-open supplies an actual nonempty etale open. Its complement in the Noetherian integral curve has dimension zero and is finite by the cited topological lemma. The finite map sends it and the finite marking to a finite closed set of target values. A polynomial vanishing on those values is written explicitly. The product u(a)l(b)u(c) parameterizes a dense cell in SL_2; the avoidance conditions give a nonzero polynomial in three parameters, and density of A^3 supplies a determinant-one matrix over A. Thus it extends over the entire affine base. The finite-etale fibre conclusion follows from the cited etale base-change and finite-etale algebra statements; marking avoidance is checked independently. Step 14 uses Noetherianity and quasi-compactness to extract a finite affine cover from the closed-point neighbourhoods.

Steps 15–16 use the zero-dimensional normal-integral identification S=Spec K, smooth-normality of C, the projective-ample theorem, and the new generic norm-open statement directly on C. A separable closure is infinite by the displayed polynomial argument, so that open has a point there even when K is finite. Only finitely many ordinary section coefficients and coordinate-change coefficients are chosen. The algebraic-generators theorem and the separable-closure theorem give a finite separable coefficient field E. Membership in the open is preserved in that subfield by its nonvanishing equations. The etaleness field-extension theorem gives the needed descent, and a nonempty finite scheme stays nonempty under field extension, giving disjointness descent. The normal-model theorem identifies the final normalization with C_E, the field tensor product and the extended action fixing E. Its invariance comes from norms, not from factoring through a quotient.

For the special-fibre auxiliary, I checked the construction over finite fields and on nonreduced/reducible curves. One first chooses an ample-power section avoiding every generic point, including zero-dimensional components. Its zero locus is a finite set. In a sufficiently high common multiple of that degree, restriction to the finite union of its G-translates is surjective by coherent Serre vanishing. An invertible module on that finite reduced scheme is trivial, so one can choose a section nonzero at all those points. Raising the first section gives the same degree. The two orbit-saturated zero sets are disjoint. Their norm pair is base-point free; the tensor of translated ample bundles is ample, so its pencil cannot contract a positive-dimensional component, and properness then gives finiteness. This argument explains the power and why no infinite-residue-field or tame-action hypothesis is needed. These ingredients belong to the future split of this statement, not to uncited steps in the parent.

For the generic auxiliary, I checked nonemptiness over an algebraic closure and openness over F. A faithful finite constant group has a free geometric orbit outside the finitely many fixed loci of its nonidentity elements. For all sufficiently high powers, restriction to the first infinitesimal neighbourhoods at this one orbit is surjective by Serre vanishing. Choose b nonzero at every orbit point and a with one simple zero there and nonzero at all other orbit points. Then N_G(a)/N_G(b) has a simple zero, so its differential is nonzero in every characteristic. Separately, global generation over the infinite algebraic closure gives pairs with disjoint orbit-saturated zero sets by avoiding a finite set of zeros. Base-point freeness is open by the proper incidence image, and nonzero differential is open: N_G(a)dN_G(b)-N_G(b)dN_G(a) is a polynomial in the section coordinates with values in the finite-dimensional global section space of B^(2n) tensor Omega_C/F. These two nonempty opens meet in the irreducible pair affine space. The nonzero-differential/etale-open criterion is exactly 0C1C. This also proves that the resulting open is defined over F and that no prime-to-|G| assumption is hidden. These arguments are recorded here for the next worker; the new node itself contains only its statement.

Small cases checked: trivial actions; a kernel of characteristic-divisible order (removed before taking generic products); faithful wild translations of P^1; finite ground fields and finite residue fields; reducible and nonreduced special curves; zero-dimensional special components in the auxiliary; empty marking; characteristic two; and the Frobenius pencil. Keeping a characteristic-p kernel in the product would fail the simple-zero check, so step 2 is essential. Purely inseparable generic pencils are excluded by the norm-open's nonzero-differential condition. Every parent step is shorter than 2000 characters, so no long step conceals a lemma. The two non-elementary linear-series constructions are exactly the two statement-only nodes. Off-unit generic tools are declared in split_report.tool_uses; definitions need no route exception. Blueprint from.place and same_as are filled; ancestor still returns None, with the retained complete via ancestry. No chapter/unit or maintainer-owned field was changed.

## Not duplicates

lem-sfb-ample-curve-two-section-pencil vs lem-sfb-invariant-local-curve-pencils: the auxiliary is a single-fibre ample-series input with no normal model, relative lifting, generic separability, marking, constants or prescribed fibres. The parent performs those constructions in its steps.

lem-sfb-separating-pair-open vs lem-sfb-invariant-local-curve-pencils: the auxiliary gives a parameter open in an ordinary section space for each large degree on one smooth curve; it says nothing about prescribed special-fibre residue classes, spreading over a base or marking avoidance.

lem-sfb-ample-curve-two-section-pencil vs lem-sc-rational-function-morphism: the existing node starts with a given rational function on a smooth curve; it supplies neither ample sections nor disjoint orbit-saturated zero sets on an arbitrary projective curve.

lem-sfb-ample-curve-two-section-pencil vs lem-sc-morphism-from-function: the existing node gives finiteness for an existing function on a smooth curve, without the section existence or possibly nonreduced/reducible source.

lem-sfb-separating-pair-open vs lem-sfb-invariant-separating-parameters: invariant rational field parameters do not supply sections in every high ample power, base-point freeness or an open in the section-pair parameter space.

lem-sfb-ample-curve-two-section-pencil vs lem-a1-affine-groupoid-invariant-norm: the existing node proves an invariant identity for affine determinant norms; it has no existence of sections, ample line bundle or pencil. Product invariance in step 3 is an elementary group-index permutation.

lem-sfb-separating-pair-open vs lem-a1-affine-groupoid-invariant-norm: the existing invariant identity does not prove base-point-free pairs or the nonempty nonzero-differential open on a smooth curve.

lem-sfb-ample-curve-two-section-pencil vs lem-a1-affine-groupoid-polynomial-norm-invariant: coefficientwise invariance of one affine polynomial norm does not give orbit-separated global sections in an ample power.

lem-sfb-separating-pair-open vs lem-a1-affine-groupoid-polynomial-norm-invariant: polynomial norm invariance does not give the high-degree separating parameter open or nonzero differential.

lem-sfb-ample-curve-two-section-pencil vs lem-zl-prescribed-point-eventual-jet-system: the existing result supplies prescribed-point interpolation and immersion under a fixed algebraically closed compactification datum; it has no group norm, orbit-disjoint pair or invariant-pencil parameter open.

lem-sfb-separating-pair-open vs lem-zl-prescribed-point-eventual-jet-system: the existing result supplies prescribed-point interpolation and immersion under a fixed algebraically closed compactification datum; it has no group norm, orbit-disjoint pair or invariant-pencil parameter open.

lem-sfb-ample-curve-two-section-pencil vs lem-trf-finite-surjective-ample-reflection: the existing result reflects ampleness across a given finite surjective map, whereas the new statement constructs norm-section pairs and their pencils without any given finite quotient.

lem-sfb-separating-pair-open vs lem-trf-finite-surjective-ample-reflection: the existing result reflects ampleness across a given finite surjective map, whereas the new statement constructs norm-section pairs and their pencils without any given finite quotient.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-relative-kill-by-twisting: the existing result is higher-direct-image vanishing; it does not construct sections with orbit-disjoint zeros or norm pencils.

lem-sfb-separating-pair-open vs lem-pc-relative-kill-by-twisting: the existing result is higher-direct-image vanishing; it does not construct sections with orbit-disjoint zeros or norm pencils.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-q3-affine-open-twist-vanishing-independent: the existing result gives higher-direct-image vanishing on one affine base open, without section pairs, group norms or their separating open.

lem-sfb-separating-pair-open vs lem-pc-q3-affine-open-twist-vanishing-independent: the existing result gives higher-direct-image vanishing on one affine base open, without section pairs, group norms or their separating open.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-m1-projective-graph-twist-vanishing: the existing result is vanishing for twists in a projective graph embedding, not norm-section pair existence.

lem-sfb-separating-pair-open vs lem-pc-m1-projective-graph-twist-vanishing: the existing result is vanishing for twists in a projective graph embedding, not norm-section pair existence.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-q2-chow-twist-finite-cohomology: the existing result gives coherence and finite cohomology for one Chow twist, with no group-action or pencil assertion.

lem-sfb-separating-pair-open vs lem-pc-q2-chow-twist-finite-cohomology: the existing result gives coherence and finite cohomology for one Chow twist, with no group-action or pencil assertion.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-e4-affine-restricted-twist-fixed-degree: the existing result is vanishing in one cohomological degree on one affine base open, not orbit-separated sections or norm pencils.

lem-sfb-separating-pair-open vs lem-pc-e4-affine-restricted-twist-fixed-degree: the existing result is vanishing in one cohomological degree on one affine base open, not orbit-separated sections or norm pencils.

lem-sfb-ample-curve-two-section-pencil vs lem-pc-coherent-hi: the existing result gives coherence, finite-dimensionality and higher vanishing; it supplies no section-pair or norm-pencil existence.

lem-sfb-separating-pair-open vs lem-pc-coherent-hi: the existing result gives coherence, finite-dimensionality and higher vanishing; it supplies no section-pair or norm-pencil existence.

lem-sfb-separating-pair-open vs lem-sfb-curve-riemann-hurwitz-numerical: the existing result is the genus formula for an already given separable finite map, not existence of norm pencils.

lem-sfb-separating-pair-open vs lem-a1-nonzero-differential-generically-etale: the existing result tests the differential of an already given morphism; it does not supply the sections, base-point freeness or nonempty open.

lem-sfb-separating-pair-open vs lem-a1-finite-map-curve: the existing result constructs an affine-curve compactification and affine-line map, not pairs in prescribed ample powers or their norm parameter open.

lem-sfb-separating-pair-open vs lem-a1-nonconstant-normal-curve-map-flat: the existing result is flatness of an already given nonconstant map to a normal curve, not existence or openness of separating norm pairs.

lem-sfb-ample-curve-two-section-pencil vs lem-weil-pbc-coherent-serre-vanishing: the existing result is coherent Serre vanishing, an ingredient for restriction surjectivity in a future split, not either full norm-section assertion.

lem-sfb-separating-pair-open vs lem-weil-pbc-coherent-serre-vanishing: the existing result is coherent Serre vanishing, an ingredient for restriction surjectivity in a future split, not either full norm-section assertion.

lem-sfb-ample-curve-two-section-pencil vs lem-weil-pbc-formal-systems-graded-vanishing: the existing result is higher cohomology vanishing for graded modules, without any group-section construction.

lem-sfb-separating-pair-open vs lem-weil-pbc-formal-systems-graded-vanishing: the existing result is higher cohomology vanishing for graded modules, without any group-section construction.

Whole-DAG statement searches for orbit sections, norm sections and separating pencils, and blueprint_refs searches for norm sections, orbit sections, pencil, orbit and separating found no equivalent node. Same-tag candidates above were opened and read. The two new nodes share only supporting Serre-vanishing material: one is valid over every special residue field without smoothness or faithfulness, the other assumes a smooth geometrically integral curve and faithful action and asserts a separating open in every sufficiently high degree.
