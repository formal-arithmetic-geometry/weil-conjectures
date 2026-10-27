## Worker report

Q76 split lem-sfb-finite-locally-free-ample-reflection by one level. The imported statement is unchanged. The sandbox initially had no node, report or search log, so I copied the live item. No repair note exists. No Lean file was written and no compiler or build was invoked.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-ample-reflection.json: four proof steps, status split; existing statement dependencies and metadata retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-pullback-section-norm.json: statement, unsplit, not a Mathlib match. It gives a section of the specified power downstairs, without an ampleness assumption.
- citations.json: one verbatim statement quotation for every step/node pair.
- report.md and searches.jsonl: this review and the executed searches.

### Attachments

None. I searched lean/WeilConjectures by the item's exact blueprint tag, by norm/finite/ample, and by the new node's concepts. CoordinateCoverDescent concerns a finite field extension and coordinate covers; it does not give the item for an arbitrary scheme morphism and an arbitrary supplied invertible sheaf. FiniteLocallyFreeNormCharts supplies the function-norm charts already represented by its existing DAG node. The library's proper-over-a-field ampleness notion in Modules/Ample is also not the absolute notion used here. No exact closed attachment was found.

### WANTED

None: all source passages required here are present locally.

### Problems found and decisions

No statement dispute. Stacks 0BD0 states existence of some ample line downstairs, but its proof explicitly proves ampleness of the norm of the given ample line. Stacks 0BCY gives the identification of that norm, for a pullback line, with the degree power of the supplied line. Thus the proof, rather than 0BD0's bare statement, supports this item's stronger specified-line formulation. I did not cite the bare existence-of-an-ample-line node as if it stated this identification.

The new section-norm node is a strict auxiliary assertion: it assumes no ample line at all, gives no affine locus and no ampleness conclusion, and works with one arbitrary section. The item's avoidance argument, surjectivity argument and affine-section criterion remain in its own proof. No new norm-existence or norm-ample node was created.

A key varying-rank issue is that absolute ampleness requires quasi-compactness and global sections. One cannot simply assert it is Zariski local on the base. I instead use one clopen rank stratum at a time, choose the avoidance section on the original ample source, take its restricted norm, and glue that section with zero on the open complement. This requires no common exponent across different rank strata and no theorem about arbitrary open restrictions preserving absolute ampleness.

The latest blueprint chapter, unit and direct-images proof (3) were read under literature/blueprint/latest. Its current direct-images route is compactification; this node is an inherited auxiliary tool through the earlier alteration/Picard branch and is not an attempt to replace the current unit proof. The ancestry command prints None, as it already does for the parent chain; I retained null rather than fabricating a blueprint ancestor. Whole-blueprint searches for norm, norm section, norm pullback, norm ample, finite locally free norm, ampleness finite, 0BCZ and 0BD2 found no blueprint statement of this auxiliary norm-section lemma; the broad norm/ample results were checked for relevant candidates.

The logged searches were all actually run with msearch.py. The new node records the exact queries for LeanSearch, Loogle, two LeanFinder phrasings and grep. The hits on Algebra.norm_ne_zero_iff require domain hypotheses and describe ring elements, not values in all fibres; norm_localization and det_baseChange cover ring calculations only. I read RingTheory/Norm/Defs.lean lines 40-105, including Algebra.norm at 60-62, norm_apply at 64, norm_eq_matrix_det at 82-84 and norm_algebraMap_of_basis at 87-91. None is a one-line specialization giving the sheaf-glued section. A tentative function-norm search was accidentally invoked with its tentative node id in the item slot; its search-only log was consolidated into this item's log and the otherwise empty tentative directory removed. No such node is delivered, and the recorded searches used by the delivery were run in this item's slot.

### Unfinished

Nothing required for this stage-1 delivery remains. The new auxiliary node is deliberately statement-only; its future split will carry the norm construction. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-finite-locally-free-pullback-section-norm vs lem-a1-affine-groupoid-basechange-polynomial-norm: polynomial norms after invariant-base extension in a groupoid, not sections of an arbitrary pulled-back line.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-a1-affine-groupoid-norm-prime-separation: separation of two geometric groupoid objects by an invariant norm, not a line-bundle section norm.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-a1-affine-groupoid-invariant-norm: invariance under groupoid source/target, not line-bundle sections.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-a1-affine-groupoid-orbit-fibres: the quotient fibres are groupoid orbits; no line-section norm conclusion.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-affine-invertible-finite-set-section: a section avoids a finite set on an affine source; no norm or prescribed power downstairs.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-finite-normal-ample-descent: existence of some ample line under a normal-integral finite cover; no assertion for an arbitrary section or specified pullback line.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-finite-function-norm-nonvanishing: regular functions and an already supplied norm family; no line-bundle section in the prescribed power.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-finite-locally-free-ample-reflection: the item concludes ampleness using avoidance and affineness; the auxiliary has no ampleness assumption or conclusion and only constructs sections.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-norm-frame-tensor-section-gluing: given function norms and trivializations upstairs, it glues an unspecified norm line with chosen frames; it neither identifies that line with the specified L^{tensor d} nor supplies a determinant norm or fibrewise nonvanishing.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-finite-trivialize-invertible-upstairs: local trivialization over a finite map, not a norm section of a specified power.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-semiabelian-algebraic-equivalence-norm: inversion and algebraic equivalence of lines on semiabelian varieties, not arbitrary finite locally free norm sections.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-finite-norm-invertible-sections: for a supplied function norm and arbitrary M upstairs, it produces some line N downstairs; its statement does not identify N with L^{tensor d} when M=f^*L.

lem-sfb-finite-locally-free-pullback-section-norm vs def-sfb-algebraic-space-groupoid: a definition of groupoid data, not a line-section norm theorem.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-affine-finite-point-scalar-separation: scalar interpolation on affine schemes, not a norm section.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-sfb-affine-invertible-section-fibre-correction: correction of one residue value while preserving old values; no norm construction.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-pur-finite-flat-kummer-norm-degree: Noetherian Kummer-transfer compatibility and degree on smooth proper curves; the current node has no Noetherian, coefficient, curve or invertibility-of-an-integer hypothesis and concerns arbitrary line sections.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-pd-finite-locally-free-norm-charts: regular-function determinant charts, no gluing of line-section coefficients into a specified tensor power.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-pd-finite-free-norm-prime-criterion: finite free ring algebra elements and prime ideals, not sheaf sections of a line bundle.

lem-sfb-finite-locally-free-pullback-section-norm vs lem-trf-finite-surjective-ample-reflection: proper schemes over a Noetherian ring and an ampleness conclusion, not arbitrary line sections with neither properness nor Noetherianity.

## Review by Q76

I read divisors.tex Section Norms (0BCX), all of 0BCY (lemma-norm-invertible), 0BCZ (lemma-norm-map-invertible), 0BD0 (lemma-norm-ample) and 0BD2 (lemma-finite-locally-free-has-norm), including their proofs. The item has finite locally free plus surjective, not just finite; on each rank stratum this supplies exactly the positive degree needed by 0BD2. The line is the supplied L, and the norm is applied to powers of its pullback, so the exponent is dn, not just n and not a newly chosen ample line. Neither normality nor any Noetherian or properness assumption enters these source passages. I also read Morphisms 04MH (lemma-finite-locally-free), Properties 09NV (lemma-ample-finite-set-in-principal-affine) and 01PV (lemma-affine-cap-s-open), with their proofs, for the rank, section selection and affineness steps.

For the new node, 0BD2 constructs the determinant norm. On a cover where L has frame e_i and f_*O is free of rank d, write the given section as a_i(f^*e_i)^n. The desired local section is N(a_i)e_i^{dn}. If e_i=u_ij e_j, then a_j=a_i(f^sharp u_ij)^n, so N(a_j)=N(a_i)u_ij^{dn}; these local sections glue. This explicitly gives the pullback identity which 0BCY leaves to verification. The norm's vanishing assertion in 0BD2 and the converse nonvanishing argument in 0BCX/0BCZ give precisely the displayed saturated-locus equality. The new node's statement contains only the result, not this proof. It is self-contained, all its notions are defined inline or cite existing definition nodes, it has no proof/proof_deps, and the TeX has single logical backslashes. No domain or reducedness assumption is hidden in the norm: over a residue field, vanishing at one point makes multiplication fail to be surjective on the finite algebra, even when it has nilpotents.

Step 1 uses exactly the quasi-compactness clause in def-weil-pbc-ample-invertible-module and the pointwise surjectivity in def-weil-surjective-morphism. I wrote the finite-subcover argument, so no uncited descent theorem is invoked. The empty case follows from the same definition.

Step 2 uses only clause (1) of lem-weil-pbc-finite-flat-rank-iso, which explicitly states that the rank is locally constant and its fibres clopen. It does not use that node's degree-one/isomorphism clause. Its hypotheses finite, flat and locally of finite presentation are exactly the three conditions in def-pc-finite-locally-free, which is also cited. Restriction is to the inverse image of an OPEN in the target, with the same affine charts, not an arbitrary source open on which finiteness might fail. Positive degree is checked from a nonempty fibre; I corrected the wording from a supposed residue-field quotient to a unital map into that residue field, so no unstated maximal-prime identification is needed. The affine basis used is the scheme's definition, not the false assertion that an arbitrary intersection of affines is affine.

Step 3 uses the finite-fibre clause (2) of lem-weil-pbc-finite-closed-map-finite-fibres. Its hypothesis is finite, already given. I read the whole cited statement: no Noetherian hypothesis is required. lem-sc-ample-finite-principal-affine supplies a section avoiding the finite E and supported, in its nonvanishing locus, inside the open f^{-1}V; all its hypotheses hold on the original ample source Y. lem-weil-pbc-invertible-pullback-tensor supplies pullback composition with sections and the tensor section formula, so restriction gives the section to which the new node applies. The new node states exactly the t_U and saturated locus needed. Surjectivity is used again to deduce U_{t_U} is contained in V: an empty fibre outside V would otherwise satisfy the condition vacuously. I checked every cited statement, not its proof, for these conclusions.

Step 4 uses the defining sheaf property of def-weil-sheaf-of-modules-category only on a disjoint two-open cover, so extending by zero here is elementary gluing of a section of the original module; it is not a claim about extension-by-zero functors or quasi-coherent direct images. The nonvanishing equality is checked separately on the two opens. lem-sc-affine-cap-section-open explicitly applies to sections of positive tensor powers, and gives affineness because X_t is contained in the affine V. The final criterion is exactly def-weil-pbc-ample-invertible-module, with quasi-compactness from step 1 and positive exponent dn. No power-reflection theorem, locality-of-ampleness theorem or algebraization theorem is hidden in the assembly.

I checked B1-B10: one real auxiliary lemma, all objects and definitions present, exact tags/labels, no duplicate blueprint result, no unsupported Mathlib leaf or closed Lean attachment. For C1-C8 I opened every used statement, verified each hypothesis, supplied citations.json with verbatim quotations, and declared generic off-unit tools in split_report rather than writing maintainer tool_uses. D1-D5 hold because the item itself carries the finite-set avoidance, rank handling and affine-section argument; the auxiliary does not restate an item clause. For E1-E7 the tests were: empty base (vacuous conclusion); degree 1 (ordinary section); split degree d (coefficient norm is product over components); nonreduced k[epsilon]/(epsilon^2) (norm(a+b epsilon)=a^2, detecting exactly the residue zero); disjoint rank-1 and rank-2 base components (the section is extended by zero and the exponent may depend on the chosen point); nonseparated base (choose V inside the stratum, never intersect two affines and assume affineness); arbitrary characteristic, including a degree divisible by the characteristic (determinant norm requires no division). The hypothetical degree-zero component is excluded by the actual surjectivity assumption. These checks found no false statement and caused the two explicit proof clarifications described above. Every non-elementary proof step is shorter than 2000 characters; none hides an unrecorded norm-line identification, since that identification belongs to the new auxiliary node.

This is a direct-delivery self-review under the brief; no second worker or subagent was started. The server split check has passed. The full server dry-run validation is recorded below; the push result is reported by deliver.py and in the final response.

### Validation

The full deliver.py --no-push run exited 0 with OK (not pushed) at 26ddd330441. The server preflight, check_dag and review_split passed. A local read-only JSON check verified all 14 step/node quotations verbatim, proof_deps equal to the union of uses, and unchanged item statement and stmt_deps. This report update is followed by a final dry run before the authorized push.
