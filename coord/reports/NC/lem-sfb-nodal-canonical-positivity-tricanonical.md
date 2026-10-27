## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-canonical-positivity-tricanonical.json: unchanged statement, six proof steps rebased onto the current DAG.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-subcurve-dualizing-degree.json: one new statement-only lemma, unsplit; no Mathlib match.
- citations.json: all eighteen step/dependency pairs, with verbatim current-statement quotations.

The former proposed lem-sfb-reduced-curve-subcurve-vanishing is removed from the delivery: the current DAG now has lem-sfb-curve-ideal-h1-subcurve-obstruction, whose contrapositive supplies it. Its retained file and the previous complete report are archived under archive/ in this sandbox. All original search logs and full search-result files remain untouched. Thus this delivery has one new node and zero Mathlib leaves.

## Attachments

None. The project-library identifier and concept searches (tricanonical, nodal canonical) find no exact project declaration. The smooth curve very-ampleness theorem cannot state the reducible nodal result. No Lean was written or compiled.

## WANTED

None. All cited sources needed for this proof are available locally.

## Return repair and current-base comparison

The return approved the mathematical reading but refused landing because the side completion had not been promoted into the live queue. I compared returned head d39a04c5528800125bcb479a429a4bde814c3e92 with the retained files and current origin/sheaf-dag by read-only object decoding, without git commands. repair-comparison.json records the comparison (base 46093a8604e44a10a0020a02725a77e3cea058ef when checked). The live item remains unsplit; the delivery tool rebases in its own worktree and preserves maintainer fields. Promotion remains L's operation.

The required initial dry run found a newly existing Tag 0E3E node. I opened it and removed the duplicate proposed vanishing child. Step 4 now takes its actual implication, nonzero H1 implies a low-degree connected subcurve, and explicitly contradicts it using the strict inequalities proved there. I checked that a connected reduced Noetherian dimension-one subcurve is pure: a zero-dimensional irreducible component is disjoint from the other components and would be an isolated open-and-closed point. This matches the subcurves quantified over in Step 3. The empty subscheme is explicitly permitted by the existing obstruction node. Its cohomology is the ringed-space module cohomology also used by section-boundary exactness.

Three prior dependencies changed since the returned head, and I re-read their entire current records. The proper-nodal dualizing theorem now spells out completed local rings and smoothness instead of citing the nodal shorthand; its component degree conclusion and hypotheses otherwise agree. Step 1 now matches that explicit hypothesis, and its citation quote has been updated. Its fourteen-step proof obtains arbitrary-base duality and its adjunction normalization before the final component formula. The weighted component-degree theorem now assembles its formula through integral-filtration multiplicity and Euler-difference nodes; its statement remains unchanged, including positive generic lengths and reduced components. The normalized-component ampleness theorem now assembles finite normalized-component cover, finite-surjective reflection, finite-coproduct ampleness and the proper integral degree criterion; its statement also remains unchanged. Steps 2 and 3 retain the explicit dimension/reducedness and boundary checks from the earlier repair. Every other existing dependency record is unchanged in the comparison.

This is a substantive repair: the item changes proof, proof_deps and split_report against the returned head, one duplicate child is dropped, and current quotations and the report are updated. Original arguments, earlier report, source references and executed searches are retained in the sandbox. The statement is unchanged; no STATEMENT-DISPUTED correction is needed.

## Mathlib and blueprint searches

I read the retained search results and searches.jsonl. The surviving new node has two differently phrased LeanFinder queries, Loogle, Mathlib grep and LeanSearch, all executed with msearch.py and recorded verbatim in its mathlib_searches. The hits are polynomial-degree formulas, cotangent exactness and general module pullback adjunctions, not dualizing degrees for nodal subcurves. No service was unavailable. The item's added searches also found no match; its inherited searches are retained. No unchanged search question was rerun in this repair.

The chapter and unit were read. This supporting curve lemma keeps the inherited alteration/stable-moduli route, chapter, unit and null blueprint ancestor. Existing generic off-unit tools are declared in split_report.tool_uses. Whole-DAG same-tag and keyword searches and blueprint_refs.py searches found no duplicate of the numerical subcurve adjunction formula. Its from.place and via chain are retained. No SGA source is used.

## Not duplicates


lem-sfb-nodal-subcurve-dualizing-degree vs lem-trf-nodal-generic-component-closure: the existing theorem concerns closure of a smooth generic component in a valuation-ring family and constancy of boundary-point counts; it gives no dualizing degree or Euler-characteristic formula for an arbitrary subcurve.

lem-sfb-nodal-subcurve-dualizing-degree vs lem-trf-stacks-nodal-closed-subcurve: the existing theorem supplies nodality and boundary geometry only; it gives no numerical adjunction formula.

lem-sfb-nodal-subcurve-dualizing-degree vs lem-trf-complementary-pure-subcurve-components: the existing theorem identifies complementary unions of components only, with no dualizing sheaf or degrees.

lem-sfb-nodal-subcurve-dualizing-degree vs lem-trf-nodal-geometric-fibres-reduced: the existing theorem proves geometric reducedness only, with no adjunction formula.

lem-sfb-nodal-subcurve-dualizing-degree vs lem-trf-nodal-subcurve-boundary: the existing theorem gives nodality and finite reduced boundary points smooth on each side, but no dualizing degree or Euler characteristic. The new node's substantive assertion is the missing numerical adjunction formula, not its boundary description.

lem-sfb-nodal-subcurve-dualizing-degree vs lem-sfb-nodal-relative-dualizing-line: the existing statement concerns a relative dualizing line and base change, not restriction to a complementary subcurve or its numerical degree. Only its field-fibre interpretation would be relevant here; its broader base-duality formulation is not used.

The existing lem-trf-nodal-normalization-adjunction and lem-trf-marked-nodal-dualizing-degrees also do not give the new subcurve formula: they concern degrees/pullbacks on smooth normalizations of individual components, while the new formula concerns the arithmetic Euler characteristic of a possibly reducible connected union with internal nodes, and counts only its boundary with the complement. The item reuses the already existing direct component-degree theorem.


## Review by NC

I checked delivery-errors B–E against the node statements and local sources. For the item I read curves.tex 0E8X (lemma-tricanonical) and moduli-curves.tex 0E74 (lemma-stable). For the sole new node I read curves.tex 0E34 (the dualizing short exact sequence on a subcurve), 0BS5 (chi of the dualizing module), 0E37 (nodal curves Gorenstein and geometrically reduced), and 0E38 (subcurve nodality and reduced boundary smooth on each side). These give precisely deg(omega_C|Y)=-2chi(O_Y)+length(D), allowing disconnected Y, Y=C and empty boundary. The new node introduces its objects and notions, has empty proof/proof_deps and no proof sketch in its statement. It states an independent numerical adjunction formula, not an item clause. All prior full reviews are preserved in archive/report-before-20261023-rebase.md.

Step 1 uses the properness definition for separatedness and finite type, the finite-type Noetherian finite-presentation theorem on affine charts, the relative-dualizing theorem to identify the field fibre with its Serre-duality module, and proper-nodal dualizing base change for the normalized-component formula 2g_Z-2+b_Z, including both branches of a self-node. Flatness over a field is immediate; the two representing maps are inverse by naturality. I checked nonempty pure one-dimensional nodal fibres and the current completed-local-ring hypotheses. Neither cited theorem assumes projectivity or a smooth generic fibre.

Step 2 uses exactly the normalized-component ampleness equivalence for proper dimension-at-most-one schemes. C is reduced of dimension one and its component normalizations are the ones in Step 1. The bounds b>=3 in genus zero and b>=1 in genus one are integer arithmetic; positivity in higher genus is automatic.

Step 3 uses the new subcurve adjunction formula, the same ampleness criterion on each reduced integral component, the proper-integral-curve ample-degree criterion, the multiplicity-weighted degree sum, and the proper reduced algebraically closed global-sections product theorem. Their statements give respectively the formula, positive component degrees, their sum with multiplicities one on reduced Y, and H0(C,O_C)=Omega. A proper subcurve has nonempty complementary union; connectedness forces a nonempty boundary, so delta>=1. For the whole curve d_C=2g-2>=2. I checked that no smooth-curve Riemann--Roch statement is being applied to singular Y.

Step 4 uses tensor-degree additivity and the current obstruction theorem of Tag 0E3E, which I read in full. The quotient algebra of T intersect Y has length at most two. For a proper subcurve the strict margin is 2d_Y+delta_Y-t_Y>=1; for Y=C it is 2d_C-t_C>=2. Nonzero H1 would supply a subcurve with the opposite weak inequality, a contradiction. Repeating with the empty T gives H1(C,L)=0. This directly uses the cited statement and makes no extra vanishing node.

Step 5 uses precisely the section-boundary theorem's lifting iff zero-boundary statement. Trivializing the invertible L reduces the ideal-tensor sequence to the defining ideal quotient, so it is exact. Step 4 kills the boundary group. Sections of closed pushforward are sections on T by definition.

Step 6 uses the point-and-tangent separation theorem, projective-bundle quotient geometry, the projective-space-by-sections definition, the closed-point residue-field theorem, and the positive-dimensional closed-points theorem. Their statements respectively give the immersion from generation and separation, quotient convention and tautological line, coordinate uniqueness, rationality of closed points, and another closed point for each one. A nonzero tangent vector surjects onto dual numbers: constants give the field and a nonzero first derivative gives epsilon. Lifting epsilon provides tangent separation. I checked generation as well as separation. The basis-coordinate morphism agrees with the quotient-convention evaluation morphism by the sections universal property, so the asserted tautological pullback is the same L.

Small cases checked again: rational tails have degree -1, rational bridges degree zero, a rational self-node plus an external branch gives b=3 and degree one, two self-nodes give b=4 and degree two, elliptic tails have degree one, and an isolated elliptic component has degree zero and cannot be the connected genus-at-least-two curve. Smooth genus two realizes the whole-curve bound d_C=2. The empty finite subscheme has I=O. The obstruction theorem does not falsely kill H1(O) on positive-genus curves, since its strict degree hypothesis fails there. Disconnected subcurves are allowed by adjunction while the obstruction needs only connected subcurves. All six steps remain below 2000 characters. Every step citation was checked verbatim against its current node; the changed proper-nodal quote was corrected rather than retained with obsolete wording.

## Unfinished work

The item has a complete natural-language proof. Only the independent numerical subcurve-adjunction node remains unsplit, as required for a one-level delivery. No Lean writing, compiler, Lake, build, repository write, launcher edit or direct git command was performed. Server dry run and push complete this repair.
