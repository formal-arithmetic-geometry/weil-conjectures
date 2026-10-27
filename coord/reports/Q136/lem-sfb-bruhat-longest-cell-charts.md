# Q136 stage-1 delivery: lem-sfb-bruhat-longest-cell-charts

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bruhat-longest-cell-charts.json`: item statement preserved; eight complete proof steps; split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flag-torus-fixed-geometry.json`: statement; no Mathlib match. Projective flag geometry, torus-fixed flags and tangent weights, and a separating dominant cocharacter.
- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-attracting-cells.json`: statement; no Mathlib match. General projective Bialynicki--Birula theorem with its functor interpretation.
- `dag/nodes/sec-six-functors-basics/lem-sfb-unipotent-root-intersection-products.json`: statement; no Mathlib match. Smooth scheme intersections of two Borels containing a common torus and their ordered root factors.

All three new nodes are statement-only, with empty proof/dependencies and no hidden proof sketch. There are no new Mathlib leaves. `citations.json` supplies the exact cited statement for every citation in each proof step. Search outputs and the unmodified msearch log remain in the sandbox.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint item tag, Bruhat, BorelSubgroup, longestCell and flag-variety terminology: no matching declaration. Existing upstream sorry declarations were not treated as proofs.

## WANTED

None. The actual Milne PDF is available and was read locally. No SGA source was used.

## Source error

The appended errata in `milne-algebraic-groups_iAG2017.pdf`, entry for p.447, says the proof of 21.71 proves only the inclusion of the unipotent orbit in its attracting cell. The literal printed proof takes a limit under lambda without showing the unipotent orbit is invariant under lambda. I do not repeat that inference. Step 4 proves equality by the independent root-stabilizer dimension formula, Kostant--Rosenlicht closedness in the affine attracting cell, and strict dimension drop for a proper closed subset. The root-intersection input 21.77 does not require Bruhat exhaustion, and the dimension formula is the pre-existing general orbit theorem. Thus this repair introduces no circular use of Bruhat decomposition.

The errata also retracts the necessity claim in 21.68(d) in characteristics 2 and 3. The new intersection node uses 21.68(a)--(c), not (d). None of the statements assumes characteristic zero. On checking the draft sources I removed an incorrect reference to 17.38 as an intersection theorem; it is a centralizer theorem. The source now points to 21.66--21.68, 21.77, 21.79(a), and 21.84, which supply the asserted root intersections and common torus.

No STATEMENT-DISPUTED change to the item is required: its statement remains verbatim. The repair concerns the source proof, not the mathematical conclusion or the unit route.

## Not duplicates

lem-sfb-flag-torus-fixed-geometry vs lem-sfb-reductive-borel-pair-structure: the existing node gives a proper finite-type quotient and right B-torsor; it does not state the equivariant projective embedding, smoothness of the quotient, the fixed subscheme, tangent weights, or a cocharacter separating projective weights.

lem-sfb-flag-torus-fixed-geometry vs lem-sfb-rho-regular-weyl-orbit: the existing node supplies the longest element and rho stabilizers; the new node concerns the actual scheme of flags and its fixed subscheme. The item cites the existing node for the longest element rather than duplicating it.

lem-sfb-projective-attracting-cells vs lem-sfb-bruhat-longest-cell-charts: the new node concerns arbitrary smooth projective schemes with a linear multiplicative-group action and isolated fixed points; it says nothing about Borel orbits or root groups. The item must prove the equality of its attracting loci with unipotent orbits and then construct all torsor trivializations.

lem-sfb-unipotent-root-intersection-products vs lem-sfb-borel-root-product-coordinates: the existing node supplies the product of all positive root groups in a single Borel radical. It does not give smoothness or scheme structure of intersections with a second Borel. The item reuses it for complementary root-coordinate products.

lem-sfb-unipotent-root-intersection-products vs lem-sfb-reductive-root-subgroup-parametrizations: the existing node gives individual root groups and their torus action, not their intersections or multiplication. The new node cites it in its statement.

lem-sfb-unipotent-root-intersection-products vs lem-sfb-longest-weyl-open-cell: the existing node is only the longest-cell open immersion and now depends on this item, so using it here would be circular. The new node says nothing about an immersion into G or a stratification and works for every pair of Borels containing T.

lem-sfb-unipotent-root-intersection-products vs lem-sfb-chevalley-borel-intersection: the existing node treats the reduced identity component of the intersection of ALL Borels containing T in an arbitrary connected smooth group. The new node gives the full smooth scheme intersection of TWO Borels of a reductive group, with the individual root factors needed for stabilizers; neither is an instance of the other.

A full-DAG statement search and blueprint search found no Bialynicki--Birula/attracting-cell, fixed-flag, or two-Borel root-intersection statement. The blueprint searches for Bruhat, Bialynicki, Rosenlicht, cocharacter, root subgroup, root groups, attracting, unipotent, Weyl and orbit were read. The generic unipotent/curve and orbit results were unrelated. During the launcher pause the live DAG gained `lem-sfb-kostant-rosenlicht-affine-orbits` and `lem-sfb-borel-root-product-coordinates`. I opened their statements and reused both. The planned fourth node for closed unipotent orbits was never created. Its completed searches are retained as research history.

## Review by Q136

I read Milne 21.66--21.86 (printed pp.444--452), 13.47--13.52 (pp.272--275), 17.64 (pp.373--374), the Weyl-chamber summary 21.41 and the appended errata. For the flag-geometry child I checked the line-stabilizer projective realization (4.27 and 17.9), torus fixed-point description preceding 21.70, separating-cocharacter Lemma 13.51, and tangent quotient calculation in 21.73. The new statement specifies actual character weights rather than differentials; distinct characters can have equal differentials in positive characteristic. For the attracting-cell child I retained projectivity: a smooth affine example such as G_m acting on itself would have no fixed points and no limit at zero, so the more loosely worded 13.49 without a completeness hypothesis must not be used here. The new node has an equivariant projective embedding and a finite reduced fixed subscheme and describes the attracting functor, not just its F-points. For the intersection child I read 21.66--21.68, 21.77 and 21.79(a), which supply smooth intersections, root products and the stabilizer equality; the common T factor accounts for disconnected-looking pointwise intersections and ensures the asserted equality is a scheme equality. I excluded the false claim 21.68(d).

Step 1 uses exactly the finite-W assertion of the rank-one-reflection node and the longest-element assertion of the rho node. The flag-geometry node supplies the embedding and separating action; the regular-cocharacter node supplies P(-lambda), and the intersection node gives B intersection n0 B n0^-1 = T from an empty common root set. Representatives are simply choices of elements of quotient cosets, with no claim that they form a subgroup or have order two.

Step 2 checks all hypotheses of the projective attracting-cell node against the flag-geometry node: Q is nonempty, smooth, connected, projective, with a linear embedding and finite reduced fixed subscheme. Its positive tangent weights are precisely the roots in Phi+ outside w Phi+, so the cell dimension and the longest-cell openness follow from the stated tangent formula. No geometric-point-only equality is substituted for a scheme isomorphism.

Step 3 uses the existing product-coordinate node and individual-root equivariance, not an assumed contraction of V. In those coordinates the contraction is multiplication by positive integral powers of t; the displayed conjugation identity proves preservation of the attracting functor over every test algebra. I changed this step from an elementary label to non-elementary because the uses include geometric attracting schemes, even though its calculation is explicit.

Step 4 opens the exact statements for the torsor, root intersections, root parametrizations, polynomial dimension, general orbit geometry, Kostant--Rosenlicht, and affine dimension drop. The stabilizer is V intersection n_w B n_w^-1 by the torsor identity. It is smooth with the required number of affine root factors, so the orbit dimension is the difference of their dimensions. The acting group is smooth connected unipotent and the attracting cell is affine of finite type, precisely the hypotheses of Kostant--Rosenlicht. The ambient affine space is irreducible and reduced, precisely the dimension-drop hypotheses. Equality of supports is promoted only between the reduced induced structures supplied by the orbit and attracting theorems. This is the substantive correction to the source proof.

Step 5 constructs V^w as an intersection with the opposite Borel and uses the existing single-Borel product theorem with a chosen ordering, first the V^w roots then the stabilizer roots. The sets partition Phi+, since w carries the positive/negative partition to another partition. It identifies the quotient by the actual right H_w-action: right multiplication changes only h in the unique product u h. The homogeneous-orbit quotient node explicitly states the fppf quotient and orbit identification, so the coordinate projection descends to the inverse morphism; no assertion is inferred from a mere bijection on F-points. For w0 the root set is all Phi+, giving V^w0=V.

Step 6 uses the full torsor isomorphism G times B = G times_Q G from the Borel-pair statement to construct the unique b in g=u n_w b. Its formula and the product formula are inverse scheme morphisms on arbitrary test schemes. Smoothness of the product uses precisely the smooth base-change clause of the proper-base-change node and smooth composition, not properness. Inverse images of the locally closed strata give the locally closed stratification; the attracting theorem provides the scalar-extension assertion.

Step 7 uses root coordinates only for V = A^N, the homogeneous quotient node only for lifting F-points of Q to G, and the Jacobson and closed-point residue-field nodes only to show the open union of translates is all of Q. Those statements apply since Q is finite type over the algebraically closed F. Properness implies quasi-compactness by definition, which gives a finite subcover. The section and trivialization are the displayed group-multiplication formulas, not an uncited assertion that B-torsors are all locally trivial.

Step 8 applies the smooth-connected scalar-extension clause in the solvable-normal-products node; that clause states it for any smooth connected group, with no solvability assumption. After arbitrary K/F the group remains smooth by the cited base-change clause, regular by the cited smooth-over-field theorem, and nonempty connected regular hence integral by the exact regular-connected-integral statement. For Q_K, the explicit trivializing covers and the identity of B give surjectivity from G_K; hence its image is irreducible. The same cover by affine spaces shows reducedness, with the elementary leading-monomial argument for polynomial domains written out. Nonempty opens of irreducible G are dense, proving density of the longest stratum without presuming it from surjectivity alone.

The new children were tested on the trivial group, an arbitrary split torus (empty roots, W singleton), and SL2 in every characteristic (two cells of dimensions zero and one, P1 covered by translates of A1, stabilizers V or 1). In the torus case the flag quotient is a point, every root product is empty, B intersection B = T, and the sole G stratum is T. These tests also exclude mistakenly requiring representatives of w0 to have order two. The generic attracting theorem includes a point with zero tangent space. The intersection statement gives B for B'=B and T for an opposite pair, not a set-theoretic intersection in place of a possibly nonreduced group scheme.

I checked delivery-errors B--E: each new statement introduces its objects, all notions are defined inline or cited, new files have no proofs, searches are exactly those run by msearch with their actual outputs, the three new facts are genuine inputs rather than the item's clauses, and every cited statement was opened and quoted in citations.json. The scheme-theoretic content is in the product and quotient arguments of the item; it was not moved wholesale into a new Bruhat theorem. No proof step exceeds 2000 characters. Off-unit general scheme tools are explicitly declared in split_report.tool_uses; they do not replace the unit route. The inherited blueprint ancestor is null (confirmed by the ancestor tool), so its exact place and full via chain are preserved and extended, with same_as empty after the blueprint searches. I read the current latest blueprint unit and direct-images proof: this item remains a supporting geometric input on the inherited alteration/moduli route, with no unit or chapter edit.

## Unfinished work

No unfinished item clause. The three new supporting statements deliberately remain unsplit for subsequent stage-1 work. No Lean files, compiler, Lake, or local preflight tools were used. The server check_dag on the sandbox passed; final delivery dry-run verification follows.
