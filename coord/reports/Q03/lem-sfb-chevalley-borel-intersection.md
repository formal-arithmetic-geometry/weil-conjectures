# Stage-1 delivery: lem-sfb-chevalley-borel-intersection

Group Q03; 2026-10-23. The item's statement is retained verbatim.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-borel-intersection.json`: statement, split into eight steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-general-borel-flag-variety.json`: statement only, unsplit; no Mathlib match. General smooth connected affine groups, including nonreductive ones.
- `dag/nodes/sec-six-functors-basics/lem-sfb-luna-borel-attraction-charts.json`: statement only, unsplit; no Mathlib match. The invariant affine chart input of Milne 17.65, with its containment-only hypothesis made explicit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-kostant-rosenlicht-affine-orbits.json`: statement only, unsplit; no Mathlib match. Closedness of unipotent orbits on affine finite-type schemes.
- `citations.json`: an entry for every proof-step citation; quotes are copied from the cited statements, including all clauses needed by the step. `searches.jsonl` and the individual raw search-result files preserve the executed searches.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item tag and for Borel subgroups, unipotent radicals, Kostant and Rosenlicht found no project declaration stating these results. A Lie-algebra or abstract-group result is not an attachment for an algebraic-group-scheme assertion.

## Wanted literature

WANTED: none for this split. The primary source is the local `literature/milne-algebraic-groups_iAG2017.pdf`. I extracted it into this sandbox, and read printed pp.335--336, 353--355, 361, 367--375. Existing orbit-geometry statements were also checked against the orbit lemma in this same edition (1.66, printed pp.27--28), so this delivery does not require obtaining the 2022 corrected text cited by that existing node.

## Problems and corrections

The item was statement-only, not a completed split. It is not disputed: its hypotheses and its first equality agree with Milne 17.56. The proof must work for arbitrary smooth connected affine groups; using only the reductive Borel-pair node would silently assume reductivity and can produce a dependency cycle through the parent self-centralizer lemma. I therefore added a general flag-variety input instead.

Milne's last paragraph abbreviates the solvable group attached to the torus intersection as I(T), and its unipotent subgroup as I_u(T). The proof now explicitly defines H as the smooth reduced identity component of that intersection, constructs U=H_u, and writes the multiplication inverse proving H=U T. The product is thus the specified scheme-theoretic image. I used the smooth reduced full Borel intersection K, and K_u normality, to spell out the source's reduction through Remark 17.31; this is the same full-intersection argument, without adding a separate statement of the radical equality. The reverse inclusion R_u(G) in every Borel is proved using the already available fixed-point theorem, normality and conjugacy.

In 17.65's proof, the acting subgroup is used only through containment in every Borel through T, hence in the relevant parabolic stabilizer of the dual line. The chart node states this for a smooth connected unipotent V with precisely that containment hypothesis. Applying it to U does not assume the equality being proved. Its statement only asserts the chart and invariance; the orbit argument remains in the item.

No unit or chapter record was changed. I read the latest blueprint's unit and direct-images proof (3), as well as the imported DAG chapter/unit records. This auxiliary lemma supports the inherited alteration/moduli prerequisite under that step; it is not the unit's key statement. `blueprint_refs.py ancestor` reports a null imported ancestor, which is preserved in the new nodes with the inherited via chain extended by the item. Whole-blueprint searches for Borel, flag variety, attraction, Rosenlicht and orbit found no duplicate assertion.

## Not duplicates

lem-sfb-general-borel-flag-variety vs lem-sfb-reductive-borel-pair-structure: the existing theorem assumes reductivity and supplies root data and a chosen Borel pair; the new theorem applies to every smooth connected affine group and identifies all flag stabilizers scheme-theoretically. The reductive theorem cannot supply this general input.

lem-sfb-general-borel-flag-variety vs lem-sfb-solvable-subgroup-flag-realization: the existing result embeds a solvable subgroup as a stabilizer in a complete vector-space flag scheme; it does not state the projective homogeneous variety of all Borel subgroups of G with its conjugation action and stabilizers.

lem-sfb-general-borel-flag-variety vs lem-sfb-borel-characteristic-picard-sequence: the existing result gives a Borel quotient torsor and a Picard exact sequence; it does not give the projective variety of all Borels, its transitive action and its torus-fixed points.

lem-sfb-luna-borel-attraction-charts vs lem-sfb-flag-effective-picard-generators: both cite 17.65, but the existing statement concerns generators of Pic(G/B), not invariant affine attraction opens. Its proof cannot be used as a substitute for the missing statement.

lem-sfb-kostant-rosenlicht-affine-orbits vs lem-sfb-smooth-group-orbit-geometry: the existing general result gives locally closed orbits and invariant closures, not closedness in an affine target. Closedness requires unipotence and is the new assertion.

## Review by Q03

I read the complete source of the item (17.56 and its proof in 17h), and for each new node read the actual source statement and proof: 17.9, the paragraph following 17.12, 17.48 and 17f/17.52 for the general flag variety; 17.65 for attraction charts and their invariance; and 17.64 for closed unipotent orbits. No SGA source is used. The source of 17.65 is explicit about using a projective representation, the weight decomposition and the stabilizer of a dual line; this input is a genuine lemma, rather than a restatement of the desired intersection formula. The 17.64 proof uses an invariant function in the ideal of the orbit boundary; its full closed-orbit conclusion is retained in a separate statement-only node.

For step 1 I opened the existing identity-component and reduced-factorization statements. They apply to the affine finite-type intersection subgroup even if it is nonreduced. They give the smooth connected H, while connectedness puts T into H and commutator containment proves solvability inside B_0. No assumption that I itself is smooth is used.

For step 2 I opened both the perfect-solvable-unipotent-torus and the solvable-torus-complement statements. The former actually supplies the smooth connected unipotent U and torus quotient; the latter, applied to the maximal torus T of H, gives the quotient restriction isomorphism. I wrote its inverse and the two multiplication identities, rather than merely saying the decomposition transports. Algebraically closed k is perfect, so the field hypothesis is satisfied.

For step 3 I checked that smooth-unipotent-solvable proves the required group-scheme solvability, that the fixed-point theorem is for smooth connected solvable groups acting on a nonempty proper scheme, and that the new flag theorem gives both scheme-theoretic stabilizers and transitivity. Normality of R_u(G) then carries containment from one Borel to every Borel on all test algebras. The smooth-geometrically-reduced statement applies to the map to Spec(k); the reduced-factorization statement and connectedness justify passing into H. The perfect-solvable statement explicitly contains every smooth unipotent subgroup, as needed for R_u(G) <= U.

For step 4 I checked the existing smooth-group-orbit statement gives invariant orbit closures, and the proper-permanence statement makes a closed orbit closure proper. The fixed-point theorem applies to the commutative smooth connected T on that closure, and the flag theorem identifies its fixed point with a Borel through T. The chart statement has exactly the rational-point membership test used here. U is contained in every such Borel by construction, so its invariance hypothesis is verified before application. The cover argument remains an actual step of the item.

For step 5 I checked the same orbit, properness and solvable-fixed-point statements for U. All give exactly their asserted conclusions. The complement invariance is explicitly in the chart node. The affine Nullstellensatz statement supplies rational points in nonempty opens of U: choose a nonempty principal open D(f); if it had no rational point, f would vanish at every rational point, so f=0 by the vanishing principle. This proves the needed passage from a rational orbit containment to the whole orbit image. Rational points of an orbit lift to U(k) because the orbit morphism is faithfully flat by the orbit-geometry node and its nonempty finite-type affine fibres have rational points by the same Nullstellensatz. Thus the transitivity used in the complement argument requires no separability of stabilizers.

For step 6 I checked that Kostant--Rosenlicht is applied inside the affine invariant chart, not inside the projective X. All hypotheses (smooth connected unipotent acting group, affine finite-type target) hold. Once a fixed point lies in a transitive orbit, the pointwise calculation makes the orbit trivial. I then checked the vanishing clause of the existing affine Nullstellensatz and the smooth-geometrically-reduced statement: they justify killing every defining equation of each Borel on U. This repairs the potential gap between rational-point inclusion and closed-subgroup-scheme inclusion, including in positive characteristic.

For step 7 I checked that the smooth-ambient-normality node asks for preservation of the closed subgroup scheme by each geometric conjugation, not just pointwise preservation. Permuting Borels preserves the full intersection ideal, and the canonical reduction and identity component are preserved as closed subschemes. The smooth connected G therefore satisfies that node's hypothesis. The perfect-solvable-unipotent-torus statement explicitly gives K_u normal in a smooth ambient G when K is normal, and contains the smooth unipotent U. Its smoothness and connectedness verify the maximal-property hypotheses for R_u(G). This supplies U <= R_u(G) without concealing a radical theorem. Step 8 is the equality substitution into the explicit scheme-image calculation of step 2.

I checked B--E of the delivery-error checklist against the files: all three new nodes are self-contained statements with empty proofs; every notion is inline or has a definition dependency; the item has an argument rather than clause relabellings; no parent's self-centralizer conclusion is cited; and each step's non-elementary inputs are statements that actually give the conclusion used. All eight proof steps are below 2000 characters. Search records reproduce executed queries and their results, not inferred searches. The external reduction/properness and vanishing results are declared generic tool uses.

Small cases checked: for the trivial group the flag scheme is a point and U=T=1; for a torus it is again a point and the formula is G=T. For a connected solvable group, the only Borel is G and the argument reduces to the explicit U-times-T decomposition; the affine group Ga semidirect Gm confirms that a direct-product group structure is not being claimed. For SL_2 with the diagonal torus the two Borels through it intersect in the torus, so U is trivial. The unipotent chart input also permits the trivial acting subgroup. For Kostant--Rosenlicht, translations by Ga on A1 have the whole affine line as a closed orbit, while a trivial action on a nonreduced affine scheme has singleton closed orbits: neither case requires a reduced target. The proof never infers equality with the possibly nonreduced I, only with its smooth reduced identity component.

## Unfinished work

None at this splitting level. The three new nodes are intentionally unsplit, for subsequent work. Their expected proof routes are precisely Milne 17f and 17.48, the weight/dual-line proof of 17.65, and the invariant-function proof of 17.64 respectively. No Lean was written or compiled, and no repository or launcher file was modified.
