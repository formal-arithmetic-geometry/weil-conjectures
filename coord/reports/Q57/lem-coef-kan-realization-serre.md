# Q57: lem-coef-kan-realization-serre

## Files written

All node files are in sandbox `dag/nodes/sec-six-functors/`.

- `lem-coef-kan-realization-serre.json`: the assigned statement, split into eight steps; no Mathlib match. Its statement and statement dependencies are unchanged.
- `lem-coef-kan-minimal-factorization.json`: retained new statement-only input, unsplit, no Mathlib match. A boundary-lifting retraction followed by a simplexwise product Kan fibration.
- `lem-coef-kan-locally-trivial-realization.json`: retained new statement-only input, unsplit, no Mathlib match. Realization of a simplexwise product Kan fibration has disk homotopy lifting.
- `lem-coef-kan-path-boundary-bijections.json`: retained new statement-only input, unsplit, no Mathlib match. The concrete simplicial path fibration and natural last-face boundary bijections.
- `lem-coef-serre-disk-lift-boundary-bijection.json`: additional new statement-only input, unsplit, no Mathlib match. The continuous disk-lift formula, independence and naturality, with bijectivity for based contractible total space.

Also updated: `citations.json`, with current verbatim statements for all 21 step/node citations; this report; sandbox preparation scripts and actual search outputs. Four new nodes, zero Mathlib leaves. No Lean was written or compiled. No project or launcher source, chapter, or unit file was modified.

## Attachments

None. Exact-id/tag and notion searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no project declaration proving the assigned item or the continuous disk-boundary input. The Serre hits concerned other subjects, including weak Serre classes in abelian categories. The read-only upstream sources are not treated as proof evidence when sorried.

## Literature requested

WANTED: Hovey, *Model Categories*, Corollary 3.6.2 and Proposition 3.6.3, pp. 97–98, for the item.

WANTED: Hovey, Definition 3.5.1, Corollary 3.5.7 and Theorem 3.5.9, pp. 88 and 92–95, for `lem-coef-kan-minimal-factorization`.

WANTED: Hovey, Proposition 3.6.1, pp. 95–97, for `lem-coef-kan-locally-trivial-realization`.

WANTED: Hovey, Theorem 3.3.1, Definition 3.4.4, Lemmas 3.4.5 and 3.4.8–3.4.9, and the path-fibration part of Proposition 3.6.3, for `lem-coef-kan-path-boundary-bijections`.

WANTED: Hatcher, *Algebraic Topology*, Theorem 4.41 and its proof, p. 376, together with the relative boundary definition and Theorem 4.3, pp. 343–345, for `lem-coef-serre-disk-lift-boundary-bijection`.

I read the author-hosted Hovey PDF at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf and Hatcher chapter 4 at https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf online. No PDF was downloaded. The missing local archives are explicitly requested; the item's expanded proof remains agent-origin. These simplicial/topological results have no applicable Stacks tag. No SGA route is used.

## Returned delivery and corrections

The return identifies branch head `a15b02a08dc8bc06071fe5e331aa8c7eae6e75ee`, approved by the reader but refused at landing because `lem-coef-serre-disk-lift-boundary-bijection.json` was not a file of that commit. I read that returned head's item, report and changed-file list from the server. Its delivery contained the item and the three retained inputs, but no continuous disk-boundary node. The retained sandbox has that same split. The named missing node was also absent from the current shared DAG and from both server project trees when checked.

I compared the cited existing files between the returned head's parent and current main. The changed input is `lem-coef-realization-finite-limits`: its statement now explicitly defines the simplicial boundary as monotone maps omitting a vertex, and it has acquired a reviewed split. I reread the current statement. Its colimit, finite-limit and simplex/horn-pair clauses still give exactly the facts used here. I refreshed every quote of that statement rather than retaining the obsolete full-statement quotes. The other existing cited statements are unchanged. The four new inputs remain sandbox files, so the packaging tool includes them in its single commit on current main.

The recheck also exposed C4 in step 6: a natural exact sequence alone does not specify the disk-lift construction or its choice independence. I added the missing named continuous input with the exact representative formula. Steps 5–6 now cite it. Its last-face convention is explicit, including the initial endpoint of a lift prescribed at its terminal endpoint in degree zero. This avoids an unrecorded inverse in the comparison square.

I corrected another error in retained step 8. Collapsing a side of a triangle does not leave the two other edges glued along their entire boundary; both loops survive. In higher dimensions, collapsing each active face boundary gives a wedge of two spheres. The repaired step compares the missing face with the horn disk by an explicit radial homeomorphism and affine homotopy, then uses that wedge pinch. This is a proof correction, not a change of the item's statement. There is no statement dispute against the imported item or its sources.

## What remains

The four new inputs are intentionally statement-only and await their own one-level splits. This task is stage 1 only. A fresh second reader reviews the repaired sandbox and delivers it; this worker leaves it after an accepted no-push dry run.

## Not duplicates

lem-coef-kan-minimal-factorization vs lem-coef-kan-quillen-right-proper: the new node gives a simplicial retraction/local-product factorization; the parent gives the model structure and right properness and depends on this item's realization input. Citing the parent here would be circular.

lem-coef-kan-minimal-factorization vs lem-coef-kan-realization-serre: the input gives neither realization nor homotopy-group comparison. Steps 1–2 carry the reduction to the local-product case.

lem-coef-kan-locally-trivial-realization vs lem-coef-kan-realization-serre: the input assumes product trivializations over every simplex; the item has no such hypothesis and requires the separate factorization and graph-lift argument.

lem-coef-kan-path-boundary-bijections vs lem-coef-kan-realization-serre: the input is entirely simplicial; steps 3–8 still construct the continuous comparison, prove its bijectivity, and check multiplication.

lem-coef-kan-path-boundary-bijections vs lem-coef-serre-homotopy-exact-sequence: the former gives a concrete internal-Hom simplicial path object and specified simplex lifts; the latter concerns continuous Serre fibrations.

lem-coef-kan-path-boundary-bijections vs lem-weil-pbc-trivial-kan-homotopy-equivalence: a homotopy inverse for a trivial Kan fibration does not construct the path evaluation fibration or its boundary bijections. The contraction consequence is proved in step 5.

lem-coef-serre-disk-lift-boundary-bijection vs lem-coef-serre-homotopy-exact-sequence: the existing statement gives natural connecting maps and exactness but does not assert their disk/last-face formula or independence of the chosen disk lift. Those are precisely the non-elementary additional facts used by step 6. Bijectivity from a contraction alone would have been an elementary consequence, and would not warrant a new node.

lem-coef-serre-disk-lift-boundary-bijection vs lem-coef-kan-path-boundary-bijections: the new input is for arbitrary continuous Serre fibrations, with continuous disk representatives, not simplicial path objects or Kan lifting.

lem-coef-serre-disk-lift-boundary-bijection vs lem-coef-kan-realization-serre: the new input contains no simplicial realization or homotopy-comparison conclusion. It is a general continuous lifting theorem used after step 2 has proved the required Serre property.

lem-coef-serre-disk-lift-boundary-bijection vs lem-coef-topological-serre-model: the model-structure statement classifies maps and factorizations; it does not identify connecting maps on representatives. It is not used as a substitute route.

Whole-DAG statement searches for Serre fibrations, disk lifts and connecting maps were read, not just filename matches. `tools/blueprint_refs.py search 'disk lift'` found no imported match; `search 'Serre'` returned unrelated algebraic/cohomological statements. The ancestry command confirms `prop-coef-integral-exceptional-adjoint`. The current main-20261015 proof paragraph 2 is the inherited derived coefficient-adjunction branch, reached here through cosimplicial frames; no unit/chapter route was replaced. No shared Stacks tags need pairwise comparison.

## Review by Q57

I checked delivery-errors B–E with the actual node statements open. The item still follows Hovey's minimal-fibration reduction and path-space induction. I read Corollary 3.5.7 and Theorem 3.5.9 for the first input, Proposition 3.6.1 for the second, and the path construction of Proposition 3.6.3 and the representative boundary discussion of Lemmas 3.4.8–3.4.9 for the third. The arbitrary-base realization result does not require either simplicial set to be Kan. The simplicial boundary statement includes the pointed-set degree-zero case. I read Hatcher's definition of relative representatives and boundary restriction, and the proof of Theorem 4.41 for the added input: disk lifting supplies representatives, lifting a homotopy relative to the prescribed faces proves independence, and restriction is natural. Translating its distinguished cube face to the ordered last simplex face keeps the same face parametrization on both sides of step 6. Its contractible-total-space corollary concerns the pointed base component, so the statement does not need B connected. No proof has been inserted in a new unsplit node.

Step 1 uses the trivial-Kan definition's surjectivity and boundary lifting, the monomorphism extension theorem's exact commutative-square statement, and the realization node's product identification. The graph is injective, the lifting square commutes, and the resulting h satisfies both equations needed for the displayed continuous disk-lift formula. This does not use the parent Kan–Quillen theorem.

Step 2 uses exactly the two retained factorization/local-realization statements. The first supplies both the boundary lifts of r and the simplexwise product hypotheses of q; the second therefore applies even for empty fibres. Two successive lifts prove composition directly, with no additional composition theorem concealed in a citation.

Steps 3–4 use the realization definition in def-cbc-enhanced-diagrams-cones and the current realization node's coproduct, product and disk-pair clauses. Edge-generated vertex classes partition every simplex, giving a genuine simplicial coproduct; each realized summand is path connected by edges and paths inside a simplex. Representatives and their based cylinders realize to continuous representatives and homotopies. Postcomposition commutes with the construction. These are elementary arguments, and remain steps rather than new nodes.

Step 5 uses the path-boundary node's boundary lifting, Kan evaluation map and loop fibre. The two cylinder ends and the constant-path cylinder form a degreewise subobject, so the stated trivial-Kan monomorphism extension applies and yields a contraction fixing the basepoint. The current finite-limit statement identifies the continuous fibre. Step 2 supplies the Serre hypothesis. The Serre-sequence statement explicitly supplies its component-action orbit/stabilizer assertions: contractibility makes the action transitive with trivial stabilizer, which proves the degree-zero bijection. The added disk-boundary statement specifies which representative-level boundary maps are being used; its based-contraction hypothesis has just been proved.

Step 6 no longer takes a formula from the proof of a different node. Its three citations give, respectively, the simplicial lift with constant horn, the realized disk/horn pair, and the continuous boundary formula with independence of lifts. Realizing the chosen lift gives the literal equality of the two last-face representatives. Both degree-zero maps use a prescribed terminal endpoint. This checks the whole comparison square, not just naturality as an unsupported assertion.

Step 7 is induction simultaneously over all pointed Kan complexes. Its base is step 3 and its induction hypothesis applies to the loop fibre because the path-boundary statement says that fibre is Kan. The two boundary maps are bijections, so the displayed algebraic formula proves the next vertical map bijective. No connectedness or boundedness hypothesis is added.

Step 8 is the corrected elementary geometric argument. The ray from a point just outside the missing face enters through that face and exits through the horn, giving a boundary-fixed disk homeomorphism. Straight interpolation stays in the convex simplex. The two active horn faces give two sphere summands after their boundaries and the constant faces are collapsed; they are not incorrectly identified as two disks with one common full boundary. The alternating face signs give the two positive concatenation pieces. For n=1 this is the actual directed edge path 01 then 12, so order in a noncommutative fundamental group is preserved. Bijectivity already proved in step 7 then supplies independence and group laws.

I checked small cases: the empty simplicial set and empty fibres do not acquire an unintended nonemptiness assumption; degree-zero boundary lifting does imply surjectivity where the trivial-Kan definition needs it; K empty has an empty component set, while positive degrees require a vertex. A discrete Kan complex and the point have trivial based comparison. For the added continuous node, the identity fibration of a point and the universal covering R to the circle test the contractible case; the latter's degree-zero terminal-lift rule takes a once-around loop to the opposite integer endpoint, confirming why the convention must be explicit. A noncontractible product fibre is not claimed to have a boundary bijection. The triangle is an explicit counterexample to the old quotient description.

The retained three nodes preserve their actual search records and logs. For the added node I ran logged msearch LeanFinder, Loogle, grep and LeanSearch, with a second semantic phrasing, and retained their actual stdout in repair-search-results.json and mathlib_searches. I inspected HomotopyGroup.lean and Lifting.lean at the returned declarations. The former gives continuous loop-group identifications; the latter's liftHomotopy assumes a covering map. Neither gives the asserted disk boundary for arbitrary Serre fibrations. No unavailable search is counted as evidence of absence, no search is invented, and no new Mathlib leaf is asserted.

All definitions needed by the new statements are inline or in stmt_deps. The new disk-boundary node is a statement-only generic input, not a clause of the assigned item renamed. The changed realization statement was reread, every citation quote regenerated against the current overlay, and proof_deps recomputed as the exact union of uses. The graph lift, component argument, contraction, two-lift composition, induction and horn geometry remain in the item's steps. The assigned statement itself was not weakened. The packaging tool, rather than a manual edit to the shared repository, rebuilds the delivery on current main and includes the missing path in the commit.

## Dry run

The repaired command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q57 lem-coef-kan-realization-serre --no-push` printed `OK (not pushed) deliver/Q57/lem-coef-kan-realization-serre at a035c0b4f1: preflight passed`. This validates the five-file repaired node overlay, including the formerly missing disk-boundary path, on current main. The required preflight runs on the Weil server and includes the DAG and split checks. A final repeat packages this updated report. No delivery was pushed, and no Lean compiler or Lake command was run.

## Second reading by Q57

Step 1 checked against `def-weil-pbc-trivial-kan-fibration`, `lem-weil-pbc-trivial-kan-lifts-monomorphisms`, and the finite-limit realization statement; the graph lift and explicit Serre lift formula are correct.
Step 2 checked against the minimal-factorization and locally-trivial-realization statements; the two successive lifts compose over the homotopy, including empty fibres.
Step 3 checked against the realization definition and finite-colimit statement; edge-generated simplicial components realize to exactly the path components, including the empty case.
Step 4 checked against the realization simplex-pair, product, and colimit clauses; representatives, cylinders, quotient-boundary formulation, and naturality are correctly carried out.
Step 5 checked against the path-boundary, trivial-Kan lifting, realization finite-limit, Serre exact-sequence, and disk-boundary statements; the based contraction, fibre identification, degree-zero action, and last-face convention are all supported.
Step 6 checked against the path-boundary, realization, and disk-boundary statements; realizing the chosen horn lift gives the displayed comparison square, with the prescribed terminal endpoint in degree zero.
Step 7 checked against the path-boundary statement and the step-5/step-6 bijections; the simultaneous induction is valid for the loop fibre and has no hidden connectedness assumption.
Step 8 checked against the simplex-pair realization statement and the explicit horn geometry; the radial disk comparison and wedge-of-spheres pinch preserve order and give the group operation, including the triangle case.
`lem-coef-kan-minimal-factorization` checked for a self-contained Hovey factorization statement, source, dependencies, blueprint fields, and recorded searches; verdict: valid unsplit input.
`lem-coef-kan-locally-trivial-realization` checked for its precise simplexwise product hypothesis, arbitrary-base/empty-fibre scope, source, dependencies, blueprint fields, and recorded searches; verdict: valid unsplit input.
`lem-coef-kan-path-boundary-bijections` checked for the explicit internal-Hom path object, all horn and degree-zero clauses, naturality, source, dependencies, blueprint fields, and recorded searches; verdict: valid unsplit input.
`lem-coef-serre-disk-lift-boundary-bijection` checked for the continuous Serre lifting formula, last-face convention, lift independence, naturality, contractible-total-space corollary, source, dependencies, blueprint fields, and recorded searches; verdict: valid unsplit input.

Changes made in this second reading: no mathematical or statement changes were needed after the returned-worker repairs; I verified that the added disk-boundary node is packaged and that all 21 citation quotes match the current node statements. The required dry run was rerun on the repaired sandbox and passed (`db3742f06a`).
