# Stage-1 delivery: lem-zl-reduced-frontier-mixed-gluing

Group Q113; direct delivery; 2026-10-21.

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-reduced-frontier-mixed-gluing.json`: existing statement node, now split into seven proof steps; Mathlib searches give no match.
- `citations.json`: 20 entries, one for each step/dependency citation, containing verbatim substrings of the cited statements.
- `report.md`: this report and signed mathematical review.

No new nodes; no Mathlib leaves. The sandbox also contains the logged `searches.jsonl` produced by the required search command and an auxiliary script used to write the JSON. No repository, Lean, launcher, unit, or chapter files were changed.

## Attachments

None. The required searches of `lean/WeilConjectures/` for the blueprint tag and the relevant notions found no declaration stating every clause of this item. Existing declarations about mixedness and open–closed gluing state only parts of the item and use the upstream coefficient model; they do not justify attaching this full common-stage-heart statement. In particular, `WeilConjectures/DeligneLaumon/Reduction/Weights.lean` supplies the familiar filtration language and closure statements, not the whole given frontier-chain and reduction assertion.

## WANTED

None. The source for this item is present and was read in full: `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, especially its final three paragraphs. The chapter and unit records were read as well. The proof is marked agent-written because that is the provenance of the blueprint and because the explicit heart and induction details here expand its sketch.

## Corrections and scope

There is no statement dispute and no statement change. The node was an unsplit statement without proof. The split supplies exactness and purity inputs, the actual Weil-equivariant short exact sequence, the filtration construction, two finite inductions and recovery across reduction. In particular, I did not cite the finite-coefficient statement `i-topology` as though it asserted the desired rational/common-stage heart equivalence. Instead, reduction is a surjective closed immersion, so the same common-stage open–closed triangle with empty open complement directly proves that its actual unit is an isomorphism. This is a specialization within the blueprint's open–closed route, not a change to the unit or chapter route.

The whole-DAG and blueprint searches for filtration, extension by zero, open–closed localization, exact closed direct image and reduction found the existing dependencies. They suffice, so there is no helper restating one of the item's clauses and no elementary helper node. The exact source of the actual localization operations is retained: the compact-support, direct-image and inverse-image functors named in the item are those of the existing common-stage definitions and localization theorem. No SGA source is used.

## Not duplicates

No new node was created. The broader existing gluing/reduction nodes were inspected and used only for their stated clauses; none states this entire item. In particular, `lem-zl-open-closed-weight` concerns mixed complexes after their outer localization terms are already bounded, whereas this item builds a specific finite heart filtration from finitely many component filtrations and includes the actual reduction unit and exactness assertions.

## Review by Q113

I read the current blueprint proof in full and compared the item clause by clause with its reduction paragraph, its componentwise concatenation paragraph and its final open–closed gluing paragraph. The hypotheses here are exactly the ones the gluing portion needs: constructibility in the rational/common-stage heart, a finite frontier chain, and all immersions and components defined over the finite field. There is no need for lissity, connectedness, semisimplicity or reality in this lemma. No new node needs a separate source comparison. All seven steps are below 2000 characters, and I checked that none hides a non-elementary input without a node.

Step 1 uses the statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-open-subscheme-noetherian` and `lem-pod-separated-finite-type-base-change` for the Noetherian/quasi-compact and geometric finite-type setting. The affine quotient description explains why the closed subschemes are still finite type; an open subscheme of a Noetherian scheme is quasi-compact and is locally finite type by its affine charts. I checked separatedness is inherited by the given subschemes and the coefficient prime is invertible. The actual restriction theorem `lem-zl-immersion-weil-local-behavior` gives exact Weil-heart restriction, rather than merely a stalk identification. Closed immersions are finite by `lem-weil-pbc-closed-immersion-finite`, and `lem-zl-finite-adic-direct-image` expressly asserts t-exactness and exactness on the rational/common-stage constructible hearts, with no extra smoothness or lissity hypothesis. `prop-weil-operations` supplies their Weil lifts. `def-weil-constructible-heart`, `lem-a1-constructible-pullback-t-exact`, and `def-weil-weil-sheaf-complex` justify the explicitly written kernel/cokernel construction in Weil pairs: exact Frobenius pullback preserves their universal properties, so the induced structure maps are invertible. No triangulated structure on fixed pairs is assumed.

Step 2 reads `lem-zl-extension-by-zero-punctual` for both exactness of open extension by zero and preservation of a specified pure real weight. For closed direct image, the finite hypothesis is checked using the closed-immersion lemma; `lem-zl-finite-pushforward-punctual` gives the same punctual pure weight, and Step 1 gives its exactness. Applying the functors to each short exact quotient sequence identifies the new quotient, so it is the prescribed filtration that is sent forward. The definition `def-weil-punctual-weights` is used only for the mixed-filtration predicate and its bound; it is not cited as an exactness theorem.

Step 3 uses the displayed triangle and Weil clause in the statement of `prop-sf-open-closed-triangle-all-stages` at Qbar_l, on separated finite-type geometric schemes. I checked that its first arrows are precisely the open counit and closed unit, and that the finite-field descent hypotheses for its Weil clause hold. Step 1 and Step 2 put all three vertices in the ordinary constructible heart. Clause 4 of `lem-weil-heart-short-exact-triangles` explicitly converts such a geometric distinguished triangle to a heart short exact sequence. The commuting Weil maps and Step 1 then give the Weil-heart assertion. This avoids the incorrect inference that one has a distinguished triangle in the fixed-pair category.

Step 4 uses clause 2 of `lem-a1-mixed-direct-summand`, whose statement really includes closure of sheaf mixedness under extensions with the same upper bound. The actual filtration is also written: first the kernel filtration, then inverse images under the quotient map. The quotient calculation identifies every later graded piece with the original quotient's graded piece, so arbitrary different input pure weights are retained. The construction takes place in the heart established in Step 1 and needs no split extension. It is not merely an application of a new helper restating the item.

Step 5 is elementary finite induction from Steps 2–4: a clopen component has closed complement equal to the union of the remaining components. Both are defined over k_0, so Step 3 applies; Step 2 supplies the two extended filtrations and Step 4 splices them. The empty component set means the underlying scheme is empty. A sheaf of modules there is zero by the empty-cover sheaf axiom, and its derived/rational/common-stage image is zero. These are the reasons for the base case, not an omitted nonempty assumption. No new theorem is used by this step.

Step 6 is the second elementary finite induction, with the assertion, base and backward step all explicit. At a=t the scheme is empty and the filtration is empty. At a<t the closed term comes from the induction hypothesis, the open term from Step 5; Steps 2–4 combine them. The component indices and chain indices are finite, so the final length is finite. The finitely many real weights have a common bound if none was supplied, and if a bound w was supplied no operation changes it. `def-weil-punctual-weights` is used for this final predicate and its allowance of a zero-length filtration; no claim is drawn from the proof of a cited node.

Step 7 uses the exact statement of `lem-weil-pbc-reduction-universal-homeomorphism` that the reduction is a surjective closed immersion, rather than requiring an unproved comparison of adic coefficient models. Its image is all of X_0; hence the complementary open is empty and the Step 3 sequence has zero left term. This proves the actual unit is an isomorphism in the same heart, with its Weil square supplied by the Weil clause of `prop-sf-open-closed-triangle-all-stages`. The inverse commutes with Weil structure by solving that square. Exact r_* and its pure-weight preservation are the closed-immersion case already established in Steps 1–2. Inverse images under the unit transport the constructed filtration and its quotient weights to F.

I tested the statement and construction on X_0 empty (including t=0), F=0, one clopen component, two components of different pure weights, an empty stratum Z_a=Z_{a+1}, repeated filtration terms, and a nonreduced scheme such as Spec(F_q[epsilon]/epsilon^2). In the last case the reduction unit comes from the empty-open sequence, so no smoothness or reducedness of the ambient scheme is being smuggled in. Mixed extensions need not be semisimple; inverse-image splicing still works for a nonsplit extension. The zero stalk has no nonzero eigenvalue and so introduces no new pure weight constraint. These checks found no false clause.

For C4 I opened every cited node and matched the statement used above; `citations.json` has one exact statement substring per cited occurrence. For C1 I checked the geometry, heart exactness, Weil lifts, purity and triangle-to-sequence conversion all have cited nodes, while the remaining finite induction and quotient constructions are spelled out. I searched dependency paths of all substantive inputs and found no path back to the item. The generic off-unit tools are declared in `split_report.tool_uses` for the maintainer's independent judgment; no top-level `tool_uses` field was set. The unit's fixed gluing route is preserved.

## Verification and remaining work

The server `review_split` check passed: seven proof steps, zero new nodes, the unit realization accepted. The full required delivery dry run and push follow this report; their results are recorded below after completion. No mathematical work is left unfinished at this split level.

Full delivery dry run completed successfully: `OK (not pushed) deliver/Q113/lem-zl-reduced-frontier-mixed-gluing at 50175b71e7c: preflight passed`. The invocation exited with code 0 before the push invocation was started.
