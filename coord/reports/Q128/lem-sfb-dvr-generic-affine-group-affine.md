# Q128: lem-sfb-dvr-generic-affine-group-affine

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-generic-affine-group-affine.json`: item, statement, split; Raynaud affineness assembled in six steps. Original statement and imported metadata retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-group-finite-smooth-cover.json`: new statement, unsplit; no Mathlib match after both semantic phrasings, Loogle, LeanSearch and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-trait-group-affinization.json`: new statement, unsplit; no Mathlib match. The existing Mathlib Hopf structure requires the group already affine.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-trait-principal-translate-cover.json`: new statement, unsplit; no Mathlib match. Mathlib's quasi-affine criterion needs a supplied principal affine cover and does not construct it from the generic fibre.
- `citations.json`: one exact statement quote for every node cited by every numbered step, including repeated uses.

Three new nodes, zero Mathlib leaves. Each new node has an empty proof and no proof dependencies. The arguments below explain why these are plausible smaller inputs, not additional delivered splits.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the exact blueprint tag and for Raynaud, trait-group affineness, normalization, and affinization did not find a sorry-free declaration of the item. Existing derived-global-sections affinization comparisons do not assert group-scheme affineness. No Lean was written or compiled.

## Literature wanted

WANTED: Prasad–Yu, *On quasi-reductive group schemes*, with Appendix by Brian Conrad, Proposition 3.1 (printed p.5), Corollary A.4 (printed p.29), and the residue-field extension after Lemma A.9 (printed pp.31–32), for lem-sfb-dvr-generic-affine-group-affine and all three new nodes. Read online at https://math.stanford.edu/~conrad/papers/qrg.pdf; the named local archive is absent.

WANTED: Bosch–Lütkebohmert–Raynaud, *Néron Models*, p.161 Lemma 6, for lem-sfb-smooth-trait-principal-translate-cover. Its application and precise principal-open conclusion were read in Prasad–Yu Proposition 3.1; I did not obtain a readable copy of the original lemma. The new node records that source limitation. No missing literature was downloaded into the project.

## Errors, route and corrections

The imported item is mathematically consistent with Proposition 3.1 and needs no statement correction. No STATEMENT-DISPUTED claim is made. The imported node had no proof. Its pre-existing searches, source, creation record, blueprint ancestry and statement have been retained. Searches performed for this delivery are appended where new and logged in `searches.jsonl`.

The source's final argument uses a reference forbidden by the current route lock. This split instead uses existing Stacks 04Q6 (an open groupoid image over a field is closed) and 0ABH (affineness of a quasi-compact immersion with affine principal complement and closed intersection). This proves the same affineness assertion without that reference, without faithful-flatness of a Hopf-algebra inclusion, and without assuming the affinization finitely generated. This supporting algebraic-geometric argument changes no unit step and no target. The current blueprint's `sk-thm-sf-ctf-stability` direct-image proof and its chapter/unit records were read. The inherited chain has no imported blueprint ancestor (`blueprint_refs.py ancestor` returns None); the existing null ancestor and complete via chain are preserved, and extended for each new node. Whole-blueprint searches found no same statement, so all `same_as` lists are empty.

During self-review I corrected the descent source to the actual existing-node tag 02L5, explicitly cited open-immersion base change, and made the fpqc-cover property explicit in the finite-smooth-cover node. This avoids silently taking a nontrivial assertion from a definition. I also excluded tempting existing normalization results whose hypotheses already require the original group affine. No step exceeds 2000 characters.

The off-unit tools are declared in `split_report.tool_uses`, with one reason per node: base change/permanence of affine and finite morphisms, smooth implies flat, qcqs over an affine base, principal-chart comparison, quasi-compactness of a map into a quasi-separated target, open-immersion base change, finite-surjective descent, and fpqc descent. They are general scheme-theoretic tools and do not replace a step of this unit's route. No top-level maintainer-owned `tool_uses` field is set.

## Unfinished

No part of the item's stage-1 assembly is left open. The three explicitly stated inputs remain unsplit, as required for a one-level split. Their Lean proofs and the missing local archives are future work, not claimed completions.

## Not duplicates

lem-sfb-trait-group-finite-smooth-cover vs lem-sfb-group-model-potential-smooth-normalization: the existing node starts with an affine group and smooth geometrically connected generic fibre and constructs its affine coordinate normalization. The new node accepts a possibly nonaffine separated group, disconnected fibres and nonreduced generic fibre, and gives a finite smooth cover after base extension. Applying the existing node here would assume the desired affineness.

lem-sfb-trait-group-finite-smooth-cover vs lem-sfb-raynaud-faltings-normalized-reduction: the existing node is a complete-DVR theorem for an affine flat algebra with geometrically normal generic fibre, giving reduced normalization fibres. It does not cover nonaffine or generically nonreduced groups and does not assert the required smooth group cover.

lem-sfb-flat-trait-group-affinization vs lem-weil-pbc-flat-base-change-global-sections-qcqs: the latter compares sections after an affine flat change of base. It does not give the group structure or the sections-of-a-product comparison. It is a useful input to a future split of this new lemma, not its full statement.

lem-sfb-smooth-trait-principal-translate-cover vs lem-sfb-group-finite-translate-cover: the existing node assumes geometrically integral fibres, whereas this statement includes disconnected groups. The new principal affine seed is also not supplied by the existing translate-cover lemma.

lem-sfb-smooth-trait-principal-translate-cover vs lem-sfb-strict-henselian-fibrewise-section-density: the latter assumes geometrically irreducible fibres and gives density of fibrewise sections, not a global principal affine chart or its finite translate cover. Those hypotheses cannot be imposed on the item.

No new node is made for open subgroup closedness (existing 04Q6 is more general), for the principal immersion criterion (existing 0ABH), or for gluing the principal charts (a short argument using existing 01P8). The three new nodes have paper sources rather than Stacks source tags; there are no additional same-tag pairs to distinguish.

## Review by Q128

I read Prasad–Yu Proposition 3.1 and Appendix Corollary A.4 online, including the first smooth-reduction paragraph, the global-sections group paragraph, the principal-open/translate paragraph, and the appendix's stability under further Dedekind extensions. I also read the local Stacks `more-groupoids.tex` statements/proofs for the open-image lemma and the principal immersion criterion, and opened every cited DAG statement. The item statement is exactly the separated direction of Proposition 3.1; its group structure and flat finite-type hypotheses are present, and no connectedness is stated in that proposition.

For the finite smooth cover, Corollary A.4 first allows a finite generic extension making the reduced base change a subgroup with smooth generic fibre, then gives a finite smooth group normalization. Compose the normalization with the reduction closed immersion to obtain the finite surjection to the whole base change. Further local DVR extension to a henselian ring with algebraically closed residue field is allowed by the corollary's last clause and the extension used after A.9. The source does not require the starting group affine or the DVR excellent. The new node deliberately asks only for a finite map on the generic fibre, not an isomorphism: a nonreduced generic group can lose its nilpotents under reduction. It explicitly supplies the base fpqc cover used in the descent.

For the affinization input, the paragraph before the affine chart asserts a group structure before finite generation of A is known. The new statement spells out the product-of-sections comparison which constructs it. Its flat-DVR generality can be checked independently as follows. A finite affine cover of the separated flat scheme has flat coordinate rings on its charts and intersections. Its global sections are torsion-free over the DVR and therefore flat. Flat affine base change computes sections of each chart times G; taking the finite equalizer for the cover and tensoring with the flat module of global sections identifies sections of G times G with A tensor A. Applying the same comparison to triple products verifies the group diagrams, and the canonical map respects the operations by its definition. This argument does not assume the generic fibre affine. It is not a claim that Mathlib's already-affine Hopf instance settles the lemma.

For the principal-translate input, the precise seed in Proposition 3.1 is a *global principal* open with canonical chart map an isomorphism and meeting the special fibre; an arbitrary affine open would not suffice. With algebraically closed residue field, choose a rational point v of its nonempty special open. For any closed point x of G_k, lift x v^{-1} to an R-section using smoothness and henselianity. Its translate of the seed contains x. The special fibre is finite type over k, so an open containing every closed point is the whole fibre. Together with the generic principal open this covers G; quasi-compactness gives finitely many translates. Translation pulls f back to a global section and preserves affineness. No connectedness or irreducibility is used. This establishes the intended meaning of the new statement; it is strictly weaker than affineness of the smooth group and is not the item's conclusion under a different name.

Step 1 uses exactly the new finite smooth cover, affine-base-change permanence, and finite base-change/affine-source permanence. I checked the finite map direction: q_L has affine *target* G_L, so it is its *source* N_L that becomes affine. No assertion that G_R' is already affine is used.

Step 2 uses smooth-implies-flat to meet the affinization lemma's flat hypothesis; that lemma explicitly gives the group law and homomorphism u, not merely a scheme or a ring. The qcqs-over-affine lemma applies to N over Spec R' because N is separated and finite type. It supplies precisely the qcqs assumption of the chart lemma used next.

Step 3 uses the principal-translate node for a cover of N by global principal affine opens. The existing 01P8 node explicitly identifies the *canonical* map on each chart with an isomorphism onto D(f_j); it is not just a localization-of-modules lemma. The inverse maps agree because each is the inverse of the restriction of u, so gluing produces the claimed open immersion. The separate quasi-compactness lemma applies to the commutative triangle N -> H -> Spec R': its first map to the base is quasi-compact, and H's structure map is affine, hence quasi-separated by the cited permanence node. Thus the immersion meets the quasi-compactness hypothesis in step 5.

Step 4 uses the open-immersion base-change node, then the *full* statement of the existing 04Q6 node. An R'-group gives an absolute groupoid over Spec k after taking the special fibre; u_k respects all operations. That existing statement requires only openness of the image, not finite type or separatedness of H_k. The fibre H_k is V(pi) in H, so its closed image is closed in H. The equality of this image with u(N) intersect V(pi) is the topological description of the pullback of an open immersion; no scheme-theoretic factorization through a closed stratum is inferred merely from containment of sets.

Step 5 uses exactly all three hypotheses in the existing 0ABH statement: u is a quasi-compact immersion, its inverse image of D(pi) is the already-affine N_L, and its image intersect V(pi) is closed. The DVR identity R'[1/pi]=L gives the first identification. This step obtains N affine; it does not assume it during the chart or group arguments.

Step 6 uses the finite-surjective affine-target theorem in its correct direction to obtain G_R' affine. The new cover node supplies the fpqc covering of the original base; the existing descent node then applies to the structure morphism of G. Over the affine base, an affine source G_R' does give an affine structure morphism (inverse images of principal base opens are affine principal opens of that affine source). Finally affine-morphism permanence over an affine base proves G affine. The citations quote these actual statements, rather than their proof internals.

I tested the hypotheses on the trivial group Spec R, finite constant disconnected groups, a smooth disconnected group, and nonreduced finite flat groups such as mu_p in residue characteristic p. Nothing requires connectedness, reduction of the original group, or a perfect original residue field. The finite smooth cover may be inseparable generically, which is permitted. The residue-field assumptions occur only after faithfully flat base change. The affinization may be non-Noetherian; neither the open-image theorem nor 0ABH requires a Noetherian target. No use of a non-affine intersection as affine is made. All new statements introduce their rings, schemes, maps and hypotheses and cite the appropriate definition nodes. All are statement-only and strictly smaller than the item. No dependency leads back to the item; new-node provenance via lists are not logical dependencies. The search outputs, including the exact Mathlib hypotheses excluding possible matches, were read before deciding the verdicts.
