# Q25: lem-a1-lisse-middle-extension

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-lisse-middle-extension.json`: statement; split into seven steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quote for every dependency of every proof step.
- `searches.jsonl`: five searches actually run through msearch.py, including a second semantic phrasing; retained as the search evidence.

New nodes: 0. New Mathlib leaves: 0. The item uses existing DAG statements only.

## Attachments

None. I searched the current read-only source by the blueprint id, recovery/unit declaration names, and the notions lisse/dense/middle extension. The current relevant file is `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Boundary.lean`. Its `AlgebraicGeometry.Scheme.isIso_unit_upperStarLowerStarAdjunction` at line 299 proves only the finite-ring, finite-locally-constant version and calls the sorried boundary-fibre input at line 276. It does not state the entire lisse Qbar_l item. I have not attached this partial result.

The imported audit instead names the nonexistent local modules `WeilConjectures.WeilSheaf.MiddleExtension` and `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension`. Whole-source searches find none of their three audited recovery names. Of the six imported `open` names, only `ProEtale.finiteLowerStar_singleFunctor_of_isAffine` still occurs in this checkout (LowerStar.lean:411); I read its statement: bounded constructibility of a derived affine pushforward, not dense-open recovery. It already belongs to the existing generic finiteness node `lem-sf-adic-affine-direct-image-finiteness`, whose statement is the affine finiteness assertion. The other five imported names have no occurrences here. These are obsolete audit dependencies, not missing ingredients of the finite-level proof delivered here. No unrelated nodes were manufactured from them.

## WANTED

None. The proof follows the unit's existing finite-level route and uses literature already present.

## Corrections and scope

The mathematical assertion is unchanged. I expanded the implicit conventions by stating that j is a dense open immersion, that coefficients are the standing lisse Qbar_l coefficients, and that j_* is underived. These conventions already occur in def-wf-middle-extension and the current blueprint item and unit.

The imported one-paragraph proof suppressed the identification of the actual adjunction unit and the passage from finite levels to an adic sheaf. I replaced it with the argument explicitly prescribed in the unit's Step 3: finite-level trivialization, normal integral constant-sheaf recovery, and transition-compatible inverse systems. This is a choice between the two arguments the unit already gives, not a departure from its route. The current main-20261015 item and unit state the same assertion; their short files carry no contrary proof requirement.

The imported unit says that a smooth curve is integral. Without connectedness that is not valid: the disjoint union of two affine lines is a smooth curve but is not integral. This delivery never infers integrality merely from smoothness. It first decomposes the normal Noetherian C_0 into its open-and-closed normal integral components. This does not change the unit's connected-curve setting; it also handles the item's possibly disconnected wording faithfully.

The general node lem-wf-dense-open-pi1-surjective has recovery as clause (3), but its dependency list already includes this item. Citing it here would create a cycle. I reuse the smaller constant-sheaf, component and trivialization nodes rather than that parent result. It is not recorded as same_as because its whole five-clause statement is different. No exact whole-statement duplicate was found by the whole-blueprint searches for lisse and dense open.

The supplied sandbox contained only dispatch marker files and no node, report, search log or delivery receipt. A process check found no running delivery for this item before work resumed. No previous mutation was repeated.

## Unfinished work

None for this one-level split. The existing dependencies keep their own stage-1 states. No Lean was written, no compiler or Lake command was run, and the shared repository and source checkouts were only read.

## Not duplicates

No new nodes. Existing lem-fin-normal-constant-open-image, lem-fin-etale-normal-components, fin2-lem-lisse-trivialized-finite-etale and the generic etale-restriction lemma are reused.

## Review by Q25

I read the item's master blueprint proof, the main-20261015 item and unit, the complete master unit proof (especially Steps 0 and 3), and the current local Lean recovery statements. For the finite-level part I read the existing finite-etale-trivialization blueprint proof and Stacks etale-cohomology.tex, Tag 09Z5, label lemma-push-constant-sheaf-from-open, including the proof of assertion (2). I checked the coefficient transition against Deligne, Weil II (1.1.1) b), c), d), printed pages 146–147, using the local PDF. For the geometry I read Stacks properties.tex, Tag 033M, label lemma-normal-Noetherian; varieties.tex, Tag 056S, label lemma-smooth-regular; morphisms.tex, Tag 01T6, label lemma-finite-type-noetherian, and Tag 03WT, label lemma-etale-open. I did not use an SGA source. The smooth-normal DAG node's external Tag 0AG0 is an indirect regular-local-ring reference; the smooth-over-a-field input itself is Tag 056S, followed by regular implies normal, Tag 0569. I leave the unrelated existing node untouched.

Step 1 uses the full statement of def-pod-lisse-l-adic-sheaves: objects are finite-stage lisse systems, their morphisms are compatible families, and rational and algebraic-closure coefficients are obtained by the specified scalar operations. This supplies a finite coefficient ring and a finite locally constant L_n for each n, and does not supply a single finite cover for all n. I explicitly allow the cover to depend on n.

Step 2 uses def-wf-middle-extension for the finite-type field and curve conventions, lem-weil-pbc-finite-type-over-noetherian for Noetherianity, lem-sc-smooth-normal for normality, and exactly the normal-Noetherian decomposition clause of rem-pc-regular-normal. All these node statements were opened. I checked that no algebraically closed field hypothesis is imported: smooth-normal is stated over any field, and the decomposition needs normality and Noetherianity, not geometric connectedness. The density argument on each clopen component is elementary and written out. Empty C_0 is treated separately.

Step 3 uses fin2-lem-lisse-trivialized-finite-etale only for a finite locally constant module sheaf over the finite ring at one level. Its statement supplies a finite etale surjection and constant finite module fibres on connected components. The definitions of finite morphism and finite type morphism, and the finite-type-over-Noetherian theorem, are cited to justify P being Noetherian. I wrote out why finite module generators also generate the algebra, rather than silently assuming finite type. No flatness, freeness or uniform finite trivialization is asserted.

Step 4 uses lem-fin-etale-normal-components on P_a over C_a, not on the possibly disconnected C_0 as if it were integral. Its source-Noetherian and base-normal-integral hypotheses have been established in Steps 2–3. Each resulting clopen integral Q_b is a connected component of P, so the chosen trivialization applies to it. The open-map node really states that the image of every open under an etale map is open. This proves V_b nonempty and dense, by testing every nonempty open O in Q_b, not just by asserting that inverse images preserve density. The Q_b jointly cover because p is surjective.

Step 5 uses the etale-inverse-image-restriction node's actual second clause, which identifies the unit with the restriction map on each object. It is not merely a definition of inverse image. I read its whole statement and checked that it applies to every etale map, including j and Q_b to C_0; the ordinary module-valued version is obtained from the same natural section formula and inverse linear maps. The direct-image definition supplies the exact section formula, including morphisms and module coefficients. The constant recovery node supplies the canonical map as an isomorphism with the four hypotheses needed here: Noetherian, normal integral, nonempty open, finite module. Because it is a sheaf isomorphism it works on every T etale over Q_b, including the overlaps used next. There is no appeal to an uncited base-change theorem or only to an isomorphism of abstract stalks.

Step 6 uses precisely the sheaf equalizer statement and etale covering-site definition. I wrote out local preimages, agreement on overlaps by injectivity, gluing, and uniqueness. This is elementary descent of an inverse map from the already proved local isomorphism, not a new lemma with separate mathematical content. The overlaps need not be affine, normal or integral: they are etale objects of Q_b, so Step 5 already applies. Module linearity and naturality follow by uniqueness of preimages. This step proves the global finite-level map is the unit, since Step 5 identifies that very map.

Step 7 uses the stated inverse-system and rationalization definitions and ordinary-direct-image section formula. I checked the transition equation with its indices: u_n t_n=(j_*j^*t_n)u_{n+1} implies t_n v_{n+1}=v_n(j_*j^*t_n). Thus the inverse family is an actual system morphism. I do not claim that arbitrary j_* towers are adic or that invariants commute with reduction. Here the target tower is adic because it is isomorphic to the original one. Both inverse equations survive rationalization and the finite-extension colimit. The same naturality equation proves compatibility with any Weil descent datum, without choosing a Frobenius-stable finite-level trivialization.

I checked small cases: j the identity, empty C_0, zero module, disconnected smooth curves, a cover with several components, and finite modules that are not free (for example Z/l over Z/l^2). None requires added hypotheses. The unipotent Kummer l-adic local system with infinite monodromy is allowed because only the finite levels are trivialized. The conclusion would fail on a nodal nonnormal curve for a constant sheaf, so the normality input is substantive and is cited.

All proof-step node citations have their literal statements in citations.json. There are no new definitions, unsearched new facts, restated clauses or cyclic uses. Each step is below 2000 characters; the longest is the explicit transition and descent calculation. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the actual node statements and sources: the possible failures specific to this item (wrong coefficient category, disconnectedness, density under pullback, unit normalization, hidden cover gluing, adic compatibility and the stale Lean audit) are addressed above. Generic geometric tools of other units are declared individually in split_report.tool_uses; the constant, component and trivialization tools are the ones named by the unit itself.
