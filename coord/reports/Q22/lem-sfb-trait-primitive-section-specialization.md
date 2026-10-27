## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-primitive-section-specialization.json`: statement, now split; Mathlib searches find ingredients but no exact primitive-specialization theorem. Seven proof steps, 23 distinct existing proof dependencies, no new nodes and no new Mathlib leaves.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual Q22 search records. `prepare.py` is sandbox-only preparation, not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, the item id, primitive specialization and uniformizer/section terminology. The hits concern divisors, roots and tame charts, not the assertion for an arbitrary invertible module and arbitrary nonzero generic section. No sorry declaration was accepted as finished.

## Wanted literature

None. The argument uses the local Stacks source and the existing project affine localization lemma.

## Corrections and proof route

The statement is retained verbatim. Its original source suggests a normal-domain height-one intersection argument. Instead, below the fixed unit route, I give an agent-written proof by finite affine denominator clearing followed by maximal global divisibility and local Krull intersection. This does not change a chapter or unit theorem or its route. The proof is marked `proof_origin.by = agent`; Stacks does not state this entire section lemma verbatim.

The denominator exponent is made uniform using an actual finite affine cover; local extensions agree by injectivity into a generic stalk. For the primitive normalization, fix a point of the special fibre, apply Krull intersection to its finite free stalk, and bound the powers of pi dividing the global extension. If a maximally divided section vanished on the special fibre, its coefficients on each trivializing affine would lie in pi times the coordinate ring. Divide there and glue the divisions using injectivity of pi. This contradicts maximality. In particular, the proof does not infer global-section surjectivity from sheaf exactness or use properness or completeness.

Read the chapter and the recorded unit, SETUP's three-level rule and GOAL. Also read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit, direct-image statement and proof. The latest direct-image proof (3) contains the six-functor input, not a second primitive-section lemma. The item has a long inherited provenance chain through the Q44 specialization input, with `from.node = null`; this metadata is preserved, including its precise `from.place` and `via`. Whole-blueprint searches for rational section, primitive section and line section found no equivalent imported statement. Existing algebra and scheme lemmas of other units are explicitly declared as generic tool uses in `split_report.tool_uses`.

## Not duplicates

No new nodes were created. Existing statements were reused, including the generic-stalk, affine-denominator and Krull-intersection nodes. No clause of the item was renamed as a new lemma.

## Review by Q22

I read delivery-errors B through E against the actual JSON and the sources. There are no unsplit new nodes to audit. For the item, I read Algebra Tag 031T (`lemma-normal-domain-intersection-localizations-height-1`) and Descent Tag 036D (`lemma-regular-local-smooth`), its suggested sources. The alternative proof uses Algebra Tags 00PD, 00FN and 00IQ (also the local form 00IP); I read these statements and the Krull proof. I read Schemes Tags 01I3 and 01IA, More on Algebra 0539, Varieties 056S, Properties 033N, and Morphisms 01TP, 01V6 and 01VB. For the affine denominator operation I additionally read the actual project lemma `exists_map_eq_pow_smul_of_isAffineOpen` at `lean/WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Tilde.lean:112`, its proof, and the adjacent zero criterion. Nothing was compiled or written in the repository.

1. Step 1 uses precisely the DVR definition (all ideals principal, local domain, nonzero maximal ideal), the unit-times-uniformizer-power lemma, principal-localization open immersion, open-immersion base change and the finite-presentation definition. The DVR is Noetherian because its ideals are singly generated, so the decomposition lemma's Noetherian hypothesis holds. All fractions have a power-of-pi denominator, giving K = R[1/pi]. Quasi-compactness is part of finite presentation, not inferred from local finite presentation.
2. Step 2 uses field-extension faithful flatness on affine charts and faithfully-flat surjectivity of spectra to descend connectedness from the algebraic closure. It uses only the smooth clause of `lem-pc-proper-base-change`, then smooth-over-a-field regularity and the nonempty connected regular scheme lemma. None requires a curve, an algebraically closed base, properness, or a dimension bound. Nonemptiness is supplied separately by the hypothesis, so the empty connected-space convention does not enter.
3. Step 3 uses smooth restriction and the affine smoothness equivalence, whose statement explicitly includes finite presentation of the ring map; smooth ring-map flatness and the flat-module torsion-free lemma give the injection A -> A[1/pi]. The latter is the domain case actually in force over R. The nonzero localization is a nonempty affine in integral X_K, so A is a domain. The integral-scheme definition and Hilbert basis theorem then give integrality and local Noetherianity; the generic-stalk lemma really states injectivity for sections on every nonempty open, not merely for a special chosen section.
4. Step 4 uses the invertible-module definition to obtain quasi-coherence and local bases, the affine basic-open localization node for the actual exponent-and-extension assertion, and generic-stalk injectivity for equality on overlaps. It applies to the affine U_i, not to a possibly nonaffine intersection. The exponent is the maximum of finitely many N_i and all rescaled sections restrict to the same pi^N s_K.
5. Step 5 uses the affine stalk/localization node, localization preserving Noetherianity, rank-one stalk freeness and generic injectivity from the invertible-module generic-stalk node, and the Krull-intersection node. The local ring B is Noetherian; C_x is finite free; pi belongs to its maximal ideal since x lies on the closed fibre. Thus pi B lies in the Jacobson radical, exactly the Krull node's hypothesis. The nonzero generic germ of the supplied s_K ensures t_x is nonzero, so Krull really bounds divisibility rather than merely describing a zero intersection.
6. Step 6 is elementary: the global divisibility set contains zero and is bounded by the stalk bound. A finite nonempty subset of the natural numbers has a maximum. Restriction cancels pi only over K, where it is a unit. The eventual exponent N-a is an integer and may be negative.
7. Step 7 uses the invertible-module and tensor-pullback definitions for the explicit free rank-one coefficient computation modulo pi. Vanishing means c_i belongs to pi A_i, with no need to lift arbitrary closed-fibre sections. Local divisions agree because multiplication by pi is injective, as already established in Step 3, so the sheaf axiom gives an actual global division. This is an elementary calculation, not a separate unstated theorem about global sections.

For every cited dependency I opened and read its statement. `citations.json` copies those statements verbatim, so each use has a direct C4 witness. No non-elementary inference is supported only by a definition: flatness-to-torsion-freeness, Noetherian ascent/localization, affine section denominators, regular connected integrality, generic injection and Krull intersection all have their own existing statement nodes. The remaining operations are fraction arithmetic, a finite maximum, reduction of a free module and unique sheaf gluing. Every step is shorter than 2000 characters.

Small cases checked: X = Spec R and C = O reduces a nonzero element u*pi^v of K to the unit u; negative v and either sign of the final exponent are allowed. On X = A^1_R, s_K = pi^{-d}(pi + x) normalizes to pi + x, whose reduction x is nonzero. The example s_K = pi^{-d}pi illustrates why an initial denominator-cleared extension may still need further division. No completeness or properness enters either case. If generic connectedness is dropped, X = Spec R disjoint union Spec K and the generic section (0,1) have zero restriction on the whole special fibre after every rescaling; this explains why integrality/nonzero generic germ must be justified. The actual hypotheses exclude that example. No disputed statement or source error was found.

The searches were actually run using msearch.py: LeanFinder twice with distinct formulations, LeanSearch, Loogle and source grep. I read the results: valuation uniformizers, basic-open regular functions, scalar-multiplication operations and valuative properness do not state the primitive-section existence conclusion. The earlier inherited search records are retained. No unavailable service was reported as an absence.

## Unfinished work

None in the one-level split. The existing dependencies retain their own states; this delivery adds no new downstream item. Server dry-run and delivery results are reported by the delivery command.
