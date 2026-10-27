## Worker report

Q59 repairs the human's 2026-10-21/22 re-split return. The assigned sandbox contained only dispatcher markers, no delivered nodes, report, citations or searches. I therefore continued the reviewed eight-step version on current main, preserving its statement, metadata, searches, sources and route. The reviewed Lean declaration in `lean/Sheaf/AlgebraicGeometry/RegularPointBlowupGeometry.lean:86` still ends in `sorry` at line 99. No exact finished declaration was found under WeilConjectures, by the blueprint tag, declaration name or blowup/local-ring concepts. No attachment is claimed. No Lean file was written, and no compiler or build was run.

The parent statement and statement dependencies are unchanged. Two genuine general-purpose interfaces now divide the substantial work, both `unsplit`, with no proof steps or proof dependencies:

- `lem-sfb-schematic-integral-open-criterion`: derive integrality and explicit affine embeddings into a field from a schematically dense integral open. This isolates the dense-open/function-field argument, not a new name for the blowup conclusion.
- `lem-sfb-local-spectrum-base-change-stalks`: for any morphism and any base point, identify the base-changed affine charts, the unique lifts of fibre points, the induced local-ring isomorphism with its explicit fraction inverse, and closedness of lifts of closed points. This isolates the scheme-localization argument, independent of blowups and regularity.

The old integrality argument (step 2) and the point/stalk argument (steps 5-6, plus the topological closedness argument in 8) are separate substantial tasks of comparable size. The parent still performs the finite-generation, properness and Noetherianity setup, the complement argument, flat base change of blowups, and application of the existing local surface theorem. Its proof text is 2554 characters (four steps), below the 3000-character limit; no step exceeds 2000 characters. This is a change to the dependency structure, not an unchanged re-push.

## Sources and route

Read AGENTS, GOAL, SETUP (including all three blueprint levels), stages/1-dag, worker role, standing stage-1 brief, tools/README, the item's chapter/unit, and delivery-errors B-E (including their repeated historical version). The relevant blueprint ancestry is the inherited alteration-reduction prerequisite for det-thm-sf-ctf-stability-direct-images proof (3), via nodal-trait rational domination, specifically regular-point-blowup geometry before contraction. `blueprint_refs.py ancestor` returns None for this created-node chain; the new nodes therefore inherit null from.node and the full via chain with this item prepended. Their from.place names the exact original subargument. No chapter or unit route was changed.

Read local Stacks resolve.tex 0AGQ (lemma-blowup) and 0AGR (lemma-blowup-regular), including the exceptional projective-line/Cartier-equation calculation. For the new dense-open node I read morphisms.tex 01RE (lemma-characterize-scheme-theoretically-dense) and 01RV (lemma-integral-scheme-rational-functions), integral case. Its proof task is the original injection argument: restriction embeds each nonempty affine coordinate ring in sections on its intersection with the dense integral open, and those sections embed in the generic field by affine fraction maps and sheaf separation. Thus its conclusion is not obtained merely by asserting topological density.

For the new local-spectrum node I read schemes.tex 01J6 (lemma-morphism-from-spec-local-ring) and 02NA (equation-canonical-morphism), algebra.tex 00DK (lemma-tensor-localization) and 00E3 (lemma-spec-localization). The statement records the actual affine model and fraction inverse rather than the vague instruction 'transport local rings'. For the parent's applications I also read divisors.tex 0805 (lemma-flat-base-change-blowing-up), 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), and 02NS (lemma-blowing-up-projective, supplying the proper-blowup tool). No SGA source is used.

## Review by Q59

I checked the two new statements against the source arguments with their objects fixed before using them. In the first, V is itself integral and the sheaf map is injective; a merely dense open on a nonreduced scheme would not suffice. Quasi-compactness of its inclusion is explicitly assumed to match the project's density definition. Every affine open W has W intersect V nonempty: otherwise injectivity sends the nonzero ring of a nonempty affine to the zero ring. Its maps to K are restrictions and germs; the field is the generic stalk of V, not an unspecified choice. The ring embeddings establish integrality of Z, including nonemptiness inherited from V.

For the second I verified that p need not be closed and f need not be flat, proper, Noetherian or of finite type. On the affine chart, the image of S avoids Q because Q contracts to the prime for p. Tensor-localization gives the whole inverse image of W, not just a neighbourhood of one lift. Prime correspondence therefore gives global uniqueness. The inverse of the local map sends (d/s)/(e/t) to dt/(se), with s outside Q and e outside Q, so every denominator is permitted. Prime correspondence permits e to be chosen outside Q. Fraction equivalence makes the maps well-defined even with zero divisors. The projection to Spec A sends the lift to its maximal ideal, because the contracted prime is p. Closedness follows from the preimage of the closed singleton being exactly the singleton of the unique lift. This is independent of properness.

New assembly step 1 uses the statement of def-sbc-closed-immersion-ideal-sheaf for quasi-coherence and affine ideals, def-weil-pbc-noetherian-ring for finite generators, pqf-def-coherent for their finite-free surjections, and lem-weil-pbc-affine-open-stalk-localization for the actual local ring. A zero point ideal in that affine would make its maximal ideal zero and hence the local ring a field; dimension two excludes this. lemma-nagata-blowup-proper really assumes a finite-type quasi-coherent ideal, which was just checked; def-weil-proper-morphism supplies finite type, and lem-weil-pbc-finite-type-over-noetherian supplies both parts of Noetherianity. These are theorem citations, not conclusions inferred from a definition of blowup.

New assembly step 2 uses the field-at-the-generic-point clause of lem-sc-integral-function-field-affine-fraction, and def-pc-integral-scheme to check the nonempty integral complement. Its generic point cannot be the dimension-two center. The statements of lem-weil-pbc-locally-noetherian-quasi-separated and lem-weil-pbc-noetherian-open-subscheme-noetherian give exactly qcqs for the base and quasi-compactness for its complement. det-nagata-boundary-divisor-cartier explicitly gives the scheme-theoretic density of the inverse-image open under exactly those hypotheses. thm-nagata-global-blowup-complement gives the required isomorphism to U. The inverse-image open has quasi-compact inclusion because every open in a Noetherian scheme is quasi-compact (apply the open-subscheme lemma to the affine intersections as well). The new criterion then applies with Z=X' and V=b^-1(U), without any regularity assumption on X'.

New assembly step 3 uses def-weil-regular-scheme for regularity of A, not just of affine coordinate rings. lem-weil-pbc-spec-local-ring-canonical-morphism explicitly includes flatness and the affine localization presentation, so its citation is adequate. The ideal pulls back to p R_p, the maximal ideal of A. I cite both def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change: the latter's statement 'the constructed comparison' alone would not specify its source and target. The displayed fibre product has the local spectrum in its first factor, matching the definition.

New assembly step 4 uses the new local-spectrum node for unique lifts, their local-ring isomorphisms, closedness and the equation on the base point. The existing lem-sfb-local-surface-maximal-blowup-geometry actually states regularity for the entire local blowup, and dimension two for all closed points of its exceptional fibre. Thus nonclosed exceptional points get regularity without any dimension-two assertion. Closed points in X' lift to closed points in Y and hence in its exceptional fibre, which checks the exact hypothesis of the dimension clause. Outside the center the isomorphism already proved in step 2 gives the regular local rings. def-weil-regular-scheme then gives regularity of the locally Noetherian X', and def-weil-pbc-krull-dimension-ring explains why a ring isomorphism preserves prime-chain dimension. Every cited statement was opened; citations.json quotes the full actual statements for all citations, so there is no inferred strengthening or appeal to a proof rather than a statement.

I tested the dense-open node on Z=V=Spec k, affine integral curves with a nonempty open, and an attempted embedded nilpotent at the missing point: that last example fails the stated sheaf-injectivity hypothesis, as required. Empty V is excluded by integrality. I tested the local-spectrum node on f=id_X, on the base change from the affine plane at its origin, on the generic exceptional point of a surface blowup (local dimension one), on nonrational closed exceptional points, and with rings having zero divisors. It does not identify the entire base-changed scheme with the fibre and makes no rational-residue-field assumption. The parent also allows points away from p to have other local dimensions.

Delivery-errors B1-B10: nodes have only self-contained statements, definition dependencies, correct single-backslash TeX, tags with labels, and real searches; the new nodes are not reported as Mathlib leaves or closed declarations. C1-C8: all non-elementary assembly inputs are nodes, all uses were read, their quotes were copied, and no dependency points back to the item. The two new nodes use only notions in their statement-dependencies; no proof dependencies are smuggled into them. D1-D5: these are independent scheme arguments with different hypotheses, not clauses 'X' is regular' or 'closed points have dimension two' moved into helpers. E1-E7: the flatness, finite generation, qcqs, closedness, regular-local and dimension hypotheses have each been checked where used; no statement correction or dispute was needed. The long-step check finds no step above 2000 characters. The original detailed arguments are retained verbatim below to avoid losing work while the new nodes are queued for other workers.

## Mathlib searches

The parent retains all its recorded prior searches. Each new node was searched with leanfinder, loogle and grep through the required msearch.py, with a second semantic phrasing; leansearch was attempted for each and returned the service rate-limit error, correctly recorded as unavailable. Searches.jsonl is the actual tool log. Hit statements were read. isIntegral_of_isOpenImmersion goes from the ambient scheme to its open, the reverse of the first lemma. SchemeTheoreticallyDominant.isReduced gives reducedness, not the field-embedding criterion. SpecToEquivOfLocalRing concerns morphisms from local spectra; stalkMapIsoOfIsPullback assumes an open immersion, which Spec O_X,p -> X need not be. Preimmersion gives an embedding and surjective stalks, not this combined base-change/fraction description. Relevant Mathlib SchemeTheoreticallyDominant, Preimmersion and FunctionField sources were read. Neither helper is an exact match or a one-line specialization. No search that did not run is recorded.

## Tool uses and dependencies

The parent retains the maintainer-approved generic tools det-nagata-boundary-divisor-cartier and lem-weil-pbc-spec-local-ring-canonical-morphism. Their roles are unchanged: density of a blowup complement and flat canonical localization. No trace-formula projectivity node or alternative alteration route is introduced. The old direct affine/tensor/localization proof citations now describe the work isolated by the new local-spectrum lemma and are retained verbatim in the allocation below; they are no longer direct proof dependencies of the parent. No existing node is edited apart from the assigned item. No hollow definition is introduced.

## Not duplicates

lem-sfb-schematic-integral-open-criterion vs def-sc-rational-functions: the existing statement concerns The ring of rational functions of a scheme; the new statement assumes a schematically dense integral open in an arbitrary ambient scheme and concludes ambient integrality and explicit embeddings of its affine rings into the generic field.

lem-sfb-schematic-integral-open-criterion vs lem-sc-integral-function-field-affine-fraction: the existing node assumes an integral ambient scheme and describes its affine function field; the new criterion derives integrality of a previously arbitrary ambient scheme from a dense integral open.

lem-sfb-schematic-integral-open-criterion vs lem-sc-integral-scheme-stalks-in-function-field: the existing statement concerns Integral schemes: sections and stalks inject into the function field; the new statement assumes a schematically dense integral open in an arbitrary ambient scheme and concludes ambient integrality and explicit embeddings of its affine rings into the generic field.

lem-sfb-schematic-integral-open-criterion vs lem-sc-rational-functions-generic-stalks: the existing statement concerns Rational functions are the product of the generic local rings; the new statement assumes a schematically dense integral open in an arbitrary ambient scheme and concludes ambient integrality and explicit embeddings of its affine rings into the generic field.

lem-sfb-schematic-integral-open-criterion vs lem-trf-affine-schematic-density-criterion: the existing statement concerns Affine criterion for schematic density of finitely many principal opens; the new statement assumes a schematically dense integral open in an arbitrary ambient scheme and concludes ambient integrality and explicit embeddings of its affine rings into the generic field.

lem-sfb-schematic-integral-open-criterion vs lem-trf-schematic-density-generic-fibre-open: the existing statement concerns Schematic density in fibres spreads from the generic fibre; the new statement assumes a schematically dense integral open in an arbitrary ambient scheme and concludes ambient integrality and explicit embeddings of its affine rings into the generic field.

lem-sfb-local-spectrum-base-change-stalks vs lem-pc-intrinsic-flat-module-stalk-tensor-presentation: the existing statement concerns Affine quasi-coherent stalks are tensor products of sections with the stalk ring; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-sc-dual-number-scheme-pushout: the existing statement concerns Spec of the square-zero algebra $K[\epsilon_1,\dots,\epsilon_n]$ is the pushout of $n$ copies of the dual-number scheme; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-trf-fibre-module-localization: the existing statement concerns The residue-field fibre module is the localization of the prime quotient; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-trf-localization-maximal-contraction: the existing statement concerns Contraction of the maximal ideal of a prime localization; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-algebra-localization-away-base-change: the existing statement concerns Localization away in an algebra commutes with arbitrary base change; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-essentially-smooth-base-change: the existing statement concerns Essential smoothness under base change; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-fibre-dimension-neighborhood-localized-bound: the existing statement concerns Global dimension bound for localized fibres; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-fibre-ring-primes-bijection: the existing statement concerns Primes of the fibre ring are the primes over p; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-formal-glueing-canonical-maps: the existing statement concerns The canonical maps of formal glueing: localized S-module structure, swap of two localizations, localization of a base change; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: the existing statement concerns The generic fibre of a domain over a domain is an irreducible spectrum; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-away-tensor-iso: the existing statement concerns Localization of a module at an element is base change to the localized ring; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-base-change: the existing statement concerns Base change of a localization is a localization; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-dimension-chains-below-prime: the existing statement concerns The dimension of the localization at a prime is the length of the longest chain of primes below it; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-ideal-kernel-generators: the existing statement concerns Localization of the ideal multiplication kernel; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-module-tensor: the existing statement concerns Localization of a module at an element is the base change to the localized ring, naturally; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-of-regular-ring: the existing statement concerns A localization of a regular ring is regular; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-prime-residue-field-iso: the existing node is an algebraic localization/prime/residue-field theorem; the new statement constructs the scheme base-change charts for arbitrary f:T -> X and proves global uniqueness and closedness of point lifts in that scheme.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-projective: the existing statement concerns The localization of a projective module is projective; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-quotient-by-prime: the existing statement concerns Primes of a localization and the quotients by them; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-spectrum-embedding: the existing statement concerns Spectrum embedding for arbitrary multiplicative localization; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localization-tensor-over-base: the existing statement concerns Localization over S commutes with tensoring over R; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localize-localization-at-prime: the existing statement concerns Local rings of prime and principal localizations; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-localized-finite-quotient-charts: the existing statement concerns Canonical local charts of a positive finite-algebra quotient; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-morphism-from-spec-local-ring: the existing statement concerns Morphisms from the spectrum of a local ring (Stacks 01J6); it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-polynomial-complete-local-fibre-reduction: the existing statement concerns Reduction of polynomial completion fibres to complete local domains; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-primes-of-localization: the existing statement concerns Primes of prime and principal localizations; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-regular-through-localization: the existing statement concerns A regular map factoring through a localization is regular from the localization; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-smooth-over-essentially-smooth-base: the existing statement concerns Smooth algebras over an essentially smooth base have localization models; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-local-spectrum-base-change-stalks vs lem-weil-pbc-spec-local-ring-canonical-morphism: the existing node describes the canonical map Spec O_X,p -> X itself; the new statement treats its pullback along every f:T -> X, with unique fibre-point lifts, explicit affine/local-ring formulas and preservation of closedness.

lem-sfb-local-spectrum-base-change-stalks vs new-lem-pc-complex-localization-unit-kernel: the existing statement concerns Denominator kernel of the scalar-extension unit on ordinary complex cohomology; it does not state the general scheme-level local-spectrum base-change comparison, its unique lifts for an arbitrary morphism, and their closedness. The new node includes that scheme comparison, not just localization algebra.

lem-sfb-schematic-integral-open-criterion vs lem-sfb-integral-blowup-projective-geometry: the existing node proves blowup integrality and projectivity, while the new node has no blowup and gives a general dense-open criterion; the existing statement does not supply the criterion. It is not cited to reintroduce projective-bundle route dependencies.

## Allocation of every returned argument (verbatim retained work)

### Returned step 1

Allocation: Parent assembly step 1: the finite-generation/nonzero-center setup remains explicit.

Let $\mathcal I$ be the ideal of the reduced closed point $p$. By [def-sbc-closed-immersion-ideal-sheaf] it is quasi-coherent and, on an affine neighbourhood $\operatorname{Spec}R$ of $p$, is the sheaf of the maximal ideal $\mathfrak p\subset R$ corresponding to $p$. Choose affine neighbourhoods from a locally Noetherian cover of $X$. Their coordinate rings are Noetherian, so their ideals are finitely generated by [def-weil-pbc-noetherian-ring]; the local generators give a surjection from a finite free sheaf, so $\mathcal I$ is of finite type by [pqf-def-coherent]. On such an affine neighbourhood of $p$, [lem-weil-pbc-affine-open-stalk-localization] identifies $R_{\mathfrak p}$ with $\mathcal O_{X,p}$. If $\mathcal I$ were zero then $\mathfrak p=0$; since $\mathfrak p$ is maximal, $R$ and hence $R_{\mathfrak p}$ would be a field. A field has Krull dimension zero, contradicting the dimension-two hypothesis. Thus $\mathcal I$ is nonzero.

Original cited nodes: def-sbc-closed-immersion-ideal-sheaf, pqf-def-locnoeth, def-weil-pbc-noetherian-ring, lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-krull-dimension-ring, pqf-def-coherent

Source: {"document": "literature/stacks-project/schemes.tex", "place": "Tag 01IN (lemma-closed-subspace-scheme); properties.tex Tag 01OV (definition-noetherian); algebra.tex Noetherian definition; Tag 01HV (lemma-spec-sheaves), part (6)."}

### Returned step 2

Allocation: Parent step 1 carries properness/Noetherianity. Parent step 2 checks density and nonemptiness. The affine-to-generic-field argument is the independent task lem-sfb-schematic-integral-open-criterion.

By [lemma-nagata-blowup-proper], applied to the finite-type quasi-coherent ideal $\mathcal I$ of step 1, $b$ is proper. Properness includes finite type by [def-weil-proper-morphism]. Since $X$ is Noetherian, [lem-weil-pbc-finite-type-over-noetherian] now gives that $X'$ is Noetherian (both locally Noetherian and quasi-compact). For integrality put $U=X\setminus\{p\}=X\setminus V(\mathcal I)$. The scheme $X$ is quasi-compact and, being locally Noetherian, quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]; the open $U$ is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Hence [det-nagata-boundary-divisor-cartier] applies to $(X,U,\mathcal I)$ and makes $b^{-1}(U)$ scheme-theoretically dense in $X'$ [def-nagata-scheme-theoretically-dense-open]. The open $U$ is nonempty: by [lem-sc-integral-function-field-affine-fraction] the local ring at the generic point of $X$ is a field, of dimension $0$, so that point is not $p$. Every nonempty affine open of $U$ is one of $X$, hence has a domain as ring, so $U$ is integral [def-pc-integral-scheme]; by [thm-nagata-global-blowup-complement] $b^{-1}(U)\cong U$ is integral with function field $F$, the function field of $X$. Now $X'$ is nonempty. Let $V\subseteq X'$ be a nonempty affine open. Density makes $\mathcal O_{X'}(V)\to\mathcal O_{X'}(V\cap b^{-1}U)$ injective, so $V\cap b^{-1}U\neq\varnothing$. Sections of the integral scheme $b^{-1}(U)$ over a nonempty open inject into $F$, since they do on each nonempty affine open of a cover by [lem-sc-integral-function-field-affine-fraction]. Hence $\mathcal O_{X'}(V)$ embeds in the field $F$ and is a domain, and $X'$ is integral by [def-pc-integral-scheme].

Original cited nodes: lemma-nagata-blowup-proper, def-weil-proper-morphism, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-noetherian-open-subscheme-noetherian, det-nagata-boundary-divisor-cartier, def-nagata-scheme-theoretically-dense-open, lem-sc-integral-function-field-affine-fraction, def-pc-integral-scheme, thm-nagata-global-blowup-complement

Source: {"document": "literature/stacks-project/divisors.tex", "place": "Tags 02NS (properness), 02OS (lemma-blowing-up-gives-effective-Cartier-divisor: the center pulls back to an effective Cartier divisor, so its complement is scheme-theoretically dense) and the blowup-complement isomorphism; integrality from that density instead of Tag 02ND."}

### Returned step 3

Allocation: Parent steps 2 and 4: complement isomorphism and regularity away from the exceptional fibre.

The zero set of $\mathcal I$ is precisely $\{p\}$. Therefore [thm-nagata-global-blowup-complement] identifies $b^{-1}(X\setminus\{p\})\to X\setminus\{p\}$ with an isomorphism. For a point $q$ in this open complement, its local ring in $X'$ is consequently isomorphic to $\mathcal O_{X,b(q)}$. That ring is regular local by regularity of $X$ and [def-weil-regular-scheme]. This proves regularity at every point away from the exceptional fibre, as well as the asserted complement isomorphism.

Original cited nodes: thm-nagata-global-blowup-complement, def-weil-regular-scheme

Source: {"document": "literature/stacks-project/divisors.tex", "place": "Tag 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), part (1); properties.tex Tag 02IT (lemma-characterize-regular)."}

### Returned step 4

Allocation: Parent step 3: canonical flat local-spectrum map and the maximal-ideal blowup comparison.

Put $A=\mathcal O_{X,p}$ with maximal ideal $\mathfrak m$. It is a regular local ring by [def-weil-regular-scheme], and its dimension is $2$ by hypothesis. The canonical morphism $c:\operatorname{Spec}A\to X$ is flat and is, on an affine neighbourhood $\operatorname{Spec}R$ of $p$, induced by $R\to R_{\mathfrak p}=A$, by [lem-weil-pbc-spec-local-ring-canonical-morphism]. The pulled-back ideal of $p$ is $\mathfrak pR_{\mathfrak p}=\mathfrak m$. Consequently [def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change] give an isomorphism over $\operatorname{Spec}A$,
$$Y:=\operatorname{Bl}_{\mathfrak m}(\operatorname{Spec}A)\ \cong\ \operatorname{Spec}A\times_X X'.$$
Write $h:Y\to X'$ for the second projection under this identification.

Original cited nodes: def-weil-regular-scheme, lem-weil-pbc-spec-local-ring-canonical-morphism, def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change

Source: {"document": "literature/stacks-project/divisors.tex", "place": "Tag 0805 (lemma-flat-base-change-blowing-up); schemes.tex Tags 01J6 (lemma-morphism-from-spec-local-ring), 02NA (equation-canonical-morphism)."}

### Returned step 5

Allocation: The affine-chart and global unique-lift task is now lem-sfb-local-spectrum-base-change-stalks, applied in parent step 4.

Fix $q\in X'$ with $b(q)=p$. Take $U=\operatorname{Spec}R\subset X$ containing $p$, let $\mathfrak p\subset R$ represent $p$, and put $T=R\setminus\mathfrak p$. Choose an affine open $W=\operatorname{Spec}B\subset b^{-1}(U)$ containing $q$, with corresponding prime $Q\subset B$. Its inverse image under $h$ is the open subscheme $W\times_U\operatorname{Spec}A$ by [lem-weil-pbc-open-fibre-product]. By [lem-weil-pbc-fibre-product-affine-spectra] its ring is $B\otimes_R R_{\mathfrak p}$; by [lem-weil-pbc-localization-base-change] this ring is $T^{-1}B$ (using the image of $T$ in $B$). As $Q\cap R=\mathfrak p$, this multiplicative subset avoids $Q$. By [lem-weil-pbc-localization-spectrum-embedding] there is exactly one point $\widetilde q$ over $q$, corresponding to $T^{-1}Q$. All preimages of $q$ lie in this inverse image of $W$, so uniqueness holds globally.

Original cited nodes: lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-localization-base-change, lem-weil-pbc-localization-spectrum-embedding

Source: {"document": "literature/stacks-project/schemes.tex", "place": "Tags 01JR (lemma-open-fibre-product), 01I4 (lemma-fibre-product-affine-schemes); algebra.tex Tags 00DK (lemma-tensor-localization), 00E3 (lemma-spec-localization)."}

### Returned step 6

Allocation: The explicit mutually inverse fraction maps are conclusions of lem-sfb-local-spectrum-base-change-stalks, applied in parent step 4.

In the notation of step 5, [lem-weil-pbc-affine-open-stalk-localization] identifies the two local rings with $B_Q$ and $(T^{-1}B)_{T^{-1}Q}$. The canonical map between them is an isomorphism: its inverse sends
$$\frac{b/s}{d/t}\ \longmapsto\ \frac{bt}{sd},\qquad s,t\in T,\ d\notin Q.$$
Here $s\notin Q$ and $d\notin Q$, so the denominator on the right is allowed. Every denominator outside $T^{-1}Q$ has a representative $d/t$ with $d\notin Q$ by the prime correspondence of [lem-weil-pbc-localization-spectrum-embedding]. The displayed formula and $b/d\mapsto(b/1)/(d/1)$ respect the fraction relations and are inverse, by multiplying numerators and denominators. Thus $\mathcal O_{X',q}\cong\mathcal O_{Y,\widetilde q}$, including for nonclosed $q$ over $p$.

Original cited nodes: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-spectrum-embedding

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Tag 00CO (definition-localization), Tag 00CP (proposition-universal-property-localization); schemes.tex Tag 01HV (lemma-spec-sheaves), part (6)."}

### Returned step 7

Allocation: Parent step 4: apply the existing local surface-blowup theorem and the regular-local characterization.

Apply [lem-sfb-local-surface-maximal-blowup-geometry] to the ring $A$ of step 4. Its hypotheses are exactly that $A$ is regular local and has dimension $2$, so it gives regularity of $Y$. Hence every $\mathcal O_{Y,\widetilde q}$ is regular local by [def-weil-regular-scheme]. The isomorphism of step 6 proves the same for every $q$ over $p$; step 3 already handled every other point. Since $X'$ is locally Noetherian by step 2, the local-ring characterization in [def-weil-regular-scheme] proves that $X'$ is regular.

Original cited nodes: lem-sfb-local-surface-maximal-blowup-geometry, def-weil-regular-scheme

Source: {"document": "literature/stacks-project/resolve.tex", "place": "Tag 0AGR (lemma-blowup-regular), globalized using Tag 0805; properties.tex Tag 02IT (lemma-characterize-regular)."}

### Returned step 8

Allocation: The closed-lift assertion belongs to lem-sfb-local-spectrum-base-change-stalks; parent step 4 applies the closed-exceptional-point clause and preserves dimension along its local-ring isomorphism.

Finally let $q$ be closed in $X'$ with $b(q)=p$. Its lift $\widetilde q$ from step 5 is closed in $Y$: the inverse image of the closed singleton $\{q\}$ under the continuous morphism $h$ is exactly $\{\widetilde q\}$. The point $\widetilde q$ lies in the exceptional fibre of $Y\to\operatorname{Spec}A$, since its image is $\mathfrak m$. Being closed in $Y$, it is closed in that fibre as well. The closed-exceptional-point clause of [lem-sfb-local-surface-maximal-blowup-geometry] therefore gives $\dim\mathcal O_{Y,\widetilde q}=2$. The ring isomorphism in step 6 preserves chains of prime ideals, so [def-weil-pbc-krull-dimension-ring] gives $\dim\mathcal O_{X',q}=2$, as required.

Original cited nodes: lem-sfb-local-surface-maximal-blowup-geometry, def-weil-pbc-krull-dimension-ring

Source: {"document": "literature/stacks-project/resolve.tex", "place": "Tags 0AGQ (lemma-blowup), 0AGR (lemma-blowup-regular), local Cartier-equation calculation at closed exceptional points; algebra.tex Tag 00KE (definition-Krull)."}

## Validation

Required dry run completed with exit 0: OK (not pushed) deliver/Q59/lem-sfb-regular-point-blowup-geometry at 22fdeee5283: preflight passed. The server ran the required checks. No check_dag, review_split or preflight tool was run locally. The final delivery invocation follows this completed dry run.
