# Q29: lem-trf-exceptional-internal-hom-composition

## Files written

- dag/nodes/sec-trace-formula/lem-trf-exceptional-internal-hom-composition.json — existing statement split into seven proof steps; no statement or hypothesis change. Source paragraph corrected from §0.3(a) to §0.3(b), where equations (0.2)–(0.3) actually appear.
- citations.json — a verbatim statement quotation for every cited node in every proof step.
- report.md — this report. Sandbox-only reading material and the search log are not delivery nodes.

## New nodes

None. No Mathlib leaves created. All needed infrastructure already has DAG statements. The composition calculation remains in the item's proof rather than being moved to a child restating the item.

## Attachments

None. Searched the read-only project under WeilConjectures/ for the exact blueprint tag and exceptional/internal-Hom terminology. BoundaryDuality.lean:56 has AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom, but its conclusion is only existence of an isomorphism on an etale derived category. It states neither this pro-etale constructible canonical map nor its composition equation, so it is not an attachment. TraceFormula/Defs.lean has exceptional adjunction naturality, not the requested composition identity. No use of upstream sorry declarations as finished proofs.

## WANTED

None. All material used is present locally.

## Corrections and scope

The item was unsplit and the sandbox had no earlier attempt. Its mathematical statement is well typed after the source identifications it explicitly requires. The original source reference named §0.3(a), but equation (0.3) is in §0.3(b). Moreover the paper writes the inverse of our E_h. The split explicitly takes that inverse and specifies the projection-map direction, rather than identifying maps only because both are isomorphisms. No STATEMENT-DISPUTED correction is necessary.

The current blueprint ancestor lem-trf-local-term-locality and its unit sk-i-curve-zero correct the invalid ordinary stalk/internal-Hom argument by the contracting-correspondence theorem. This split preserves the recorded ancestry via external-duality-composition and trace-class-open-restriction, and supplies only formal exceptional-exchange composition; it does not revive the invalid stalk argument or change the unit route. No chapter/unit file was edited.

## Searches

Read the existing four recorded searches on the item. Ran and read five further searches with msearch.py in this sandbox: leanfinder with two phrasings (geometric exceptional exchange and a general closed-monoidal projection/adjunction formulation), loogle CategoryTheory.Adjunction.comp, grep for upperShriek/Hom or exceptional/Hom, and leansearch for the canonical comparison's composition coherence. All services answered; grep had zero hits. Generic Adjunction.comp and comp_counit_app give the already-recorded composite-adjunction infrastructure; the expComparison and comparison_iso hits assume Cartesian monoidal categories and do not state a two-functor projection/exceptional comparison. Read Monoidal/Closed/Functor.lean, including its CartesianMonoidalCategory hypotheses. Ordinary scheme-module pullback pseudofunctor results likewise do not give exceptional internal Hom. None is an exact match or one-line specialization of the item. Exact queries and results are retained in mathlib_searches and searches.jsonl.

Searched the whole DAG and the imported blueprint by exceptional internal Hom, projection/composition, adjunction/composition and counit/composition; ran blueprint_refs.py ancestor and search. Existing exchange gives the individual canonical isomorphism, not its composition identity. Existing fix-prop-projection-formula supplies naturality and composition of the projection maps, and the existing composite-adjunction/conjugate definitions supply exactly the required Hom-bijection normalization. These suffice without new nodes. Generic tool citations are declared in split_report.tool_uses; none replaces a unit proof step.

## Review by Q29

I read Varshavsky's local PDF, pp. 5–6, §0.3(a)–(b), particularly the evaluation description of (0.3) via (0.2), and the current main-20261015 blueprint proof of exceptional-internal-hom-exchange. The latter spells out the five Hom bijections defining our forward canonical exchange. I also read the projection-formula proof in main-20261015, which identifies these as the specified projection transformations and cites their composition coherence, and the current ancestor statement/proof and unit/chapter records. There are no new nodes requiring independent source checks. I used no SGA source: the relevant formulas were read in Varshavsky and the blueprint, and the abstract adjunction/currying statements in Stacks.

For step 1, I opened def-trf-admissibility and checked that it specifies the constructible restrictions, actual adjunctions, and the exceptional composition comparison as conjugate of compact-support composition. I checked thm-sf-comp-composition really gives Ff ≅ R(cj)_! for separated finite-type maps of finite-type schemes; its etale-origin constructible restriction is the one specified in admissibility. The pullback-composition statement gives L(cj)* ≅ Lj*Lc* on ringed pro-etale sites with compatible constant coefficient maps. The pullback-Tor and tensor-ctf statements and proetale-internal-hom-ctf statement explicitly allow finite-type schemes without separatedness of their structure maps. They give precisely LM, lLM, Q, H, P and the tensor objects needed below. The composite adjunction is on the same full subcategories because each functor preserves them. Nothing requires M to be site-perfect or j to be open, smooth or proper.

For step 2, I read Stacks sites-cohomology.tex, labels lemma-internal-hom (08J9) and lemma-section-RHom-over-U (08JA), and opened both cited DAG statements. One gives derived currying and the other gives H^0(RHom) = Hom, so together they actually imply the displayed tensor–Hom adjunction. The compatible small pro-etale skeletons meet their small-site condition. A definition of internal Hom alone would not have supplied this result.

Step 3 takes the individual canonical comparison from exceptional-internal-hom-exchange and unpacks its meaning from Varshavsky (0.2)–(0.3), with the direction reversed. The three displayed arrows are the projection map, F_h of evaluation, and the exceptional counit. The two adjunctions of steps 1–2 transpose precisely this arrow. The projection theorem's statement explicitly asserts invertibility at finite coefficients, naturality in both inputs and compatibility with composition, on bounded constructible/finite-Tor domains. It applies to our schemes: the current def-fix-six-functor-datum says finite-type schemes and separated finite-type morphisms, not separated structure maps. The source's inverse construction, containing inverse projection followed by the counit, reverses these same Hom bijections. This proves the characterization of the named canonical comparison; it does not quote an unasserted compatibility from the exchange node's proof.

Step 4 is just substitution of j, LM and GN in step 3. Its a has type fP → H and its uncurry has type fP ⊗ LM → GN; thus it is a short elementary instance and cites no additional result.

For step 5 I opened def-weil-pbc-composite-adjunction and read Stacks categories.tex label lemma-compose-counits (0DV0). The statement gives the composite counit epsilon_c followed after F(epsilon_j), in that order. Naturality of epsilon_j at E_c gives the displayed rewrite before uncurrying; naturality of the projection map at a gives the second equality. Substituting step 4 gives the complete five-factor arrow. None of these equalities is hidden behind an appeal to general coherence.

For step 6 I opened def-weil-pbc-adjunction-conjugate. Its formula identifies the right comparison with the transformation inducing the precomposition maps on Hom sets. Admissibility explicitly chooses this conjugate, so kappa transports the cj-adjunction to the composite adjunction, not to an arbitrary adjunction on an isomorphic functor. The composite-adjunction statement then gives exactly the same ordered counits. The projection theorem explicitly states composition compatibility; I wrote out its instance with intermediate targets to check the orientation. The first-input pullback comparison and kappa_N in the second input transport evaluation by the natural Hom bijection of step 2. This yields literally the arrow from step 5, with common source FfP ⊗ M and target N. Step 7 uses injectivity of the two Hom bijections to conclude equality, without a Yoneda-size assumption.

I checked identity morphisms: projection composition reduces to one projection, and the identity adjunction contributes identity counits. I checked zero M or N: the relevant Hom objects and evaluation maps are zero and the displayed composites agree. The proof allows general separated finite-type j and c, as the item requires, and does not assume properness, smoothness, or site-perfect inputs. Keeping the Hom factor first avoids any tensor swap or Koszul sign. I checked each citations.json quotation against the cited statement, proof_deps against the union of uses, and all seven steps for hidden intermediate claims. Each step is below 2000 characters; the formal comparison is written as a calculation in the item, not exported as a disguised copy of the item.

## Not duplicates

No new nodes, hence no new/existing pairs. The item is not a duplicate of the individual exchange theorem: it asserts an equality involving two composable geometric morphisms and the specified compositor, whereas that theorem asserts invertibility and naturality for one morphism.

## Unfinished work

No mathematical step remains in this one-level split. Its cited infrastructure nodes remain their own items. Required server validation and direct delivery follow this report.
