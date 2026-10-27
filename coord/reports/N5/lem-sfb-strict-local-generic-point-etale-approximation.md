## Worker report

Item: lem-sfb-strict-local-generic-point-etale-approximation. Group N5. Stage 1 only, 2026-10-24.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-strict-local-generic-point-etale-approximation.json: existing statement, now split into ten steps; no exact Mathlib match.
- citations.json: thirty verbatim citations, covering every use in every step.
- report.md: this report. searches.jsonl records the actual required msearch.py calls. write_split.py is sandbox-only scratch work, not a delivery file.

No new nodes and no Mathlib leaves. No Lean files, compilation, repository edits, launcher edits, or direct git commands.

### Attachments

None. Searched the live library under lean/WeilConjectures/ for the exact blueprint tag and the strict-henselization, generic-point and étale-approximation notions. StrictHenselizationGeneric.lean concerns localization at a generic point; EtaleTraitStalk.lean supplies the smaller stalk-DVR result; neither states this item. No complete project declaration supplies all its clauses.

### Literature wanted

None. All required Stacks source files and the current blueprint are locally available.

### What changed and what was wrong

The imported node was statement-only. Its source annotation promises an affine local DVR refinement but supplies no proof. Merely localizing an étale algebra at its marked prime would leave the finite-presentation conclusion unjustified. The new proof makes the refinement explicit: the étale algebra has finite spectrum, so its prime localization is already a principal localization. It needs no henselian hypothesis on R and does not assume that an étale neighbourhood is finite or integral over R.

The statement, statement dependencies, source, created record and all maintainer-owned fields are unchanged. No STATEMENT-DISPUTED correction was necessary. The source's reference to 01ZM is treated as an affine finite-coordinate approximation argument, not as a literal theorem asserting local DVR neighbourhoods. The proof is marked agent-written because its finite-spectrum refinement and coordinate assembly are written here. The older source annotation's normal-component removal is unnecessary: the principal-open argument handles the whole finite spectrum directly.

The existing blueprint.from.node is null, as tools/blueprint_refs.py ancestor confirms. Its inherited place names det-thm-sf-ctf-stability-direct-images (3), with the complete created.item chain already present. I preserved that provenance and read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is a supporting trait approximation below the unit, not a replacement of its direct-image route. No unit realization is claimed for this auxiliary node. The whole-blueprint searches for “strict henselization”, “generic point”, “local etale”, “etale trait” and the DAG tag/keyword searches found no equivalent blueprint statement.

### Mathlib searches

Read both fresh LeanFinder responses, the LeanSearch response, the Loogle result and the Mathlib grep result produced by msearch.py; exact queries and returned records are in searches.jsonl and appended to the item's mathlib_searches. The first LeanFinder query returned localization criteria for etaleness, etaleLocus, existence of an étale neighbourhood at an étale prime, residue-field maps, and Field.henselian. The second phrasing returned valuations, tilts, Hensel rings and the same étale-localization facts. LeanSearch also returned IsDiscreteValuationRing.exists_lift_of_le_one and localization of a Dedekind domain at a nonzero prime. None constructs a strict-henselization point over a finite-presentation local étale trait. Loogle with the Etale and IsDiscreteValuationRing names returned no hit, and the strictHensel/strict_hensel/henselization grep of RingTheory returned none. All services answered; no unavailable service is reported as a negative match. Inherited search records were retained rather than represented as N5 searches.

### Existing tools and dependency audit

Every cited statement was opened before use. The nonclosed tools from other units are explicitly declared in split_report.tool_uses: the pointed/triple presentation, the strict-henselization DVR theorem, small filteredness, the strict-henselization maximal-ideal identity, and the étale trait stalk theorem. They supply ring and local-ring interfaces not supplied by the constructible-stability unit. Other citations are definitions, existing Mathlib leaves, or Lean-closed results. No tool_uses maintainer field was set. I checked the statement/proof dependency closures of every cited node: none leads back to this item.

### Unfinished work

None in this one-level stage-1 split. The existing nonclosed dependencies remain their own work items. No new unsplit dependency is introduced.

## Not duplicates

No new nodes. In particular, the principal-open refinement is written as an elementary argument using the existing localization-spectrum statement; the coordinate descent is written as an elementary polynomial-quotient argument using the existing fraction-field extension statement. Neither was turned into a redundant node or a restatement of the item.

## Review by N5

I read the item's source in limits.tex, Tag 01ZM (lemma-descend-finite-presentation), including its explicit affine reduction. I also read algebra.tex Tag 04GW (lemma-strict-henselization-different), including filteredness and the two colimit presentations; Tags 00U1/00U2 (definition-etale, lemma-etale), especially principal localization, composition and base change; Tag 00U3 (lemma-etale-over-field); and Tag 00E3 (lemma-spec-localization). For the local rings I read more-algebra.tex Tags 0AP2 (lemma-Dedekind-etale-extension) and 0AP3 (lemma-henselization-dvr), together with Tag 07QM (lemma-dumb-properties-henselization). Finally I read the torsion-free flatness discussion around Tags 0539/0AUW and algebra.tex Tag 00HR (lemma-local-flat-ff). There are no new node statements to validate against sources.

1. The first step uses lem-sc-strict-henselization-triples-presentation for the given ring-colimit vertex, and the actual conclusion (3) of lem-weil-pbc-etale-local-ring-triples to identify the scheme and ring diagrams. The geometric point can be taken over an algebraic closure of the chosen separable residue closure; its relative separable closure is the chosen field. The two colimits agree by their universal properties, including their R-algebra structures. I checked that lem-sc-strict-henselization-dvr assumes a Noetherian base stalk, and justified this because a DVR is a PID; the closed-point stalk is R by the affine-stalk localization statement. This yields an actual domain D, an injective structural map, and a nonzero image of pi. It does not use the false implication that every flat map is injective.

2. The second step uses the finite affine cover in def-weil-finite-type-morphism, not the stronger unsupported assertion that an arbitrary affine open inherits finite generation. A map from a field spectrum factors through the chart containing its one image point. The affine-spectrum correspondence supplies the coordinate map. Choosing fractional representatives in D is the definition of Frac(D); no limit theorem is hidden in this step.

3. The small filtered category is exactly the one in lem-sc-pointed-etale-small-filtered, not the potentially large unrestricted neighbourhood category. def-sc-ring-strict-henselization supplies its colimit, and the existing elementwise commutative-ring-colimit theorem supplies representatives. Finite simultaneous lifting is a finite induction on filteredness. I expanded the residue-kernel argument: the colimit residue map kills m_R D=m_D by lem-sc-ring-strict-henselization-local-maximal-ideal, and its kernel is proper, hence equals m_D. This establishes q=ker(chi), contraction to the closed point, and a local map B_q to D. It does not assume that a coprojection B to D is injective.

4. I checked that the two fibres really exhaust Spec(B), using the local-domain dimension-one chain argument and lem-sc-dvr-dimension-one. The base-change node states étaleness of the actual tensor-product fibre, and the product-of-fields node applies to any étale algebra over a field, including the zero algebra. The fibre-ring definition and the general localization-spectrum embedding, together with the elementary quotient-prime correspondence, identify its primes with primes over the specified base prime. This is why the whole stage spectrum is finite; quasi-finiteness alone over an arbitrary base would not suffice.

5. The cited étale trait stalk node applies at a point over the closed point and gives a domain DVR and its uniformizer; it is not applied at a generic point, whose stalk would be a field. The affine-open-stalk node identifies the actual stalk with B_q and the actual map out of R. The formula h(b)/h(s) extends the given map because every denominator outside q maps to a unit of D. Its residue preimage is qA, so locality is proved rather than assumed.

6. I checked the elementary finite-product construction against Tag 00E3 and the exact general localization-spectrum node. For each prime not contained in q there is an element in that prime outside q; the finite product stays outside q. All remaining primes lie below q, so the principal localization is local. Since every element of B outside q is now a unit, its universal maps to and from B_q are inverse. This does not require normality, an idempotent component decomposition, or any assertion that an arbitrary prime localization is of finite presentation. Its argument is below 2000 characters and is a finite construction from the cited prime correspondence, not a hidden approximation theorem.

7. The existing principal-localization étale lemma states precisely both clauses needed: B_f is étale over R, and any affine étale algebra is finitely presented. I also checked the scheme convention, which requires quasi-separatedness as well as local finite presentation and quasi-compactness. The proof now explicitly supplies quasi-compactness of the map and its diagonal: their domains have finite underlying sets because A is a DVR. Thus finite presentation is proved in the stronger correct scheme sense; it is not inferred merely from a finite affine cover.

8. The kernel of A to D is prime because D is a domain. By the cited dimension-one fact for the local domain A there are only two possible primes. The nonzero image of pi excludes its maximal ideal, proving injectivity. This avoids assuming B to D is injective and also verifies that all descended denominators stay nonzero in A.

9. I checked both hypotheses of the torsion-free PID flatness node: A is a PID by the DVR definition, and D is torsion free because it is a domain containing A injectively. The local-flat-faithfully-flat node is applied only after flatness and locality are established. A definition of flatness alone is never used as a substitute for this theorem.

10. The fraction-field extension node provides an injection and its uniqueness, so the maps from K are compatible, not merely abstract field embeddings. The coordinate argument checks every polynomial in the presentation ideal using injectivity into F; it does not need finite generation of that ideal or any uncited finite-presentation limit descent. The resulting coordinate maps agree on K and the chosen generators, hence induce equality of the actual morphisms after pullback. This is the final v_A required by the original statement, not just a point with the same image.

I tested the empty coordinate list (choose a stage using filtered nonemptiness), V empty (there is no v, so no false existence follows), zero fibre algebras (their empty spectra contribute no primes), a stage already local (the product f may be 1), extra generic-only components (removed by the same finite product), several special-fibre primes (all other primes are removed), a nonhenselian DVR such as Z localized at a prime, and imperfect residue fields (finite separability occurs only in the étale-fibre tool; perfection is never used). All maintain the stated hypotheses. No properness or separatedness of V, excellence, integral R-to-A extension, or algebraic closedness of F was introduced.

I checked B–E of delivery-errors.md: no new statement-only nodes to misstate or duplicate; all uses are backed by verbatim statement quotes; the proof does not transfer its clauses into new nodes; and every localization, kernel, flatness and fraction-field argument carries its needed hypotheses. The longest step is below 2000 characters. The preliminary server review_split check passed. The required full dry run and push follow this written review.
