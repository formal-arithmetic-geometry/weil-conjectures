# Stage 1: lem-sfb-etale-relative-tor-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-relative-tor-comparison.json: statement, split into eight explicit steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-tensor-faithfully-flat-comparison.json: statement-only algebraic input, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-strict-henselization-tor-interval.json: statement-only algebraic input, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for each cited node at each step. Full statements are quoted to retain hypotheses and formulas, rather than paraphrasing the relevant assertion.

## Attachments

None. Searched lean/WeilConjectures for the item tag and relative Tor/etale comparisons; the Tor-amplitude source hits concern flat models, perfect complexes or Artinian residue-field tests, not this comparison for arbitrary complexes. No finished project declaration states the item or either new input.

## Literature wanted

None. All sources used are present in literature/stacks-project/.

## Findings and corrections

The live statement is unchanged. Stacks spaces-perfect.tex, Tag 0DK7 (lemma-tor-dimension-rel), states both the prescribed-interval equivalence and the local finite-dimension equivalence for arbitrary complexes. Its proof gives the stalk chain but leaves clause (2) formal. Steps 5–8 spell out the latter: exact localization and derived tensor restriction, Zariski-to-etale local bounds, then finite subcovers of each affine open and sheaf separatedness. This uses no global quasi-compactness or global uniform interval.

The interrupted attempt had already saved the split and two new nodes. I retained them and read the recorded search results; the first resumed dry run failed only because this report was missing. No prior delivery process was running. The sources and existing citations were audited before creating this report. Every non-elementary step is shorter than 2000 characters. The generic comparisons in Step 5 are existing node statements, not additional hidden lemmas. The two new nodes are algebraic inputs with no scheme/site comparison or local clause, so neither restates a clause of the item. They have no proof or proof dependencies.

The nearest-blueprint-ancestor command reports None. The item already inherits blueprint.from.node=null along a chain beginning with lem-sfb-proper-adjoint-diagonal-pair. I retained that provenance, its specific from.place and via chain; the new nodes prepend this item to via. The current blueprint proof read is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This auxiliary realizes a prerequisite in the inherited proper-flat-duality chain; no chapter or unit route is changed. Whole-blueprint searches for Tor amplitude, relative Tor, strict henselization, 0DJF and 0DK0 revealed no duplicate of either algebraic assertion. The unrelated relative Tor hit lem-pur-divisor-class concerns a divisor class, not a comparison of arbitrary module complexes.

## Mathlib search audit

Reused searches.jsonl from the interrupted attempt, reading its exact queries, success flags and returned declaration names. The new nodes each record LeanFinder, LeanSearch, Loogle and grep searches, including second phrasings. No service failure is represented as absence. For the coefficient-extension input, the closest hits Module.FaithfullyFlat.rTensor_reflects_exact (Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean:318), lTensor_reflects_exact (:362) and Module.Flat.iff_flat_tensorProduct (:601) concern ordinary modules and exact sequences. Read their source: none states the derived isomorphism over the unchanged base ring R or the arbitrary-complex Tor interval comparison. The tensor identities returned by the second derived-tensor phrasing are ordinary tensor algebra, not this derived assertion. For strict henselization, the hits HenselianLocalRing and Algebra.FormallyUnramified.flat_of_restrictScalars (Mathlib/RingTheory/Unramified/Finite.lean:275) concern henselian terminology and ordinary module flatness for an unramified algebra. They do not state the derived Tor equivalence over a strict henselization. Loogle's Tor combinations and grep for Tor/henselization or Tor/faithful-flatness found no derived comparison. The item searches returned small-etale topology and ordinary etale morphism declarations, without its Tor assertion. No Mathlib leaves are claimed.

## Not duplicates

No existing node has either new node's exact source tag/label in its source field. I searched the whole DAG by tag, by the source labels, and by statement concepts. The following nearby existing statements were opened and reused where applicable:

- lem-sfb-relative-tensor-faithfully-flat-comparison vs lem-sc-strict-henselization-faithfully-flat: the existing node says the ring map is faithfully flat; the new node gives the derived comparison and relative Tor detection for arbitrary coefficient algebras over a fixed R.
- lem-sfb-relative-tensor-faithfully-flat-comparison vs lem-trf-ringed-tor-amplitude-stalk-test: the existing node tests sheaf Tor amplitude on stalks; the new node compares two algebraic stalk complexes after faithfully flat coefficient extension.
- lem-sfb-strict-henselization-tor-interval vs lem-sc-strict-henselization-faithfully-flat: the new node compares Tor intervals for any complex already over the strict henselization, without requiring it to be extended from the smaller ring. Faithful flatness alone does not assert that reverse restriction-of-scalars implication.
- lem-sfb-strict-henselization-tor-interval vs lem-sfb-etale-zariski-module-geometric-stalk: the existing node identifies module stalks with scalar extensions; it contains no equivalence of Tor intervals over the two base rings.

## Review by NO

I read Stacks spaces-perfect.tex, Tag 0DK7, statement and proof, against the unchanged item. I read more-algebra.tex, Tag 0DJF (lemma-no-change-tor-amplitude), including its free-resolution total-tensor calculation, for the first new node: the comparison is stated in D(B), not only on cohomology, and does not require A or B flat over R. Flatness over A lets ordinary scalar extension compute derived extension. The total complexes in the source are identical under tensor associativity and direct-sum distribution; faithful flatness detects their cohomology vanishing. This is the mathematical justification of the new input's precise stronger derived formulation. I read flat.tex, Tag 0DK0 (lemma-tor-amplitude-up-down-henselization), clauses (1) and (3) and their proof, for the second new node. Applying the source to Spec(R) at its closed point gives exactly the stated local-ring form; its proof does not require L to descend, and has no finiteness or Noetherian assumptions.

For Step 1 I opened lem-weil-pbc-sets-inverse-image-stalk, lemma-openclosed-stalk-upperstar, lem-sfb-etale-zariski-module-geometric-stalk and lem-weil-pbc-strict-henselization-functoriality. The first gives the Zariski inverse-image stalk, the second the etale inverse-image stalk, the third the strict-henselization ring identification, and clause (4) of the fourth identifies the induced scalar map using pointed neighbourhoods. Naturality of the underlying-set comparisons with respect to ring operations makes these ring comparisons; no false assertion that R-sh to A-sh is flat is made.

For Step 2 the exactness-on-all-modules clause of lem-sfb-derived-etale-zariski-equivalence, not its quasi-coherent equivalence clause, is used. lem-weil-pbc-exact-functor-derived-factorization gives termwise realization for that exact functor. The geometric-stalk node explicitly treats every module without quasi-coherence and commutes with module morphisms, hence with the differentials. lem-sc-strict-henselization-faithfully-flat supplies A to A-sh faithful flatness. The exact-extension clause of the new coefficient comparison then identifies the actual derived stalk. These hypotheses hold for every local scheme ring.

For Step 3 I checked the two new statements: the strict-henselization input applies to an arbitrary R-sh complex, including L carrying its R-sh action through A-sh; the faithful-flat input is applied to R to A to A-sh and needs only the already-established faithful flatness of A to A-sh. Their equivalences preserve the same fixed integers a and b. Neither is a restatement of the site's Tor comparison.

For Step 4 I read both stalk tests. lem-trf-ringed-tor-amplitude-stalk-test allows any ringed space, so (X,f-inverse O-Y) is permitted. lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test allows an arbitrary ring sheaf, explicitly not just O-X, so it applies to f-et-inverse O-Y-et. No quasi-coherence, boundedness or quasi-compactness is required by either. The algebraic-closure existence clause and the geometric-point definition cited in that step supply a geometric point over every ordinary point.

For Step 5 I opened every restriction/comparison input. The open-immersion module-pullback statement identifies j-star with restriction; the etale inverse-image-restriction statement and the etale-site-localization statement identify the other side. The all-module clause of lem-trf-zariski-etale-functor-comparison-square applies to j and not merely to quasi-coherent modules. Exact-functor-derived-factorization extends it termwise. lem-pur-site-restriction-module-adjunction-exact applies to any ring sheaf and gives exactness of slice restriction. lem-weil-pbc-ringed-topoi-derived-tensor-pullback gives the isomorphism in the unbounded derived category for localization with restricted ring, not just a per-degree claim. lem-weil-pbc-exact-functor-complex-cohomology then identifies its cohomology. Composite inverse-image functors agree by their adjunctions; this explains restriction of the inverse-base ring rather than conflating it with the structure ring.

For Step 6 the small-etale-site definition supplies covering stability under base change. lem-sf-site-tor-interval-restriction applies to arbitrary ringed sites and arbitrary test modules on each slice; this is stronger than merely restricting one global test module. The relocalization clause of def-pur-localized-ringed-site identifies successive restrictions. Thus different Zariski neighbourhoods may carry different intervals.

For Step 7 I checked that etale-morphism-open-map provides open images, and the small-etale-site definition says the covering family is jointly surjective. Affine-scheme-qcqs together with the quasi-compactness definition gives a finite subcover of those images, without assuming the etale domains are quasi-compact. On a nonempty affine there is a nonempty finite family. Enlarging each interval to the finite minimum/maximum is an elementary consequence of the vanishing definition.

For Step 8 the three already-opened exact-restriction, derived-tensor-pullback and exact-cohomology statements give the displayed vanishing after restriction of any test module. Base changes of the finite cover cover each object by the etale-site definition. Sheaf separatedness makes a section whose restrictions vanish equal to zero; hence the cohomology sheaf is zero. Step 4 now gives a bound on that affine open. The affine-opens-basis statement supplies such neighbourhoods of every point. This supplies the argument the source calls formal, without using a missing local-to-global lemma.

I checked edge cases: X empty (zero module categories, vacuous stalk tests and interval [0,0]); the zero complex; a=b; R already strictly henselian; the field case R=k with R-sh a separable closure; and the identity coefficient extension A=B. I also checked nonflat base R to A (for example Z to F_p with B=A): the new coefficient comparison remains the identity, so no hidden R-flatness is permissible or used. In contrast B=0 over nonzero A is not faithfully flat, so it cannot spuriously detect a nonzero complex. The local proof takes finite subcovers only on affine opens and thus handles non-quasi-compact X and nonuniform local intervals. No statement dispute, unsupported purity route, SGA reference, compiler invocation, or new Lean file is involved.

## Unfinished work

The assigned one-level split is complete. The two new non-elementary inputs remain statement-only queue nodes as required; their downstream formalization and splitting belong to later items. Mechanical dry run and push are recorded by the delivery tool.
