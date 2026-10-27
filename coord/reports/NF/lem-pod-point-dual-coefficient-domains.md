# NF stage-1 report: lem-pod-point-dual-coefficient-domains

## Files written

- dag/nodes/sec-six-functors/lem-pod-point-dual-coefficient-domains.json: existing statement, now split into seven proof steps; statement unchanged; not a Mathlib leaf.
- citations.json: 30 literal statement excerpts, one for each step/node citation.
- report.md, searches.jsonl and sandbox-only preparation scripts: review and search evidence.

New nodes: 0. New Mathlib leaves: 0. The needed smaller results already exist. No Lean, compiler, Lake, repository write or direct git command was used.

## Attachments

None. I searched all lean/WeilConjectures for the blueprint id and point/sections/duality/coefficient terminology and read the nearest relevant declaration, AlgebraicGeometry.Etale.pointSectionsDerivedBaseChangeIso, PointFiberAlgClosed.lean:96. It assumes a flat ring homomorphism, concerns small-etale derived base change and does not supply this item's unbounded nonflat quotient assertion, its completed pro-etale coefficient stages, and all dual domains together. It is not an attachment for this item.

## WANTED

None. The item source and the supporting Stacks source are available locally. For point definitions and operation reduction the current snapshot places the files in sec-six-functors-basics, rather than their old sec-smooth-purity paths; I located and read those current files as well as the live node statements.

## Problems found and repairs

The imported item had a complete statement but no proof. No STATEMENT-DISPUTED issue was found and the statement remains byte-for-byte equal to the live statement. In particular I retained the unbounded ambient finite-reduction clause and did not add flatness or finite Tor dimension of the quotient. The blueprint's brief compatibility discussion is source material, not a proof of these domain and normalization claims.

I expanded finite reduction using the actual ringed-point evaluation comparison, and explicitly retained the target A_{E,m} action. An isomorphism merely in D(A_{E,n}) is insufficient to identify a D(A_{E,m}) arrow; Step 1 constructs the scalar comparison with that action, then detects its invertibility by its cohomology after exact restriction. I separated this ambient argument from finite-Tor membership, where bounded free models genuinely are available.

In a preliminary draft I almost cited def-weil-derived-pullback-tensor-hom for an adjunction theorem. Its live statement only defines the operations. I corrected Step 7 to cite the actual canonical internal-Hom coefficient comparison and evaluation compatibility in thm-sf-ctf-stability (vii) and lem-fix-operation-reduction. No conclusion uses a definition as proof of an adjunction theorem. I also did not infer finite-Tor preservation of a quotient merely from a definition: Step 4 uses finite free point realization and the actual reconstruction counit.

## Not duplicates

No new nodes were created, hence there are no new/existing same-tag pairs to distinguish. Whole-DAG and blueprint searches for point duality, finite Tor, coefficient passage, sections comparisons and dual domains were read. The relevant content is already in lem-sf-point-ringed-evaluation-model, lem-sf-point-tor-amplitude-realization, lem-pod-point-sections-reconstruction, the integral comparison nodes and thm-sf-ctf-stability. The item's parent lem-pod-point-duality-coefficient-compatibility and sibling lem-pod-point-dual-evaluation-transport depend on this item and are deliberately not cited.

## Review by NF

I read the item source thm-pod-global-verdier-duality.proof.md in main-20261015, including the paragraph identifying point duality and the subsequent coefficient-compatibility argument. I also read the point-dualizing proof, the point-perfectness proof's finite-model argument, the current point coefficient definition and operation-reduction statement, the chapter and unit records, SETUP's three levels, and delivery-errors B--E in both copies of that document. For the ambient derived comparison I read sites-cohomology.tex, Tags 07A4 (lemma-pullback-tensor-product), 0G7E (lemma-pullback-K-flat) and 06YY (lemma-derived-base-change). The detailed point application is marked agent-written, not attributed verbatim to Stacks. There are no new node sources to certify.

For Step 1 I opened all five cited statements. The evaluation model supplies the identity ring-map point, exact sections, its K-flat preservation, its actual ring values and scalar square. The general ringed tensor lemma permits arbitrary unbounded inputs. The resolution and derived change-of-rings lemmas compute scalar change in the target coefficient category, and the cohomology criterion detects the scalar map's invertibility there. The target scalar action is carried by the balanced sections rule. This does not require the quotient itself to be K-flat. The sites and modules are taken in the project's fixed small skeleton/universe, so no unrestricted large indexing category is introduced.

For Step 2 I read the exact formulas in the integral reduction and sections scalar-extension nodes: the former is an isomorphism in D(A_{E,n}), and the latter is phi inverse including the actual chi completion map. Their inputs are bounded constructible integral complexes, which our finite-Tor integral inputs are. For Step 3 I checked the rationalization formula and the common-stage representative rule in def-weil-finite-coefficient-point, and the identity/tower equations in the scalar-extension statement. The tower equality, rather than an unspecified transport, makes enlargements agree. The tensor theorem explicitly states reduction/scalar compatibility, and the ringed evaluation statement supplies the scalar square. These are the prescribed maps, not freely chosen isomorphisms.

For Step 4 I read the finite-free-model assertion with the exact Tor interval in lem-sf-point-tor-amplitude-realization. The reconstruction node assumes exact extension/sections and their explicit adjunction; these hypotheses are separately supplied by lem-pod-point-exact-extension-sections. Its counit then identifies C with the actual constant finite-free model. Coefficient change reduces each finite matrix, so the target model is bounded and free over the target sheaf ring. The bounded-above flat-to-K-flat criterion is explicitly cited from lem-pc-bounded-above-flat-kflat-site, which applies to arbitrary sites; I checked that the similar lem-kun-kflat-criteria is only stated for the small etale site and did not cite that version for this pro-etale argument. The unit's constructibility and the finite-Tor triangulated closure are separately cited. This is a short assembly of existing results, not a new lemma hidden behind a perfectness assertion.

For Step 5 I checked the integral category's required bounded constructible reductions and the finite-Tor definition's uniform Tor bounds; these are different conditions and both are used. Integral scalar extension is completed and has its own constructibility theorem. The stability theorem supplies integral Dbc=Dctf. Rationalization and field extension are already typed as bounded-constructible functors by their definitions, and finite Tor is the stated field-stage definition. Common-stage objects are represented over an actual finite field, with no Karoubi completion introduced.

For Step 6 I read the duality preservation assertions of thm-sf-ctf-stability at finite, integral and field stages. The scheme s is a separated finite-type k-scheme; the relevant structure map is the identity. This supplies membership of D_sC and D_sQ_sC, and the preceding coefficient arguments also apply to D_sC. The point dualizing node identifies precisely this identity-adjunction dual with the coefficient dual. I checked no cited input reaches this item by following all statement and proof dependencies.

For Step 7 I checked the unit, tensor, internal-Hom and evaluation comparison statements, including the finite-Tor domains in thm-sf-ctf-stability (vii). The dualizing comparison is written explicitly as u_target inverse, coefficient-unit comparison and Q(u_source). Its normalization equality follows by cancellation. Composing the canonical internal-Hom coefficient comparison with RHom(1,w_Q) gives exactly the evaluation transpose in the item's statement. The proof only needs this arrow to be defined; it does not promote an unspecified objectwise identification into the required normalized arrow.

Small cases checked: C=0; the coefficient unit; a shifted rank-one free complex; n=m (unit coefficient comparison); n=1; integral torsion complexes represented by a two-term free complex; identity field extension; and E subset L subset M with the specified associators. For the genuinely nonflat case A=Z/ell^2 to A'=Z/ell and B=A'[0], the unbounded ambient comparison remains valid although the resulting derived tensor has infinitely many nonzero Tor groups. This confirms the ambient claim does not silently assume the conclusion is bounded. B is not used as a finite-Tor input in Steps 4--6. For finite free P, reduction preserves its support interval even for this nonflat map. The signed Hom/evaluation conventions are inherited from the specified comparisons and never altered.

Against B: no new unsplit statement contains a proof, no new definition is introduced, and the inherited statement/TeX/blueprint ancestry is preserved. Against C: every non-elementary input is an existing cited statement, with a literal excerpt in citations.json; no cited proof internals are used; dependencies have no path back to this item. Against D: the item contains the assembly argument and no new node merely restates a clause. Against E: the coefficient ring, target action, exact category and completed versus ordinary tensors are tracked separately, the nonflat edge case is retained, and no hypotheses are added. All seven steps are under 2000 characters, and I found no further reusable lemma to extract. Off-unit generic tools are declared for reviewer judgment in split_report.tool_uses; the geometric unit route and all human-fixed statements are unchanged.

## Mathlib searches

The inherited searches remain in the node. Six fresh searches were run with the required msearch command: LeanFinder twice, Loogle, LeanSearch and two source grep patterns, all recorded exactly in searches.jsonl and appended to mathlib_searches. All services answered. The results concerned ordinary monoidal/condensed structures, module functor linearity, scheme structure-sheaf sections, cotangent exactness and tensor products on prime spectra; none states the full point coefficient comparison and domains or a one-line generalization of it. No new leaf is claimed.

## Unfinished work

None in the one-level stage-1 split. Its cited unsplit nodes remain independent future items. The first dry run exited successfully at 624296b081c. I then added the explicit general-site bounded-flat K-flat criterion in Step 4 as a citation improvement; final dry run and direct push follow this review.
