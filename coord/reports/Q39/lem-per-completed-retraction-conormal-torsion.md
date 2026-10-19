# Worker report: lem-per-completed-retraction-conormal-torsion

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-completed-retraction-conormal-torsion.json: statement unchanged; four-step split of the completed-retraction argument. No Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-away-completed-cotangent-torsion.json: new statement-only unsplit input, Stacks 0ALQ(1), 0AJU(3), 0AJQ, 0AJP; not in Mathlib.
- dag/nodes/sec-deligne-laumon-a1/lem-per-completed-cotangent-transitivity.json: new statement-only unsplit input, Stacks 0ALM, 0AJR, 0GAE, 0AJP, 0AJQ; not in Mathlib.
- citations.json: one verbatim statement quotation for each cited node at each proof step.
- searches.jsonl: actual Mathlib searches executed through the required launcher command.
- report.md: this report and signed review.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures for the exact item id and completed-retraction, conormal, rig-etale, continuous-cotangent, completed-cotangent and adic-cotangent concepts. The only initial conormal hit was an unrelated deformation-to-the-normal-cone comment. No declaration states this item or either general completed-cotangent input. Upstream master sorry declarations were not used as finished proofs.

## WANTED

None. All mathematical source passages are available in literature/stacks-project/restricted.tex; tags were verified in literature/stacks-project/tags/tags.

## Findings and corrections

The imported statement is sound and unchanged. Its source is the existence paragraph for A=C in Tag 0AKJ (lemma-fully-faithful-etale-over-complement), ending before algebraization. The initial node had no proof. The important missing distinction was that S is only finite type over R. The existing finite-algebra completed-Jacobian node cannot supply the required input: its E is finite as an A-module, and its base A is complete. Neither condition is given for S/R. I added the general 0ALQ(1) input rather than assuming these hypotheses.

The cited transitivity theorem concerns completed naive cotangent complexes, not ordinary differentials of completed rings. Ordinary Mathlib Jacobi-Zariski does not specialize in one line: completing presentations and proving their comparison is additional mathematics. The new sequence explicitly uses H^-1 of the termwise tensor complex on its left, not the tensor of H^-1. No flatness of sigma is assumed or used.

The four proof steps are below 2000 characters each. The two elementary steps explicitly prove surjectivity/continuity and annihilation after tensoring and passing to a submodule. Neither a new node nor a citation hides those short arguments. No new node repeats a clause of the item: neither requires a retraction, and neither concludes anything about its kernel conormal.

Read the current chapter/unit records and the ancestor/via chain. This is a generic commutative-algebra input under the recorded Artin-Gabber/local-duality route; no chapter or unit statement or route is altered. The item is not a unit key node. No SGA source is used. All writes are inside the assigned sandbox; no Lean or compiler command, git command in a shared checkout, or local preflight/check_dag/review_split invocation was used.

## Not duplicates

- lem-per-etale-away-completed-cotangent-torsion vs lem-per-completed-etale-jacobian-torsion: the existing node assumes a complete base and an algebra finite as a module; the new input concerns completion of every finite type algebra over a possibly incomplete base, which is required here.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-jacobian-torsion-etale-shrink: the existing node is the reverse implication 0ALQ(2), shrinking an already torsion-completed presentation; the new node is 0ALQ(1), deriving torsion from etaleness away from the ideal.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-rig-etale-principal-reduction: the existing node constructs an intermediate principal-complete algebra from conditional algebraizations; the new node only obtains completed cotangent torsion from an etale-away finite type algebra.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-principal-jacobian-algebraization: the existing node algebraizes a principal-complete algebra assuming cotangent torsion; the new node establishes that torsion for a completion and does not algebraize.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-jacobian-torsion-closed-base-change: the existing node preserves assumed cotangent torsion under closed base change; the new node derives it from etaleness before any such base change.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-rig-etale-jacobian-algebraization: the existing node algebraizes an arbitrary completed presentation with assumed torsion; the new node derives torsion for the completion of a given finite type algebra.
- lem-per-etale-away-completed-cotangent-torsion vs lem-per-completed-retraction-conormal-torsion: the item concludes bounded torsion of a retraction kernel modulo its square; the new node has no retraction and only bounds cohomology of a completed polynomial presentation.
- lem-per-completed-cotangent-transitivity vs lem-per-completed-retraction-conormal-torsion: the item needs etaleness and a retraction and concludes conormal annihilation; the new node is a six-term sequence for arbitrary complete topologically finite type composable algebras.
- lem-per-completed-cotangent-transitivity vs lem-per-completed-etale-jacobian-torsion: the existing node bounds cotangent cohomology for a finite etale-away algebra; the new node asserts transitivity without etaleness or a torsion bound.
- lem-per-completed-cotangent-transitivity vs lem-per-jacobian-torsion-closed-base-change: the existing node is closed-base-change preservation of cotangent torsion; the new node is transitivity for a composable pair, with no torsion assumption.
- lem-per-completed-cotangent-transitivity vs lem-weil-pbc-jacobi-zariski-homology-sequence: the existing node uses ordinary polynomial presentations and ordinary cotangent modules; the new node uses restricted polynomial completions and their continuous derivative complexes.
- lem-per-completed-cotangent-transitivity vs lem-per-etale-away-completed-cotangent-torsion: the other new node establishes bounded cohomology torsion for an etale-away completion; transitivity has no etale-away or torsion condition.

The whole DAG was searched by 0ALQ, 0ALM, 0AJR, 0GAE and the completed/continuous cotangent, naive cotangent, Jacobian, and completion-differential concepts. Whole-blueprint searches through tools/blueprint_refs.py for conormal, rig-etale, cotangent, completion, Jacobian, transitivity, 0ALQ and 0ALM found no blueprint node stating either new input. The existing local-field continuous differential nodes require complete local algebras over coefficient fields; they do not state either new assertion over arbitrary Noetherian A and I. New ids were searched across the DAG and Lean source before creation.

## Review by Q39

I read restricted.tex at lemma-fully-faithful-etale-over-complement (0AKJ), especially the A=C reduction and the sentence invoking rig-etale and exact-sequence-NL. I also read lemma-rig-etale (0ALQ) including its proof, lemma-equivalent-with-artin (0AJU), the definition and presentation equation NL (0AJR), lemma-NL-up-to-homotopy (0GAE), lemma-exact-sequence-NL (0ALM) including the exact-row diagram and snake-lemma argument, and the full statements of lemma-topologically-finite-type (0AJP) and lemma-topologically-finite-type-Noetherian (0AJQ). The tags table matches these exact labels. Thus the first new node agrees with 0ALQ(1) and the cohomological condition of 0AJU, with the presentation/completeness supplied by 0AJP/0AJQ; the second new node states 0ALM with the presentation independence that 0GAE supplies, and introduces each ring, ideal and two-term complex explicitly.

For Step 1 I opened the actual statements of the new torsion node, def-weil-pbc-noetherian-ring and lem-weil-pbc-adic-completion-mod-ideal. They respectively give the bound and completeness/finite-type-reduction for B, finite generation of J, and completeness plus the same quotient for C. These are exactly what the step uses. The remaining quotient R/J is generated over itself by no variables. I read the finite-type, adic-completion, polynomial, spectrum and etale definition statements used by the item and new statements; they describe the notions asserted, rather than a theorem about a different notion.

Step 2 uses only the stated C-algebra condition: sigma composed with the structural map is the identity, which both proves surjectivity and fixes scalar compatibility. Continuity is checked on products generating each J^n, rather than assumed for arbitrary algebra homomorphisms with unrelated adic ideals.

For Step 3 I read the full new transitivity statement against 0ALM. B and C satisfy all its hypotheses by Step 1. Its Noetherianity assertion justifies its use of a completed B-polynomial presentation. The two zero-variable presentations are valid: R-completion is C by definition, B-completion is B by Step 1, and sigma is surjective by Step 2. Their kernels are 0 and K, respectively. The homotopy independence assertion is genuinely included in the cited statement, so the computation does not import a claim from its proof. Exactness at H^-1(C/B), with H^-1(C/R)=0, is precisely the injectivity asserted. The leftmost tensor-complex homology is irrelevant, so no unjustified flatness or commutation with kernels enters.

In Step 4 I read def-weil-pbc-module-tensor-product. Its balancing and generation by pure tensors prove that the same exponent c annihilates C tensor_B M. Injectivity and C-linearity then prove annihilation of K/K^2. I explicitly checked K acts trivially and that restricting the C-action agrees with the original R-action through R to B. Every cited statement is quoted verbatim in citations.json; there is one entry per (step,node), with no quote inferred from a proof. The item itself is not used by either new node, so these inputs introduce no backward dependency.

For small cases I checked J=0 (completion is the original ring and exponent 1 makes the assertion vacuous), J=R (both completions are the zero ring, so K/K^2=0), S=R and sigma=identity (zero conormal), and an empty/zero algebra whenever a retraction can exist. The general transitivity input also admits zero variables, identity maps and nonflat quotient maps. As a nontrivial torsion check, take R=k[t], J=(t), S=R[x]/(tx,x^2), sigma on completions given by x to 0. Away from t the algebra is R[1/t], hence etale; its conormal is k killed by t. This demonstrates why the conormal need not be zero and why a power-torsion conclusion is appropriate. For the finite-type distinction, S=R[x]/(tx^2-x) with R=k[t] is finite type and etale over D(t), admits x to 0, and is not finite over R: its x-generated summand is R[1/t]. Thus module-finiteness cannot be silently inserted.

All new nodes are statement-only, introduce every object, have definition dependencies, exact source tags/labels and completed blueprint fields, and have real search logs. I inspected Mathlib/RingTheory/Kaehler/JacobiZariski.lean, RingTheory/Etale/Locus.lean, RingTheory/Extension/Cotangent/Basic.lean and AdicCompletion/LocalRing.lean at the returned candidates. Their statements concern ordinary polynomial cotangent objects, ordinary etale loci, or the maximal-ideal cotangent map; none supplies completed presentation independence or the 0ALQ torsion theorem in one specialization. Both natural-language search phrasings for each new node were read, along with Loogle, LeanSearch and grep results. All services answered; no unrun query is recorded as a new search. I corrected the prospective misuse of the existing finite-module node before writing the split. No source error or disputed statement was found.

## Unfinished work

No part of this one-level split is intentionally unfinished. The two new general inputs remain unsplit for later workers, as required. Server dry run and direct delivery follow this review.
