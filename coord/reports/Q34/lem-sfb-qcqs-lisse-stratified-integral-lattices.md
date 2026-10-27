# Stage-1 report: lem-sfb-qcqs-lisse-stratified-integral-lattices

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-lisse-stratified-integral-lattices.json`: statement, split; seven proof steps using existing nodes; no Mathlib match.
- `citations.json`: verbatim statement excerpts for all 17 step citations.

No new nodes and no Mathlib leaves. `write_split.py` is a sandbox-only preparation helper; it is not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint id, lisse/lattice, integral lattice and stratified lattice. The rationalization theorem in `SixFunctors/ProEtale/Adic/PadicIntLatticeLisse.lean` proves that a specified integral tower rationalizes to a lisse sheaf, not the existence of embedded integral lattices on strata of an arbitrary qcqs scheme. It is not an attachment.

## Wanted literature

None. Sources read were the current blueprint rank/scheme/trace statements and proofs, its lisse finite-coefficient descent statement and proof, Stacks `etale-cohomology.tex` Tag 03S0 (`lemma-etale-stratified-finite`), and the existing DAG statements used below. The qcqs adaptation is marked agent-written because it combines these sources rather than copying a human-written theorem with precisely this conclusion.

## Corrections and scope

The item statement is retained. No statement dispute was found. The original item was statement-only; it is now split. Its finite-subextension-valued coefficient is not replaced by the all-continuous algebraic-closure coefficient. The already existing lisse finite-field model theorem supplies exactly the former convention.

The blueprint's trace detail assumes a Noetherian base and its parent invokes narrower stratification citations. These cannot be used verbatim for this item. Stacks Tag 03S0 applies to étale morphisms between qcqs schemes, and the trace-image and continuous lattice-sum nodes already have arbitrary-scheme hypotheses. The proof uses those precise statements and writes the assembly calculation. In particular no new node merely renames a clause of the item.

The chapter and unit records were read; neither is changed. The inherited unit is the compactification-coherence unit, so generic coefficient/lattice tools are declared in `split_report.tool_uses` with their purposes. They discharge its inherited closed-complement generator input without changing the unit's route.

## Mathlib and duplicate searches

Read the inherited Mathlib searches in the live item. Ran fresh authorized msearch queries (recorded in `searches.jsonl` and appended exactly in `mathlib_searches`) using LeanFinder twice, LeanSearch, Loogle and grep. All services returned; none was recorded as unavailable. The semantic hits concern regular functions on qcqs schemes, finite morphisms, quasicoherent local generators, or order lattices of submodules. Their printed signatures do not give integral lattices for lisse continuous-field coefficient modules. The second phrasing searched the trace/lattice-sum formulation. No exact or one-line-specialization match was returned.

Searched the whole DAG for `03S0`, `stratified-finite`, lattice sheaves, finite sums of lattices, trace images, and lisse finite coefficient descent; opened the candidate statements. Also ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `lattice`, `stratified integral`, and `03S0`. The lattice-scheme blueprint detail is already qcqs; the trace detail and other stratified-lattice theorems have Noetherian or finite-type hypotheses. None states this combined qcqs, finite-subextension-valued assertion. Its `same_as` therefore remains empty.

## Not duplicates

No new nodes were created. All reusable facts were found in the DAG and cited there.

## Review by Q34

I checked the seven steps against the open source texts and the statement of every cited node, rather than taking facts from their proofs. The central hypothesis check is that quasi-compactness and quasi-separatedness suffice throughout; I did not use a Noetherian induction argument.

1. `lem-sfb-lisse-finite-coefficient-model` explicitly quantifies over qcqs schemes and lisse internal modules, and explicitly uses the finite-subextension-valued algebraic-closure coefficient. Its conclusion gives both the lisse finite-field model and its scalar-extension isomorphism, including varying ranks and empty schemes. In the fixed-field case the model is the original module.
2. `det-lem-stratified-lattice-rank` states the clopen rank loci and their finiteness under quasi-compactness. The proof restricts to these loci; they remain qcqs because a clopen subspace is closed and its diagonal is a restriction of the original diagonal. This checks the hypotheses of the next lattice-scheme application, including rank zero.
3. `det-lem-stratified-lattice-scheme` states representability, separated étaleness, surjectivity, and the universal embedded lattice on a qcqs constant-rank base. It does not assert the representing scheme quasi-compact. I therefore use `lem-weil-pbc-etale-covering-sieve-finite-affine-refinement`, whose statement allows an arbitrary covering sieve and guarantees a finite jointly surjective affine family inside it. Membership in the generated sieve gives the required factorization to the representing scheme. I read its actual upstream proof in `AlgebraicGeometry/Sites/CohomologyColimit.lean:71`. The small étale site definition makes the singleton surjection a cover. `lem-weil-pbc-proetale-qcqs-finite-family-geometry` supplies finite scheme coproducts and qcqs affines. `lem-weil-pbc-continuous-locally-free-pullback` preserves freeness on the chosen maps, and `sk-prop-sfb-cartesian-coefficients` gives exact underlying inverse image and the coefficient identifications, so the embeddings remain embeddings. Assembly over disjoint components has no overlap condition.
4. Read Stacks Tag 03S0 in full, including its separated-case reduction and finite affine gluing argument. The cited `lem-weil-pbc-etale-stratified-finite` has precisely the qcqs source and target hypotheses verified in step 3, and its conclusion expressly gives constructible locally closed strata and finite étale base changes. The proof writes why surjectivity persists under base change rather than adding it to the cited conclusion. The two pullback nodes used in step 3 again apply to the stratum maps. No containment of images is mistaken for factorization through a subscheme.
5. `lem-sfb-embedded-lattice-coefficient-comparison` explicitly compares the pulled condensed coefficients, their inclusions, embedded lattices and rationalizations with continuous-function coefficients on any scheme. This prevents an implicit change of category. `lem-sfb-finite-etale-trace-image` supplies an actual trace morphism and its image equality on splitting covers. `lem-weil-pbc-finite-etale-etale-local-split` supplies those covers without a Noetherian hypothesis. Surjectivity ensures a nonempty sheet set whenever the splitting neighbourhood is nonempty; no trace-degree inverse is assumed.
6. `lem-weil-pbc-lattice-sheaf-locally-constant` identifies lattice pairs on a trivial rational module with a constant discrete sheaf. Finitely many sheet sections may therefore be made simultaneously constant locally. `lem-sfb-continuous-lattice-sum` states the equality of sheaf sums, local freeness and rationalization of the inclusion; this is stronger than an abstract finite-sum algebra lemma and is exactly what the image calculation needs. The embedded-lattice comparison transports these conclusions back to internal modules. This is why the narrower Noetherian trace-descent theorem is unnecessary. The source's finite-sum claim is used with a nonempty finite sheet set and any finite rank, including zero.
7. The last step is elementary assembly: the finite partitions lie inside clopen pieces; the scalar comparison is written explicitly with mutually inverse balanced-tensor maps. Empty base means the empty partition, and the coefficient field may still be the fixed finite field E; rank zero means the zero lattice. No assumption on dimension, characteristic, or invertibility of ell has entered any cited statement.

Every step is shorter than 2000 characters. All proof dependencies are the union of step uses; no definition is substituted for a needed theorem. I verified there is no dependency return path from any of these tools to the item. Every node citation has an exact substring from its statement in `citations.json` (complete statements are used where several clauses are required). I checked B1–B10, C1–C8, D1–D5 and E1–E7: no new-node self-containment/notation/tag issue arises, searches are real and logged, tools are declared, the proof is a construction rather than relabeling, and the Noetherian/coefficient-category traps have been removed.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own independent stage states.
