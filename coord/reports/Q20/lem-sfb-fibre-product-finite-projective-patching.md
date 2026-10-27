# Stage-1 delivery: lem-sfb-fibre-product-finite-projective-patching

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibre-product-finite-projective-patching.json: statement unchanged; six-step proof of the equivalence, finite projectivity of its quasi-inverse, and specified unit and counit; status split.
- citations.json: verbatim statement quotes for every node cited in every numbered step.
- searches.jsonl: actual logged msearch.py searches retained.
- report.md: source review and delivery findings.

No new nodes; no new Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id and the module/fibre-product, patching, finite-projective and Milnor notions found no exact declaration. AffineDescentStageRealization concerns spreading retracts along filtered systems, not this patching equivalence.

## WANTED

None. All sources used are available in literature/stacks-project.

## What needed repair

The original item was unsplit and the sandbox had no previous item, split, report or searches. The statement agrees with Stacks 0D2J and is unchanged. Finite flat alone does not imply projective over an arbitrary ring: the proof explicitly constructs a finite presentation using its finite relation kernel. The component surjections split by projectivity, which proves their kernel base changes directly without an uncited flat-Tor theorem. The unit is proved only for finite projectives by retracting the finite-free case; the arbitrary-module unit need not be injective (Stacks 08IG).

The initial dry run found newly available exact DAG nodes lem-sfb-finite-module-fibre-product-patching and lem-sfb-flat-module-fibre-product-patching. I opened both statements and their dependencies and replaced the proposed nodes by these citations, deleting both proposed sandbox node files. The proof uses only the finite-generation clause and the flatness-of-patching clause, respectively. I also opened lem-sfb-relative-fp-module-fibre-product: it gives a more general relative finite-presentation theorem, but the item's short relation-kernel argument is retained following 0D2J, so that the essential assembly is actually proved here.

Blueprint ancestry reports from.node=None through blueprint_refs.py ancestor. I retained its null value, via list and detailed source place; same_as remains empty after whole-blueprint searches. I read the latest blueprint unit and the DAG chapter/unit records. This supporting algebra split does not replace any six-functor/alteration route, and the item is not the unit's key node. No unit realization file was edited.

## Unfinished work

None in this one-level split. The cited existing finite-generation and flatness nodes remain separately queued as their live states require. No Lean, compiler, Lake or build was run, no repository git command was run, and no files outside the sandbox were written.

## Not duplicates

No new nodes. The proposed finite-generation and flatness nodes were exact duplicates of newly available live nodes and have been removed. The live relative finite-presentation node is a general supporting theorem; the present item proves an equivalence of finite-projective categories with explicit quasi-inverse, unit and counit, so it is not a duplicate of that statement.

## Review by Q20

I read Stacks more-algebra.tex Situation 08KH (situation-module-over-fibre-product), 07RU (lemma-module-over-fibre-product), 0D2H (lemma-finite-module-over-fibre-product), 0D2I (lemma-flat-module-over-fibre-product), and 0D2J (lemma-finitely-presented-module-over-fibre-product), including their proofs. I also read Algebra 00NX (lemma-finite-projective), especially the split finite-free argument. The reused finite-generation statement is exactly 0D2H after renaming Stacks A' to A, A to F, and B' to R and reversing the gluing isomorphism. The reused flatness statement includes assertions (1) and (2) of 0D2I; the present proof uses only (1). Both introduce their own objects and tensor matching condition and supply the required hypotheses. No new nodes remain after reusing these live statements.

For step 1 I checked def-weil-pbc-projective-module states the lifting-along-surjections characterization. Lifting the identity splits a chosen finite-free surjection, and lifting on finitely many basis vectors proves the base-changed retract is projective. The cited tensor definition states compatibility with composition and identities, which preserves the retract equations. This is a written elementary calculation, not an uncited projective base-change theorem.

For step 2 I opened lem-sfb-patched-module-base-change: its statement really gives both projection maps as natural isomorphisms for arbitrary modules, not merely an isomorphism of abstract objects. Its gluing direction is the inverse of the item's alpha; the proof explicitly supplies this conversion. I opened lem-weil-pbc-tensor-over-quotient-ring and checked clause (1) gives F tensor M = M/IM with I = ker(A to F), since A to F is surjective. The compatibility over F is the very matching equation defining K.

For step 3 the reused finite-generation input applies because each component is finite. The existing Mathlib leaf lem-weil-pbc-projective-module-flat explicitly gives flatness of every projective module, supplying precisely the hypotheses for the reused flatness input. Expanding elements using the chosen generators proves the component maps q_A and q_B are surjective; no flatness of A or B as R-modules is assumed.

For step 4 I checked projectivity splits both component surjections. The image of 1-sq is exactly the kernel and its values on the finite basis generate that image. Tensoring the two inverse direct-sum maps proves the relation-kernel identifications without any Tor assertion. Equality of the common quotient maps on every basis vector follows from q(e_i) being a matching pair. The tensor definition cited here gives pure-tensor generation and the universal relations needed for all these identities. This elementary split-sequence argument replaces the source's more general flat-Tor invocation, so no missing theorem is hidden behind the word exactness.

For step 5 the coordinatewise fibre-product identity is checked in both directions; its restriction identifies ker(q) with the fibre product of H_A and H_B. Applying 0D2H to these finite relation modules is legitimate even though they need not have been proved projective. Finite generators of ker(q) give an actual finite-free presentation. I opened lem-weil-pbc-finitely-presented-flat-module-projective: it states exactly that a finitely presented flat module is finite projective, with no Noetherian hypothesis. Flatness was established in step 3.

For step 6 I verified the unit's inverse formula by both compositions using naturality and qs=1. On finite free modules the unit is precisely the coordinatewise ring fibre-product map. Naturality is checked on elements; the two triangle identities are checked on pure tensors and matching pairs. The tensor definition gives pure-tensor generation. I do not cite the false arbitrary-module unit isomorphism or extract any unexposed construction from a node's proof.

The two reused lemmas are genuinely smaller general inputs, not the item's equivalence or its unit/counit clauses. Step lengths are 609--831 characters, all below 2000. Every non-elementary ingredient is a cited statement; the elementary steps write out the splitting and coordinate arguments. The proof-dependency list is exactly the union of uses; citations.json copies the full statements verbatim. All non-Mathlib reused statements are in the same unit, so no off-route tool use is needed.

For edge cases I checked M=N=0, rank n=0, I=0 (A=F, hence R is B and K is N), F=0 (R=A times B and K=M direct sum N), and A=0 (forcing F=0, reducing to B). The reused flatness input permits infinite free modules. The reused finite-generation input permits torsion and nonflat modules. The proof uses no finite generation or nilpotence of I. For a concrete non-nil kernel, A=Z onto F=Z/2 with B=Z gives R the same-parity integer pairs and the compatible rank-one triple gives K=R. A nonsurjective second map is allowed, e.g. A=F=k(t), B=k: then R=k and the matching rank-one module is k. Conversely, omitting the first surjectivity would invalidate the applied source, so it is explicitly retained in each reused statement.

Search review: actual msearch logs are retained and queries copied unchanged. LeanFinder and LeanSearch returned Module.Finite.exists_comp_eq_id_of_projective, Module.finitePresentation_of_projective and Module.Flat.projective_of_finitePresentation, which concern already-projective/flat modules rather than patching. I read Finiteness/Projective.lean and FinitePresentation.lean around these results. For the flatness node I read Flat/Stability.lean's baseChange and Flat/Equalizer.lean's tensor-kernel results: the first extends scalars from an already-flat module, the latter needs flatness in advance and gives no glued module. For finite generation the finite-limit candidate in FGModuleCat/Limits.lean requires IsNoetherianRing and a single scalar ring; these hypotheses and objects do not match. Thus neither supporting fact is a one-line Mathlib specialization. No SGA source or alternate high-level route is used.
