# Worker report: lem-per-ctf-hom-locally-constant

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-ctf-hom-locally-constant.json`: split statement, eight proof steps; statement unchanged; not in Mathlib.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-galois-partition-tensor-closure.json`: one new statement-only unsplit node, ordinary tensor closure of a fixed Galois-partition class; no Mathlib match.
- `citations.json`: verbatim statement quotations for every citation of every item step. The complete quoted statements include the hypotheses as well as the clauses being used.

## Attachments

None. Searched the project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, Galois constructibility, weak constructibility, ind-unipotence and local/internal Hom terminology. No project declaration states the item. The upstream master reference search supplies no attachment; its sorry declarations are not completed proofs.

## WANTED

None. I read the local ILO PDF and local Stacks TeX. No downloads or Lean commands were needed.

## Corrections and proof route

The sandbox initially had only a search log and dispatcher brief markers, with no saved node, report or delivery process. I retained the recorded search, read its returned names, copied the current unsplit item, and appended actual searches. The item retains its earlier repository searches too. New-node searches are exactly queries in searches.jsonl, including the honest zero-hit unknown-identifier Loogle query. The later valid Representation.tprod query returns representation tensor infrastructure, not the required closure theorem. Two semantic phrasings, LeanSearch and source grep were also read; none provides a Mathlib leaf.

ILO XVII Lemma 7.6.11, printed p. 314 (PDF page 320), proves the locally constant flat case by exact local Hom and a common Galois cover. I read Definition 7.6.8 and Proposition 7.6.9 as well. The item's explicit warning about infinite finitely generated stalks prevents assuming one global finite etale trivialization. I preserve this warning and use the existing `lem-per-noetherian-ctf-flat-model`, specialized to Tor amplitude [0,0], to obtain a stratified trivialization. ILO XVII Exercise 7.2.7, p. 303, is the relevant distinction between etale-local constancy and the finite-cover local-system notion. No statement correction or additional dualizing hypothesis is made.

I also corrected the owned blueprint.from.place: the current main-20261015 ancestor proof discusses duality in Step 3, whereas the inherited pointer named Step 1 of an older proof. The ancestor id and via chain are retained. Read its current statement/proof and the chapter and unit records; this is an auxiliary coefficient-duality argument below the perverse unit, not a replacement of its Fourier route.

## Not duplicates

lem-per-galois-partition-tensor-closure vs lem-per-galois-partition-exact-refinement: the existing node gives an exact abelian inclusion, extension/filtered-colimit closure and common refinement; it does not assert tensor closure. An exact abelian inclusion alone does not justify closure under arbitrary ambient subquotients, so I do not use that shortcut.

lem-per-galois-partition-tensor-closure vs lem-per-constructible-finite-monodromy-filtration: that node supplies geometric extension-by-zero filtrations for constructible finite-type sheaves; the new node concerns ordinary tensor products of two arbitrary-size weakly constructible sheaves for one fixed partition.

lem-per-galois-partition-tensor-closure vs lem-per-ctf-hom-locally-constant: the new statement has two arbitrary module-sheaf factors, neither flat nor finite type, and no derived Hom or amplitude assertion. Steps 1-5 and 8 carry the item's Hom argument. Only Step 6 uses the new tensor result.

Searched all DAG nodes for ind-unipotent, FCons, weak constructibility and Galois partitions, and the entire imported blueprint with blueprint_refs.py searches for Galois partition, weakly constructible, ind-unipotent, unipotent, locally constant and finite projective. The only unipotent blueprint hit is a finite-field Sylow trace filtration, not tensor closure. same_as is empty. No source Stacks tag is shared by the new node: its source is the ILO local-system/ind-unipotent description, not a purported Stacks tensor theorem.

## Review by Q18

I read ILO XVII 7.2.1-7.2.7, 7.3.1-7.3.8, 7.6.8-7.6.11, and 11.2.1/11.3.1-11.3.4 at printed pp. 301-305, 313-314, 328-330. For the new tensor node, the source provides the equivalence with discrete continuous fundamental-group modules and the ind-unipotent criterion. Tensor closure is a consequence, not a theorem printed verbatim there: use the convolution filtration of tensor products of unipotent modules, with its graded pieces quotients of tensors of trivial graded pieces, then commute tensor with filtered colimits. No flatness is needed for that representation calculation. Proving that it applies to the sheaf class requires the local-system equivalence, its tensor compatibility and the torsion extension theorem; those are not supplied by the existing exact-refinement statement. I left this genuine auxiliary theorem unsplit, with no proof hidden in its statement, rather than using it uncited in the item.

I opened the statement of every cited node and compared each use:

1. Exact-functor cohomology gives acyclic preservation for F tensor, so F[0] is K-flat by the cited derived-tensor definition. The flat-model node explicitly supplies a representative in the *same* [0,0] interval and a simultaneous connected reduced Galois stratification with finite projective values. Taking H^0 identifies its sole term with F. Its hypotheses are exactly the same Noetherian X, Noetherian F_l-algebra A and ordinary etale coefficient category; no finite ring or finite-type-over-a-field assumption is imported.
2. The local-finite-type definition gives arbitrary etale constant charts. The geometric-stalk definition and exact constant-coefficient inverse image identify a chart value with a fibre of the stratified trivialization. Thus each nonempty chart's module is projective. This is only a fibre comparison, not a claim that the strata form an etale covering.
3. The sheaf-Hom definition gives the retraction h -> hp, f -> fi. I wrote its image idempotent and explained exactness by applying the idempotent to a local lift. The finite-projective evaluation node gives the canonical tensor-dual comparison, and the coversTop node detects local isomorphisms and zero homology. Stacks 08DQ/08DM are the finite-summand calculation; I read 08JI and 08JJ as checks but do not cite their stronger conclusions unnecessarily. Stacks 03P5's constant-sheaf-sections node makes the matrix image constant by the pointwise calculation now written in the step.
4. The inverse-image node states exactness, additivity and constant coefficient identification for every scheme morphism, not just etale ones. Its finite-image calculation proves the needed Hom pullback comparison for our locally finite-projective source. This avoids citing the finite-ring-only pullback-Hom theorem for our possibly infinite A. Applying it to the covers of Q shows D is actually constant there.
5. The derived-Hom definition gives Hom(F,I) for a K-injective target; the exact-functor cohomology node says T sends quasi-isomorphisms to quasi-isomorphisms and computes the displayed cohomology. I checked that this uses exact *internal* Hom, not exact global Hom. The bound is [u,v], with no dimension restriction.
6. The exact-refinement node explicitly gives inclusions of both weakly constructible classes into a common one for every coefficient algebra. I use exactly these inclusions, and the new tensor node applies to D and H^qN in that one class. I do not read geometric factorization of covers into the refinement statement.
7. Degree vanishing, boundedness and independence of N,u,v are immediate from Steps 5-6. This is the only step marked elementary. The refinement was fixed using F and P; there is no dualizing complex anywhere.
8. On each finite constructibility stratum of a cohomology sheaf of N, the earlier pullback calculation and finite-projective evaluation identify the local Hom value with Hom_A(M,B). It is a retract of B^r and hence finitely generated. The local-finite-type and stratification definitions then give the exact constructibility assertion, including arbitrary infinite coefficient rings.

I checked Stacks source labels for 010N (homology lemma-exact-functor), 03EL/03EO (sites-modules tensor-product-pullback/internal-hom-adjoint-tensor), 08JI/08JJ (sites-cohomology finite-summand Hom/perfect dual) and the constant-sheaf calculation. Citations use only actual statements; definitions are never used as substitutes for a vanishing or comparison theorem. Off-unit uses are declared generic locality, inverse-image, finite-projective evaluation, constant-section and cohomology tools in split_report.tool_uses.

Small cases: X empty; F=0; F=A_X; a nonfree projective coefficient module, for instance an idempotent summand over F_l x F_l; an unbounded-size weakly constructible sheaf; and u=v. The bounds give zero, identity, or the corresponding finite-summand functor as expected. For the new lemma I checked zero factors, the identity partition and two nonflat constant factors A/(t) over A=F_l[t]: ordinary tensor still lies in the class, while a derived-tensor assertion would introduce extra Tor and is deliberately not asserted. The tensor filtration in the report uses images in representations and does not assume flat graded pieces.

B1-B9: the new node is self-contained, statement-only, all notions are defined inline or have their definition dependencies, single TeX escaping, and all actual search records and blueprint ancestry are present. C1-C8: every non-elementary step cites its used statements, proof_deps is their union, and no node restates a clause as its whole argument. D1-D5 and E1-E6 were checked against the local models and actual ring/site hypotheses above. All eight proof steps have fewer than 2000 characters. The principal repairs during self-review were making the constant-image argument explicit, distinguishing class refinement from cover domination, and correcting the old blueprint step pointer. No live repository, launcher or Lean file was written; only the sandbox is changed. The required server dry run is the validation gate before direct delivery.

## Unfinished work

No part of this one-level split is omitted. The one new auxiliary theorem is intentionally unsplit, as the stage-1 brief requires; it is not a claimed Mathlib leaf or finished Lean proof.
