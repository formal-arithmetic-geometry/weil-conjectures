# Q50 — lem-per-trait-log-smooth-uniformizer-chart

## Files written

All JSON files are under dag/nodes/sec-deligne-laumon-a1/ in the sandbox.

- lem-per-trait-log-smooth-uniformizer-chart.json: statement unchanged; four-step split following ILO XVI 3.6.3, with an explicit finite torsion calculation.
- lem-per-log-smooth-differential-generators.json: statement-only lemma; no Mathlib match. Gives differential generators, torsion-free characteristic group, finite prime-to-characteristic cokernel modulo units, and divisible units.
- lem-per-divisible-unit-lattice-extension.json: statement-only lemma; no Mathlib match. Precisely ILO XVI 3.6.4, with its finite-free lattice conclusion.
- lem-per-kato-lattice-chart-realization.json: statement-only lemma; no Mathlib match. The inverse-image construction for a prescribed lattice and differential basis, rather than the existential trait chart assertion.
- citations.json: one verbatim statement excerpt for each use in each proof step.

## Attachments

None. Searched the project Lean source for the item id, logarithmic structures, log smoothness, and uniformizer charts. No project declaration states the item or any new child. Ordinary uniformizer statements and ordinary smooth morphisms do not attach these logarithmic assertions. The upstream master checkout is reference material only.

## Wanted literature

WANTED: K. Kato, Logarithmic structures of Fontaine–Illusie (1988), Theorems 3.5 and 3.12 and Lemma 2.10, for the underlying log differential and chart-realization arguments of lem-per-log-smooth-differential-generators and lem-per-kato-lattice-chart-realization. These are recalled in the locally present ILO XVI 3.6.3 and X 1.2, which are the sources actually read and followed here; no missing document was downloaded or falsely claimed read.

## Corrections and scope

The item's statement is correct and unchanged, including points over the generic point, its fixed uniformizer, and its etale conclusion. The stronger chart is not just the definition of log smoothness. The split extracts the two local geometric inputs and the independent lattice lemma used in the actual ILO proof. The item still proves the injection, torsion-free group completion, finite invertible torsion, and specialization to the given trait. None of the new nodes simply repeats a clause with the item's hypotheses: the realization lemma takes prescribed lattice/differential data that the preceding steps must construct, and does not establish the invertible cokernel condition.

ILO XVI 3.6.3's discussion of the finite cokernel is read modulo units, as confirmed explicitly in X 1.2, p.137. A finite cokernel of the map into the full log group, without quotienting by units, would generally be wrong. The new generator statement spells out the quotient and avoids that inference.

No route change, Lean writing, compiler, Lake command, live project edit, launcher edit, or agent launch occurred. The inherited chapter/unit and all import metadata were retained. This item is not the unit's key proposition, so no unit realization record is changed. No non-elementary step exceeds 2000 characters (lengths 868, 546, 928; the elementary final calculation is 1335).

## Mathlib and duplicate searches

Every new node was searched using the supplied msearch.py, with LeanFinder, LeanSearch, Loogle, and source grep, followed by another semantic phrasing. The queries and returned results are in searches.jsonl and search-results.txt and copied with their actual query text into the child JSON. All services returned successfully. The item also has four fresh searches. Existing inherited search records were retained as required, without representing them as searches run by Q50.

Read every returned type. The logarithmic searches return ordinary standard smoothness, ordinary Kahler differentials, ordinary etale coordinates, field logarithmic derivatives, or number-field unit lattices. The lattice searches return ModN and quotient constructions, free finitely generated modules, and injectivity of fully divisible groups. Module.Baer.of_divisible and extension_property_addMonoidHom assume divisibility by every integer, not divisibility by the single integer n; neither gives the finite-index free lattice extension in one line. No new node qualifies as a Mathlib leaf.

Searched the whole DAG by logarithmic differential, lattice extension, Kato, log smooth, 3.6.3, 3.6.4, and n-divisible, and searched the whole blueprint using blueprint_refs.py search for chart, differential, logarithmic differential, log smooth, divisible, n-divisible, lattice, and free abelian. The ancestor command gives lem-per-artin-gabber-affine-curve. Existing sharp-chart and stalk-spreading nodes do not give relative etaleness for a prescribed base chart, and the free-chart-factorization node assumes torsion-free cokernel rather than constructing finite-index extensions. No equal blueprint statement was found; same_as is [] and every new from.place specifies the internal ILO argument with its inherited ancestor context.

## Not duplicates

lem-per-log-smooth-differential-generators vs def-per-fs-log-smooth-etale: the latter defines a chart condition; it does not prove local freeness of log differentials or the finite characteristic cokernel statement.
lem-per-log-smooth-differential-generators vs lem-per-trait-log-smooth-uniformizer-chart: differential generators and divisible units are inputs to construction, not any existential chart clause.
lem-per-divisible-unit-lattice-extension vs lem-trf-fg-torsionfree-group-free: freeness alone neither enlarges a prescribed lattice nor extends a map through a subgroup that is only n-divisible.
lem-per-divisible-unit-lattice-extension vs lem-trf-fs-chart-free-factorization: the latter factors an already injective monoid chart with torsion-free cokernel; this is a group extension lemma without chart hypotheses and permits finite n-primary index.
lem-per-kato-lattice-chart-realization vs lem-trf-fine-log-stalk-chart-spreading: spreading assumes a stalk chart isomorphism and does not prove that the inverse-image monoid is a chart or that the relative comparison is etale.
lem-per-kato-lattice-chart-realization vs lem-trf-log-regular-sharp-chart: the latter assumes log regularity and realizes a sharp characteristic monoid, with no prescribed relative base chart or etale comparison.
lem-per-kato-lattice-chart-realization vs lem-per-trait-log-smooth-uniformizer-chart: the former realizes a prescribed inverse-image monoid from additional finite-index lattice and differential-basis data; constructing that data and proving the trait's finite invertible torsion conclusion remain in the item's proof.
lem-per-kato-lattice-chart-realization vs lem-per-regular-log-smooth-monomial-chart: the latter assumes regularity and produces a free monomial hypersurface form over a trait, a further downstream refinement; it is not used here.

## Review by Q50

I read ILO XVI Definition 3.6.1, Proposition 3.6.3 and its proof, Lemma 3.6.4 and its proof, and the adjacent Proposition 3.6.5 on printed pp.252–253. I also read X Proposition 1.2 and the proof on pp.136–138 to check the quotient by units, divisibility and relative differential argument. No SGA source is used. I read the chapter and unit records and the current blueprint ancestor's proof: the inherited purity/log-alteration input serves the local regular-purity part of its Step 3, rather than changing Fourier exactness at unit level.

Step 1 uses precisely the differential-generator node: its statement supplies finite torsion-free C, the t_i basis, an invertible n, n-divisible units and finite cokernel modulo units. Q=N is fs with free group completion by the explicit elementary check, and the trait is locally Noetherian. I checked that the lemma is applied at a geometric stalk, where units are n-divisible; ordinary local rings would not suffice.

Step 2 uses precisely the lattice-extension node. Its hypotheses are all available: L=Z^(r+1) is finite free, D is a subgroup of B, C=B/D is torsion-free, and its cokernel is finite killed by the same n. The conclusion does not assume the full log group is finitely generated. The kernel of L->B is allowed, as in the source lemma.

Step 3 uses precisely the prescribed-lattice realization node. The fixed chart, log smoothness, differential basis, invertible n, injection i, n-power-killed quotient and surjectivity of h modulo units all match that node's statement. It gives P^gp=G, fs P, compatibility with the same base chart, and an etale comparison on an actual pointed neighbourhood. I did not take those facts from a definition or from an unquoted proof of another node. Freeness of G then proves torsion-freeness and i proves injectivity in the item's text.

Step 4 is an explicit group calculation, not an unstated structure theorem: torsion classes in G/Zw are the rational multiples of w in G, embedded in (1/|w_j| Z)/Z, hence finite cyclic. The n-power bound follows by projecting i(Z^r+Z) onto its Z^r component and cancelling a nonzero integer. A cyclic group killed by n^a has order dividing n^a, so the displayed inverse proves its order invertible. The stalk-colimit definition is cited with the part that represents the inverse of n on an etale neighbourhood; the final sentence of def-sbc-smooth-morphisms explicitly identifies etale morphisms with smooth morphisms of relative dimension zero. The citations file was corrected to quote the colimit part, rather than merely the definition of a pointed neighbourhood.

For the child statements I tested rank zero, n=1, trivial characteristic group, and noninjective L->B. In the lattice lemma the zero cokernel permits G=L, and torsion-free B/D is necessary in the finite-index construction. In the realization lemma r=0 and a unit base monomial are allowed: P may have a nontrivial unit subgroup, so the chart is not incorrectly required sharp. For the item a point over the generic point has pi invertible, but the retained Z factor maps into the unit subgroup of P; the map N->P can still be injective. I checked the chart refinement requires no regularity of V, unlike the downstream monomial-chart theorem.

I checked delivery-errors B–E: new nodes are statement-only and self-contained (log differential notation is defined inline), notions have definition dependencies, TeX is singly escaped, sources identify the actual ILO propositions rather than inventing Stacks tags, real searches are recorded, no exact Lean attachment is available, and blueprint ancestry is filled. Every cited node was opened and read, quotes are verbatim, no proof-only construction is cited, and the server check_dag found no introduced cycle. The three children isolate substantive inputs rather than elementary steps or the whole conclusion. All hypotheses and generic/rank-zero cases above were checked against the source. No unresolved mathematical point remains for this one-level split.

## Validation

Server check_dag: OK, no finding introduced by the sandbox or on its nodes.
Server review_split: PASS. It reports zero new nodes in that invocation because it reviews the supplied item rather than the final delivery commit; the required complete-delivery dry run is next.

First full dry run exited with one gate finding: the lattice child cited no definition node. Repaired by explicitly identifying its finite free abelian group as a finite free Z-module and citing the existing def-weil-pbc-free-module, whose basis/free-module statement I opened and read. Updated the verbatim Step 2 quotation. No mathematical assertion changed.
