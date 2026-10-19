# Repair report: thm-trf-integral-adic-coefficient-morphism-trace-formula

## Files written

- `dag/nodes/sec-trace-formula/thm-trf-integral-adic-coefficient-morphism-trace-formula.json`: split statement; eight steps. The statement and Lean record are unchanged, and original steps 1–4 are byte-identical to the repository copy.
- `dag/nodes/sec-trace-formula/lem-trf-lattice-reduction-tower-normalized.json`: one new statement-only lemma, unsplit, no Mathlib match. It states the actual adjoints of the quotient transitions, including normalization at every pair of indices and its cocycle. It contains no proof, proof dependencies or hidden proof sketch.
- `citations.json`: verbatim statement excerpts for every node used by each of the eight steps.
- `searches.jsonl`: searches made by the required msearch command. The inherited four search entries had no surviving log; I ran those queries, read their actual new results, refreshed the results accurately, and added alternative phrasings.

## Attachments

None. I searched the full slopmaster2 `WeilConjectures/` tree for the blueprint id, integral-adic trace vocabulary and normalized systems. `SixFunctors/ProEtale/TraceFormula/Adic.lean` has sorried realization declarations and a sorried Euler-product theorem, not this two-clause arbitrary-coefficient-morphism identity. `Main.lean:111` states a different finite-level theorem, requires invertibility, and is itself sorried. No attachment applies; master sorry declarations are reference only.

## WANTED

None. All sources needed for this repair were present locally.

## Return repaired

The return identifies the old step 5 (2289 characters) as non-elementary and asks for its hidden arguments as cited nodes, with the statement and route unchanged. The preserved sandbox had already separated this into four steps and proposed a normalization lemma, but had no report, citations or search log. I retained its route and proof, corrected the proposed lemma (normalization maps are isomorphisms; raw transition maps need not be), made its coefficient category and every pair of indices explicit, and completed its searches and citations.

The hidden normalization comparison now has its own new node. The realization identifications already occur in the statement of `prop-trf-adic-coefficient-morphism-systems`; step 6 cites that paragraph, so no duplicate node was made. The global lift argument is an application of item (3) of `prop-trf-rational-frobenius-integral-model` and item (2) of the adic-systems proposition, now step 7. The local lift argument uses item (4) of the model proposition, its reduction assertion, and the definition/criterion of a lift in the adic-systems proposition, now step 8. These are existing nodes supplying the arguments the return asks to expose. The final application of the already proved clause (1) is kept in step 8. No whole clause of this item has been moved into a new node. All non-elementary steps are shorter than 2000 characters (the maximum is the unchanged step 2, 866 characters).

The blueprint proof (2) loosely calls both operators derived limits. The local model proposition actually states reduction of the local operator. As in the original returned proof, I use that precise reduction assertion and the definition of lift; I do not infer an unstated local derived-limit theorem.

## Not duplicates

lem-trf-lattice-reduction-tower-normalized vs det-sp-reduction-tower-normalized: the latter states the tower for the rings O_E/ell^n, whereas this lemma states the actual quotient-adjoint maps at every O_E/varpi^n level in the trace-formula convention. For ramified E, ell^n has varpi-exponent en; the former gives only those levels, and its statement does not provide normalization at intervening uniformizer levels. Its conclusion therefore cannot be substituted directly. The new lemma does not assert its additional uniform-bound or constructibility theorems: finite-Tor constructibility of levels is assumed.

lem-trf-lattice-reduction-tower-normalized vs def-trf-adic-system: the existing node defines normalized systems and their adjoint maps; it does not prove that quotient-derived reductions have those invertible adjoints.

lem-trf-lattice-reduction-tower-normalized vs def-weil-integral-reduction-tower: this definition constructs quotient transitions and maps from the integral object, but does not assert normalization at the finite coefficient rings.

lem-trf-lattice-reduction-tower-normalized vs lem-weil-integral-reduction-tower-well-defined: the existing statement proves independence of resolutions for the quotient transitions and cone maps; it does not prove that the finite-ring adjoint reduction maps are isomorphisms.

lem-trf-lattice-reduction-tower-normalized vs prop-trf-rational-frobenius-integral-model: the existing proposition supplies compatible Frobenius morphisms, their iterates and global/local operator formulas; it does not state the quotient-adjoint normalization theorem. The new lemma contains no Frobenius data or trace assertion.

lem-trf-lattice-reduction-tower-normalized vs prop-trf-adic-coefficient-morphism-systems: the latter starts with an already normalized tower; its reduction-tower paragraph identifies realizations under that setup. It does not establish normalization of the sheaf-level quotient transitions.

The whole-DAG searches used `reduction tower`, `associativity isomorphisms`, normalized systems, and the source tag 0D6D. Whole-blueprint searches used `normalized`, `reduction tower`, `lattice`, and `derived change of rings`; the ancestor command returns this item itself. I opened the candidates above and the ringed-topos comparison candidates. None states the uniformizer-level quotient-adjoint assertion; same_as is empty. No second copy of the already stated realization or lift comparisons was created.

## Review by NR

I read current main-20261015 proof (1)–(2), the trace-transport unit and the chapter record. The repair follows exactly the route finite-level formula → trace reduction → equality in the complete coefficient ring, followed by the lattice specialization. For the new lemma I read the reduction-tower paragraph of proof (2), `def-trf-adic-system`, and `def-weil-integral-reduction-tower`. I also read Stacks sites-cohomology.tex, Tag 0G7E (lemma-pullback-K-flat), Tag 06YY (lemma-derived-base-change), and Tag 0D6D (lemma-derived-pullback-composition), which justify computing successive ring changes on a flat-term K-flat model. The source's omitted comparison is made an explicit statement-only obligation, not silently declared elementary. It is over the completed coefficient sheaf R_X and the constant quotient sheaves, not a discrete constant O_E sheaf.

In step 1, clause (1) of `lem-weil-point-counts-finite` applies to the finite-type X_0 and finite extension F_(q^m)/k_0. Items (1)–(3) of `prop-trf-adic-coefficient-morphism-systems` provide level finiteness/normalization, compatible operators and lifts; I read each clause. The system is normalized and m is positive as required. Step 2 applies `thm-trf-coefficient-morphism-trace-formula`: its explicit etale-origin witness and admissibility hypotheses are assumed at every level, and the levels are in D^b_ctf by the item hypothesis. The stalk expression agrees with item (3) of the adic-systems proposition. Neither cited theorem requires invertible coefficient maps.

In step 3 I checked item (4) of the adic-systems statement: the trace of every lift reduces to the trace of the indicated finite-level operator, independently of the lift. Step 4 uses that same stated inverse-limit identification. The only elementary argument is distributing the quotient ring homomorphism over the finite sum and subtraction, then observing that a tuple with zero coordinates is zero. No infinite sum is interchanged with a limit.

In step 5 the new lemma is applied to exactly the integral K_O and its quotient tower; the finite-Tor constructibility of every reduction is an explicit hypothesis of the model proposition and the lattice clause. Item (2) of the model proposition states compatibility with those transitions, not just existence of unrelated coefficient maps. Step 6 uses exactly the reduction-tower sentence in the adic-systems statement, which identifies both the global realization and the completed stalk. Thus there is no unproved comparison hidden behind an identification.

In step 7 I verified the exact sentence in item (3) of the model statement that U_m is the derived limit of the displayed levelwise operators. Its projection equations are precisely the sufficient lift criterion in item (2) of the adic-systems statement. In step 8 item (4) of the model proposition states reduction of U_(y,m) to psi_(n,m,y); with the canonical pi_n of the adic-systems statement this is its defining lift equation. I kept the pi_n in that equation, rather than identifying reductions by an arbitrary isomorphism. Applying clause (1) with these lifts gives the lattice identity on the objects identified in step 6.

For the new lemma I tested zero K, an empty X, n=j, n=1, a non-flat torsion K on a point (within the assumed integral category), and ramified E. Derived tensor is essential for the torsion test: a second underived tensor is not being substituted. For a flat-term K-flat representative P, the normalization comparison has the formula ((x tensor b) tensor c) → x tensor (b-bar c), with inverse x tensor c → (x tensor 1) tensor c. These are the adjoints of the quotient maps, and at three indices both paths give x tensor (b-bar c-bar d). This explains why the statement is true also for ramified coefficients and why ordinary tensor-product associativity alone is not a Mathlib match. No invertibility of u is used, including u=0. For the item, an empty set of rational points gives the zero sum, m=1 and all n≥1 meet the cited hypotheses, and equality for arbitrary lifts remains the conclusion.

I checked delivery-errors B–E: the new statement introduces its objects and definitions, has empty proof/proof_deps, and its searches are actual logged requests. The searches returned ordinary tensor associators, scalar-tower lemmas, classical adic-completion objects and generic sheaf-module maps, not normalized derived coefficient systems; the second phrasings changed the mathematical vocabulary. Both Loogle errors are recorded as identifier failures, not as proof that no similarly named theorem exists. The alternative semantic searches and local grep address the actual concept. The new lemma is strictly an input to the lattice specialization, with no trace identity. Every uses entry has a verbatim quotation in citations.json. I verified the statement and Lean record stayed unchanged, the first four steps are preserved, no cycle is introduced by the new statement dependencies, and no prohibited SGA route or source is used.

## Validation

The required initial dry run was attempted before modifying the retained split and exited: report.md is missing or has no Review by NR section. The completed repair will be validated by the required server preflight through deliver.py --no-push, then delivered with the same tool. No Lean, compiler, Lake, live-project edit or direct git command was used.
