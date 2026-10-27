## Files written

- `dag/nodes/sec-trace-formula/lem-trf-hilbert-samuel-growth-dimension.json`: repaired item, statement unchanged, four assembly steps, 2215 total proof-text characters, status split.
- `dag/nodes/sec-trace-formula/lem-trf-maximal-adic-graded-length-bridge.json`: new statement-only unsplit node; standard maximal-adic grading, the cumulative length identity, and conditional passage from a homogeneous polynomial to a positive length polynomial. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-parameter-ideal-colength-bound.json`: new statement-only unsplit node; parameter-monomial surjections and binomial colength estimate, including zero parameters. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-artin-rees-principal-colength-difference.json`: new statement-only unsplit node; the exact quotient sequence and shifted colength difference for a nonzero nonunit in a local domain. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-prime-chain-bound-from-colength-polynomials.json`: new statement-only unsplit node; under explicitly supplied quotient polynomials and principal difference inequalities, quotient degree monotonicity, degree drop, and prime-chain induction. No Mathlib match.
- `citations.json`: full verbatim statement quotes for each node used by each item step.
- `searches.jsonl` and `search-*.txt`: the actual required command logs and the full search responses read. All four new nodes have LeanFinder, Loogle, grep, LeanSearch, and a second semantic phrasing, with exact queries recorded.
- `baseline-node.json`, `prior-report-NF.md`: retained original split and historical report, read before repair. The sandbox initially contained only dispatcher markers, with no item copy, report, citations, or searches. Thus the current read-only repository is the repair baseline; no previous sandbox work was discarded.

Four new nodes, zero new Mathlib leaves. Every new node has proof [], proof_deps [], proof_origin null and status unsplit. No Lean was written, and no compiler, Lake or build tool was invoked. Only the sandbox was written. The packaging/delivery scripts are the authorized exception that manage their own worktrees.

## Attachments

None. The exact item-tag and Hilbert/Samuel concept searches in lean/WeilConjectures give no completed declaration stating the item. The local Sheaf/RingTheory/HilbertSamuelGrowthDimension.lean:82 declaration IsLocalRing.exists_hilbertSamuel_polynomial still ends in sorry. The existing associated-graded-ring and finite-type constructions in WeilConjectures/RingTheory/AssociatedGradedRing.lean and AssociatedGradedFiniteType.lean do not prove the cumulative length identity or its conditional polynomial bridge. The new colength estimates and the conditional polynomial/prime-chain theorem have no matching project declaration. No local Sheaf sorry was treated as a finished proof.

## Wanted

None. All sources used are already present in literature/stacks-project/algebra.tex.

## Findings and repair of the return

The return asks for at least two comparable new statement-only tasks and a parent proof of at most 3000 characters. I extracted four substantive tasks and made the parent a 2215-character assembly. The original statement, statement dependencies, provenance, import fields, Lean attachment and maintainer review fields are retained. No STATEMENT-DISPUTED issue was found. No unit or chapter was edited. The source route remains associated graded polynomiality, discrete integration, the parameter-ideal upper bound, and the Artin--Rees/prime-chain lower bound.

The existing graded Hilbert-function theorem is reused as a node, not recreated. The bridge deliberately assumes its eventual component polynomial rather than asserting the whole Hilbert--Samuel theorem. The parameter estimate does not assert dimension equals degree, and the principal estimate does not assert eventual polynomiality. The prime-chain node takes all quotient polynomials and difference inequalities as hypotheses, which the item actually supplies. Thus none replaces the item by a same-strength relabelling, and no single new node owns the whole proof.

## Allocation of all original arguments

The bridge owns original steps 1--3: choose finitely many maximal-ideal generators, span the graded pieces by monomials, compare residue-field subspaces with R-submodules and a basis flag, sum the finite filtration, construct the graded multiplication and show representative independence, prove standard degree-one generation, and integrate the eventual component polynomial in the rational binomial basis. Its final assertion includes nonvanishing and positivity, so these are not dropped from the split. The existing graded Hilbert-function node supplies only the eventual component polynomial, exactly as before.

The parameter node owns original step 4's complete estimate: monomial surjections, the number of degree-i monomials, length inequalities and filtration, the binomial partial-sum identity, and the nilpotent case d=0. The parent still chooses a system of parameters, obtains L finite by a quotient, and compares leading degrees. The new statement is about a specified ideal with specified generators and colength, not the degree-equals-dimension conclusion.

The principal-difference node owns the commutative-algebra part of original step 5: enlarge Artin--Rees c to at least one, use xA intersect a^n contained in a^(n-c)xA, identify xA with A by multiplication by the nonzero x, compare the resulting quotient lengths, and account for length over A versus over A/(x). The polynomial-comparison part of old step 5 is assigned to the prime-chain node: a constant Q_p makes its finite difference zero and contradicts the positive length of the nonzero quotient; otherwise Q_p(X)-Q_p(X-c) has degree e_p-1 and leading coefficient c e_p lc(Q_p)>0.

The prime-chain node also owns all of original step 6: quotient surjections and identical scalar-restriction submodule lattices give degree monotonicity; strong induction on the degree for every proper quotient handles degree zero and the domain R/p_0, selects a nonzero x in p_1/p_0, descends the remaining chain to R/(p_0,x), counts l-1 inclusions there and returns l<=e. Its hypotheses are explicitly available for every proper quotient, so the induction is not circular. Old step 7 remains the final assembly.

The complete original text, without shortening, follows in the final section of this report so each future worker can recover its assigned argument. It is deliberately not inserted as proof steps or a proof sketch into a new node's statement.

## Sources, searches and blueprint

I read Stacks 00K8 (proposition-hilbert-function-polynomial) and the preceding definitions of phi and chi, 00JZ (lemma-numerical-polynomial) with its binomial telescoping proof, 00KQ (proposition-dimension) in full, and 00IN (lemma-Artin-Rees) with its proof. Tags were checked against literature/stacks-project/tags/tags. The bridge is the local residue-field specialization of 00K8 plus 00JZ. The parameter estimate is the monomial paragraph of 00KQ. The principal estimate is the explicit xA subset A use of 00IN in the exact-sequence route of 00KQ. The prime-chain task is the last paragraph of 00KQ with the precise polynomial and difference hypotheses made explicit. No SGA source is used.

Before creating the four nodes I searched the entire DAG by these tags and the associated-graded, Hilbert/Samuel, colength/length-polynomial, binomial and prime-chain notions. I opened the statements of the existing associated-graded definition, associated-graded finite-type theorem, graded Hilbert-function theorem, length definition, length-additivity theorem, Artin--Rees theorem, system-of-parameters theorem and dimension definition. Blueprint searches included Hilbert, associated graded, standard graded, parameter, length, binomial, Noetherian local, prime chain, 00K8, 00KQ, and 00IN. No imported blueprint statement duplicates a proposed new lemma. The source-tag overlaps are individually distinguished below.

The ancestor command returns lem-trf-local-term-locality. I read the chapter and sk-i-curve-zero unit records and retained the already reported historical limitation: current locality uses contraction, while this algebra input survives on the formal-monoid branch. Each new blueprint.from has the same ancestor and historical place, prepends this item to via, and names exactly which old item steps it extracts; same_as is []. This repair changes no chapter or unit route.

For every new node the required search command was run with that statement in mind, including two semantic phrasings, and its real output was read. All services returned answers. Module.length_eq_finrank (Length.lean:295-298) is only the vector-space length identity; it does not build or sum the maximal-adic grading. DiscreteValuationRing/Basic.lean:555-557 is restricted to DVRs. Ideal.index_pow_le (Ideal/Quotient/Index.lean:109-118) bounds additive-group index under Finite(R/I), with a different bound; arbitrary residue fields are allowed here, and this is no one-line module-length specialization. Ideal.exists_pow_inf_eq_pow_smul (Filtration.lean:389-392) is the already-represented Artin--Rees input, leaving the principal quotient and length calculation to prove. OrderOfVanishing/Basic.lean:292-301 requires dimension at most one. KrullDimension/Regular.lean:120-180 has dimension comparisons, and KrullDimension/Polynomial.lean has dimensions of polynomial rings; neither concerns degrees of colength polynomials. HilbertPoly.lean:18-42 treats coefficients of a supplied rational series and explicitly lists graded-module Hilbert polynomials as TODO. Accordingly all four nodes remain unsplit, not Mathlib leaves. Original item searches were retained byte for byte instead of pretending the old queries were run anew.

## Review by Q04

I checked each new statement with its source open, particularly which data its eventual worker receives. The bridge introduces R, its maximal ideal, the residue field, each graded piece and the natural associated-graded algebra. It asserts both standardness and the finite-length/sum identity, then takes an eventual component polynomial as a separate hypothesis. A residue-field subspace is exactly an R-submodule for these pieces. Its leading-coefficient conclusion uses that every maximal-adic quotient with n>=1 is nonzero, not a reducedness, coefficient-field or characteristic assumption. In a field the component polynomial is zero and the length polynomial is 1, so P=0 must be permitted and is permitted.

For the parameter statement I checked that J is inside m, contains m^a, and has finite quotient length L as required by the old estimate. The degree-i monomials multiply classes of R/J into J^i/J^(i+1), and their number is binom(i+d-1,d-1) only when d>=1. The d=0 clause is kept separate: J=0 and m^a=0 imply H(n)=length(R)=L for n>=a. The direction J^n subset m^n gives a surjection R/J^n onto R/m^n and hence the advertised upper bound. In the parent step 3 the cited system-of-parameters statement really supplies finite d, exactly d generators in m, and a maximal-ideal power inside J; length additivity really supplies the finite length of the quotient R/J of R/m^a. No Artinian-to-finite-length theorem is silently used.

For the principal statement I checked the domain and nonzero x hypotheses are exactly what identify A with xA, and x in the maximal ideal ensures B is nonzero and local. Its finite-length assumption is expressly supplied by parent step 1. Artin--Rees applies to finite module A and submodule xA, with ideal a; increasing c preserves its containment. The intersection containment gives a surjection xA/(xA intersect a^n) onto xA/a^(n-c)xA, so the first length is at least H_A(n-c). Subtracting it from H_A(n) is the upper bound for H_B(n), not the reverse inequality. Identical A- and B-submodule lattices give the equality of those two length conventions. I retained this scalar-restriction clause in the new statement, not only in an intended proof.

For the prime-chain statement I verified that all proper quotients and all thresholds are introduced independently; no uniform threshold is claimed. The polynomial and shifted-difference hypotheses are inputs, and no desired dimension formula is assumed. Quotient ideals correspond, maximal-ideal powers commute with quotient, and the scalar-restriction submodule sets are equal. These give H_J<=H_I for I subset J and therefore degree monotonicity with positive leading coefficients. For a prime p and x in m minus p, J=p+(x) remains proper; H_J>=1 excludes a constant Q_p and then the shifted difference has positive leading coefficient. Strong induction applies to all quotients of smaller degree. In a chain p_0 strictly below p_1, a chosen x in p_1 minus p_0 gives the domain quotient and lowers the degree strictly; the remaining primes stay distinct by inverse image. If the starting degree is zero the difference argument is already a contradiction, so the base case is explicit. The maximum chain length and Krull-dimension conventions match the cited dimension definition.

Parent step 1 uses exactly the bridge's standardness and last conditional assertion, and the existing graded Hilbert-function statement for a finite nonnegatively graded S-module M=S. The module is generated by 1 in degree zero. I reread both cited statements and they supply those clauses. Parent step 2 uses exactly the principal-difference node's inequality and the conditional chain node's stated hypotheses and conclusion; the quotient identifications in that step are the direct ideal correspondence, with generators descending to show Noetherianity. Parent step 3 uses exactly the parameter and length-additivity statements just checked and the binomial-bound node's two cases; comparing degrees of positive-leading polynomials is elementary. Parent step 4 only combines the established bounds and threshold. Every node cited by every item step has its complete, verbatim statement in citations.json, so no quote bends a definition into a theorem or takes an assertion from a cited proof instead of its statement.

I checked the small cases explicitly: a field has H(n)=1, zero positive graded pieces and degree 0; k[epsilon]/(epsilon^r) has H(n)=min(n,r) and eventual constant r; a DVR has H(n)=n, while its quotient by a uniformizer has constant length 1. For the principal inequality in a DVR, x=t^r permits c=r and gives min(n,r)<=n-(n-r)=r for n>r. A field has no nonzero x in its maximal ideal, so the principal hypothesis is vacuous there; the degree-zero induction forbids only positive-length prime chains. Repeated or zero entries among d>=1 parameter generators do not invalidate the monomial surjection. The zero ring is excluded throughout, preventing a zero length polynomial with undefined leading positivity. Mixed residue characteristic and finite or infinite residue fields require no extra hypothesis.

Against delivery-errors B--E I checked self-contained statement-only new nodes, exact tag/label sources, one backslash in decoded TeX, real searches with no invented verdict, correct blueprint ancestry, and explicit differences from all shared-tag nodes. Four extracted arguments provide separate work rather than moving all work into one same-strength lemma. No new node is a two-line consequence: the bridge combines graded construction, length filtration and discrete integration; the parameter task counts monomials and sums a power filtration; the principal task constructs and estimates a quotient exact sequence; the chain task compares polynomial degrees and proves a quotient-compatible induction. All parent steps are below 2000 characters, and the entire parent proof is below 3000. The original argument is preserved verbatim below rather than shortened or blurred.

## Unfinished work

The four new nodes intentionally have no proof, as required by the return. Their arguments are assigned above and retained verbatim below for parallel future workers. The parent split is complete at this level. Delivery checks and push are recorded in the final delivery command output.

## Not duplicates

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-trf-complete-toric-facet-valuations: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Facet primes and normalized monomial valuations of complete toric models (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-trf-log-smooth-log-regular: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Injective logarithmic charts preserve log regularity and recover divisorial structure (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-trf-hilbert-samuel-growth-dimension: the existing item asserts existence with degree equal to dimension; this repair extracts a strictly smaller auxiliary argument with the additional inputs in its own statement.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-trf-formal-monoid-ring-dimension: the existing node concerns complete formal monoid rings and dimension formulas, not the local length/prime-chain estimate stated here.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-sfb-strict-local-prime-to-p-kummer-splitting: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Prime-to-p torsors on a strict-local boundary puncture split at a finite root level (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-local-dimension-function-calculus: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Local existence and codimension calculus for dimension functions (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-parameter-ideal-formal-normalization: the existing node constructs a finite formal normalization from a parameter tuple; it has no binomial colength or conditional polynomial/prime-chain conclusion.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-noetherian-local-domain-open-infinite: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Nonempty opens in a high-dimensional Noetherian local domain are infinite (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-punctured-support-cohomological-bound: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Support-sensitive cohomological bound on an excellent strictly local punctured spectrum (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-catenary-completion-hyperplane: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Hyperplane reduction of a non-equidimensional completion (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-per-snc-root-algebra-structure: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Structure of the simultaneous parameter-root algebra over a strict local ring (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-noetherian-local-system-of-parameters: the existing node constructs a parameter ideal; the new node either estimates lengths for an already given ideal or bounds prime chains from given quotient polynomials.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-regular-local-generators-regular-sequence: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states A regular system of parameters is a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-complete-local-domain-finite-over-regular: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states A Noetherian complete local domain is finite over a regular complete power series subring (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-geometrically-regular-over-field-flat: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-cm-module-good-element-nonzerodivisor: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states An element cutting the support of a Cohen–Macaulay module by one dimension is a nonzerodivisor on it (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-polynomial-ring-origin-regular-local: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states The polynomial ring over a field localized at the origin is regular local of dimension d (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-polynomial-ring-maximal-localization-dimension: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Localizations of a polynomial ring over a field at maximal ideals have dimension n (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-noetherian-local-dimension-le-generators: the existing bound uses generators of the maximal ideal, not an arbitrary parameter ideal colength or given quotient length-polynomial degrees.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-completion-dimension: the existing node compares a ring with its completion; the new node has no completion.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-depth-ext: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Depth of a finite module over a Noetherian local ring via Ext from the residue field (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-noetherian-local-finite-krull-dimension: the existing node says dimension is finite; it supplies neither the binomial colength bound nor comparison with a supplied length polynomial.

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-weil-pbc-kollar-local-dichotomy: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Kollar's lemma: a Noetherian local ring is Artinian, regular of dimension one, of depth at least two, or has a finite birational-type extension (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-kun-finite-type-local-dimension: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Finite local dimension for finite type schemes over a field (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-exc-local-curve-principal-total-fractions: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states A parameter in a reduced local curve localizes to the total fraction ring (its statement introduces different data and does not give this estimate).

lem-trf-prime-chain-bound-from-colength-polynomials vs lem-exc-regular-local-lift-regular-sequence-quotient: the new node concerns a conditional prime-chain bound from all quotient colength polynomials and shifted differences; the existing node instead states Regularity lifts from the quotient by a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-maximal-adic-graded-length-bridge vs lem-trf-hilbert-samuel-growth-dimension: the existing item asserts existence with degree equal to dimension; this repair extracts a strictly smaller auxiliary argument with the additional inputs in its own statement.

lem-trf-maximal-adic-graded-length-bridge vs lem-trf-standard-graded-hilbert-function: the existing node gives eventual dimensions for an arbitrary finite graded module; the new bridge constructs the local grading and cumulative length polynomial from such an input.

lem-trf-maximal-adic-graded-length-bridge vs lem-trf-formal-monoid-ring-dimension: the existing node concerns complete formal monoid rings and dimension formulas, not the local length/prime-chain estimate stated here.

lem-trf-parameter-ideal-colength-bound vs lem-trf-complete-toric-facet-valuations: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Facet primes and normalized monomial valuations of complete toric models (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-trf-log-smooth-log-regular: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Injective logarithmic charts preserve log regularity and recover divisorial structure (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-trf-hilbert-samuel-growth-dimension: the existing item asserts existence with degree equal to dimension; this repair extracts a strictly smaller auxiliary argument with the additional inputs in its own statement.

lem-trf-parameter-ideal-colength-bound vs lem-trf-formal-monoid-ring-dimension: the existing node concerns complete formal monoid rings and dimension formulas, not the local length/prime-chain estimate stated here.

lem-trf-parameter-ideal-colength-bound vs lem-sfb-strict-local-prime-to-p-kummer-splitting: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Prime-to-p torsors on a strict-local boundary puncture split at a finite root level (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-per-local-dimension-function-calculus: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Local existence and codimension calculus for dimension functions (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-per-parameter-ideal-formal-normalization: the existing node constructs a finite formal normalization from a parameter tuple; it has no binomial colength or conditional polynomial/prime-chain conclusion.

lem-trf-parameter-ideal-colength-bound vs lem-per-noetherian-local-domain-open-infinite: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Nonempty opens in a high-dimensional Noetherian local domain are infinite (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-per-punctured-support-cohomological-bound: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Support-sensitive cohomological bound on an excellent strictly local punctured spectrum (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-per-catenary-completion-hyperplane: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Hyperplane reduction of a non-equidimensional completion (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-per-snc-root-algebra-structure: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Structure of the simultaneous parameter-root algebra over a strict local ring (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-noetherian-local-system-of-parameters: the existing node constructs a parameter ideal; the new node either estimates lengths for an already given ideal or bounds prime chains from given quotient polynomials.

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-regular-local-generators-regular-sequence: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states A regular system of parameters is a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-complete-local-domain-finite-over-regular: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states A Noetherian complete local domain is finite over a regular complete power series subring (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-geometrically-regular-over-field-flat: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-cm-module-good-element-nonzerodivisor: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states An element cutting the support of a Cohen–Macaulay module by one dimension is a nonzerodivisor on it (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-polynomial-ring-origin-regular-local: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states The polynomial ring over a field localized at the origin is regular local of dimension d (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-polynomial-ring-maximal-localization-dimension: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Localizations of a polynomial ring over a field at maximal ideals have dimension n (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-noetherian-local-dimension-le-generators: the existing bound uses generators of the maximal ideal, not an arbitrary parameter ideal colength or given quotient length-polynomial degrees.

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-completion-dimension: the existing node compares a ring with its completion; the new node has no completion.

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-depth-ext: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Depth of a finite module over a Noetherian local ring via Ext from the residue field (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-noetherian-local-finite-krull-dimension: the existing node says dimension is finite; it supplies neither the binomial colength bound nor comparison with a supplied length polynomial.

lem-trf-parameter-ideal-colength-bound vs lem-weil-pbc-kollar-local-dichotomy: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Kollar's lemma: a Noetherian local ring is Artinian, regular of dimension one, of depth at least two, or has a finite birational-type extension (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-kun-finite-type-local-dimension: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Finite local dimension for finite type schemes over a field (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-exc-local-curve-principal-total-fractions: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states A parameter in a reduced local curve localizes to the total fraction ring (its statement introduces different data and does not give this estimate).

lem-trf-parameter-ideal-colength-bound vs lem-exc-regular-local-lift-regular-sequence-quotient: the new node concerns a binomial bound for colengths of powers of a specified ideal; the existing node instead states Regularity lifts from the quotient by a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-trf-complete-toric-facet-valuations: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Facet primes and normalized monomial valuations of complete toric models (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-trf-completed-free-into-product-universally-injective: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Completed direct sum embeds universally injectively into the product (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-trf-log-smooth-log-regular: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Injective logarithmic charts preserve log regularity and recover divisorial structure (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-trf-hilbert-samuel-growth-dimension: the existing item asserts existence with degree equal to dimension; this repair extracts a strictly smaller auxiliary argument with the additional inputs in its own statement.

lem-trf-artin-rees-principal-colength-difference vs lem-trf-formal-monoid-ring-dimension: the existing node concerns complete formal monoid rings and dimension formulas, not the local length/prime-chain estimate stated here.

lem-trf-artin-rees-principal-colength-difference vs lem-pc-coherent-kernel-ideal-intersection-bound: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states A high ideal multiple intersects a kernel in a prescribed kernel multiple (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-sc-principal-ideal-dvr: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Local domains with principal maximal ideal (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-sfb-adic-short-complex-cohomology-ml: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Artin–Rees stabilizes the cohomology of actual adic quotient short complexes (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-sfb-strict-local-prime-to-p-kummer-splitting: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Prime-to-p torsors on a strict-local boundary puncture split at a finite root level (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-local-dimension-function-calculus: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Local existence and codimension calculus for dimension functions (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-parameter-ideal-formal-normalization: the existing node constructs a finite formal normalization from a parameter tuple; it has no binomial colength or conditional polynomial/prime-chain conclusion.

lem-trf-artin-rees-principal-colength-difference vs lem-per-noetherian-local-domain-open-infinite: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Nonempty opens in a high-dimensional Noetherian local domain are infinite (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-ideal-torsion-preserves-injectives: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Ideal-power torsion preserves injective modules over a Noetherian ring (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-punctured-support-cohomological-bound: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Support-sensitive cohomological bound on an excellent strictly local punctured spectrum (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-catenary-completion-hyperplane: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Hyperplane reduction of a non-equidimensional completion (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-per-snc-root-algebra-structure: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Structure of the simultaneous parameter-root algebra over a strict local ring (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-noetherian-local-system-of-parameters: the existing node constructs a parameter ideal; the new node either estimates lengths for an already given ideal or bounds prime chains from given quotient polynomials.

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-regular-local-generators-regular-sequence: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states A regular system of parameters is a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-coherent-artin-rees: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Artin-Rees for coherent modules on a Noetherian scheme (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-complete-local-domain-finite-over-regular: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states A Noetherian complete local domain is finite over a regular complete power series subring (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-geometrically-regular-over-field-flat: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-artin-rees: the existing statement supplies only an intersection formula; the new principal-difference node adds injective multiplication, the quotient exact sequence and its length inequality.

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-coherent-formal-modules-abelian: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states The category of coherent formal modules is abelian (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-cm-module-good-element-nonzerodivisor: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states An element cutting the support of a Cohen–Macaulay module by one dimension is a nonzerodivisor on it (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-polynomial-ring-origin-regular-local: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states The polynomial ring over a field localized at the origin is regular local of dimension d (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-tor-strictly-pro-zero: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Tor against A/I^n of a finite module over a Noetherian ring is strictly pro-zero (Stacks 0911) (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-noetherian-koszul-augmentation-pro-zero: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Noetherian koszul procomparison (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-polynomial-ring-maximal-localization-dimension: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Localizations of a polynomial ring over a field at maximal ideals have dimension n (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-noetherian-local-dimension-le-generators: the existing bound uses generators of the maximal ideal, not an arbitrary parameter ideal colength or given quotient length-polynomial degrees.

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-completion-dimension: the existing node compares a ring with its completion; the new node has no completion.

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-depth-ext: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Depth of a finite module over a Noetherian local ring via Ext from the residue field (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-tensor-tower-kernel-pro-zero: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Tensor kernels of finite submodule inclusions are eventually killed in flat quotient towers (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-noetherian-local-finite-krull-dimension: the existing node says dimension is finite; it supplies neither the binomial colength bound nor comparison with a supplied length polynomial.

lem-trf-artin-rees-principal-colength-difference vs lem-weil-pbc-kollar-local-dichotomy: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Kollar's lemma: a Noetherian local ring is Artinian, regular of dimension one, of depth at least two, or has a finite birational-type extension (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-kun-finite-type-local-dimension: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Finite local dimension for finite type schemes over a field (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-exc-local-curve-principal-total-fractions: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states A parameter in a reduced local curve localizes to the total fraction ring (its statement introduces different data and does not give this estimate).

lem-trf-artin-rees-principal-colength-difference vs lem-exc-regular-local-lift-regular-sequence-quotient: the new node concerns the local-domain principal-quotient colength difference; the existing node instead states Regularity lifts from the quotient by a regular sequence (its statement introduces different data and does not give this estimate).

lem-trf-maximal-adic-graded-length-bridge vs lem-weil-pbc-associated-graded-finite-type: finite type does not supply degree-one generation, the cumulative module-length formula, or integration of an eventual homogeneous polynomial. The associated-graded definition is reused as a statement dependency.

## Original argument retained verbatim with new owners

### Original step 1: maximal-adic graded/length bridge

Put $\mathfrak m=\mathfrak n$, $k=R/\mathfrak m$ and $H_R(n)=\mathrm{length}_R(R/\mathfrak m^n)$ for $n\ge1$, with $H_R(0)=0$. By [def-weil-pbc-noetherian-ring], choose generators $y_1,\ldots,y_t$ of $\mathfrak m$. The degree-$i$ monomials in the $y_j$ span $\mathfrak m^i/\mathfrak m^{i+1}$ over $k$, so these spaces are finite-dimensional. An $R$-submodule of a module killed by $\mathfrak m$ is exactly a $k$-subspace; a basis flag therefore has composition factors $k$, of length one. Thus these pieces have $R$-length equal to their $k$-dimension. The filtration by powers of $\mathfrak m$ and [lem-weil-pbc-length-additive-short-exact] now give, for every $n\ge1$, finiteness and the identity $H_R(n)=\sum_{i=0}^{n-1}\dim_k(\mathfrak m^i/\mathfrak m^{i+1})$.

Original uses: def-weil-pbc-noetherian-ring, def-weil-pbc-module-length, lem-weil-pbc-length-additive-short-exact.

### Original step 2: maximal-adic graded/length bridge; the existing graded Hilbert-function theorem stays in the parent

Form $S=\bigoplus_{i\ge0}\mathfrak m^i/\mathfrak m^{i+1}$, with product $[a]_i[b]_j=[ab]_{i+j}$. Changing a representative changes the product by an element of $\mathfrak m^{i+j+1}$, so it is well defined. Its degree zero is $k$, and the degree-one classes of the $y_j$ generate it, by the monomial description in step 1. Thus $S$ is standard graded in [def-pc-standard-graded-algebra]. Apply [lem-trf-standard-graded-hilbert-function] with $M=S$ (generated by its unit in degree zero). We obtain $P\in\mathbf Q[X]$ such that $\dim_k(\mathfrak m^i/\mathfrak m^{i+1})=P(i)$ for all sufficiently large $i$.

Original uses: def-pc-standard-graded-algebra, lem-trf-standard-graded-hilbert-function.

### Original step 3: maximal-adic graded/length bridge

The polynomials $\binom{X}{j}$ form a rational basis, since their degrees are $j$ with nonzero leading coefficients $1/j!$. Write $P(X)=\sum_j a_j\binom{X}{j}$. The identity $\binom{i+1}{j+1}-\binom{i}{j+1}=\binom{i}{j}$ shows by telescoping that the tail sum in step 1 equals $\sum_j a_j\binom{n}{j+1}$ plus a rational constant accounting for the initial terms. Hence $H_R(n)=Q_R(n)$ eventually for some $Q_R\in\mathbf Q[X]$. Since $\mathfrak m^n\subseteq\mathfrak m\ne R$, every $R/\mathfrak m^n$ is nonzero and $H_R(n)\ge1$. Therefore $Q_R\ne0$; its leading coefficient is positive, because a nonzero rational polynomial has the sign of its leading coefficient at sufficiently large positive integers. Write $e_R=\deg Q_R\ge0$. These three steps apply to every nonzero Noetherian local ring.

Original uses: (elementary).

### Original step 4: parameter-ideal colength bound, with parameter selection and degree comparison in the parent

For the upper bound let $d=\dim R$. By [lem-weil-pbc-noetherian-local-system-of-parameters], $d$ is finite and there is $J=(x_1,\ldots,x_d)\subseteq\mathfrak m$ with $\mathfrak m^a\subseteq J$ for some $a\ge1$. Hence $R/J$ is a quotient of the finite-length module $R/\mathfrak m^a$; let its length be $L$. For $d\ge1$, the degree-$i$ monomials in the $x_j$ give a surjection from $\binom{i+d-1}{d-1}$ copies of $R/J$ onto $J^i/J^{i+1}$. Length additivity [lem-weil-pbc-length-additive-short-exact], first for the kernel of this surjection and then for the $J$-power filtration, gives $\mathrm{length}_R(R/J^n)\le L\sum_{i=0}^{n-1}\binom{i+d-1}{d-1}=L\binom{n+d-1}{d}$. Since $J^n\subseteq\mathfrak m^n$, the quotient $R/J^n\twoheadrightarrow R/\mathfrak m^n$ bounds $H_R(n)$ by this same degree-$d$ polynomial. If $d=0$, the cited statement gives $J=0$ and $\mathfrak m^a=0$, so $H_R(n)=\mathrm{length}_R(R)$ for $n\ge a$. In either case the positive leading coefficient from step 3 forces $e_R\le d$.

Original uses: lem-weil-pbc-noetherian-local-system-of-parameters, lem-weil-pbc-length-additive-short-exact.

### Original step 5: principal colength difference; polynomial degree comparison in the prime-chain node

To obtain the opposite bound, let $(A,\mathfrak a)$ be any Noetherian local domain and $0\ne x\in\mathfrak a$. Put $B=A/(x)$, a nonzero Noetherian local ring. Apply [lem-weil-pbc-artin-rees] to $M=A$, $N=xA$ and $I=\mathfrak a$, enlarging its constant to $c\ge1$. For $n>c$, $xA\cap\mathfrak a^n\subseteq\mathfrak a^{n-c}xA$. The exact quotient sequence and [lem-weil-pbc-length-additive-short-exact] give $H_B(n)=H_A(n)-\mathrm{length}_A(xA/(xA\cap\mathfrak a^n))\le H_A(n)-H_A(n-c)$. Here multiplication by $x$ identifies $A$ with $xA$, so $xA/\mathfrak a^{n-c}xA\cong A/\mathfrak a^{n-c}$; the indicated inclusion gives the needed surjection onto this quotient. Also $B/\mathfrak a^nB=A/(xA+\mathfrak a^n)$, and its $A$- and $B$-submodules coincide, so its two lengths agree. Step 3 supplies the polynomials for $A$ and $B$. Since $H_B(n)\ge1$, $e_A=0$ is impossible: then $Q_A(n)-Q_A(n-c)=0$. For $e_A\ge1$, that difference has degree $e_A-1$ and positive leading coefficient $c e_A\operatorname{lc}(Q_A)$. Comparing eventual values yields $e_B\le e_A-1$.

Original uses: lem-weil-pbc-artin-rees, lem-weil-pbc-length-additive-short-exact.

### Original step 6: prime-chain bound from colength polynomials

Prove by strong induction on $e_R$ that every chain of prime ideals of $R$ has length at most $e_R$. Chains of length zero already satisfy this. Given a strict chain $\mathfrak p_0\subsetneq\mathfrak p_1\subsetneq\cdots\subsetneq\mathfrak p_l$ with $l\ge1$, put $A=R/\mathfrak p_0$ and choose $x\in\mathfrak p_1/\mathfrak p_0$, $x\ne0$. All these primes lie in the maximal ideal of the local ring, so $x$ is in the maximal ideal of $A$. Quotient ideals correspond to ideals containing the kernel, showing directly that $A$, and $B=A/(x)$, are nonzero Noetherian local rings; $A$ is a domain since $\mathfrak p_0$ is prime. The surjections $R/\mathfrak m^n\twoheadrightarrow A/(\mathfrak mA)^n$ and length additivity [lem-weil-pbc-length-additive-short-exact] give $e_A\le e_R$ (lengths over the quotient ring agree by their identical submodule lattices). Step 5 implies $e_A\ge1$ and $e_B<e_R$. Thus if $e_R=0$ such a chain is impossible, which proves the base case. Otherwise the induction hypothesis applies to $B$. Its distinct primes $\mathfrak p_1/(\mathfrak p_0,x)\subsetneq\cdots\subsetneq\mathfrak p_l/(\mathfrak p_0,x)$ form a chain of length $l-1$, so $l-1\le e_B\le e_A-1\le e_R-1$. Therefore $l\le e_R$. Taking the supremum in [def-weil-pbc-krull-dimension-ring] gives $\dim R\le e_R$.

Original uses: lem-weil-pbc-length-additive-short-exact, def-weil-pbc-krull-dimension-ring.

### Original step 7: parent final assembly

Steps 4 and 6 give $\deg Q_R=e_R=\dim R$. Step 3 gives $Q_R\ne0$ and its positive leading coefficient. Choose $N\ge1$ larger than the threshold in step 3. Step 1 gives finite composition length for every $n\ge1$, and step 3 gives $\mathrm{length}_R(R/\mathfrak n^n)=Q_R(n)$ for $n\ge N$, with exactly the exponent in the statement.

Original uses: (elementary).

