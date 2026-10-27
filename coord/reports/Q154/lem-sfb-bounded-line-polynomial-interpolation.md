## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-line-polynomial-interpolation.json: item split into four proof steps; original statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-lagrange-reconstruction.json: statement, Mathlib leaf (Lagrange.eq_interpolate and Lagrange.interpolate_eq_sum).
- citations.json: verbatim statement excerpts for every dependency of every item step.

Attachments: none. Searching lean/WeilConjectures by the exact blueprint tag and by interpolation, affine line and polynomial terminology found no declaration stating the item. The project's finite-field Lagrange idempotents and roots-of-unity interpolation concern other objects and hypotheses.

WANTED: none.

The item was unsplit. I retained its bounded statement, its original searches and provenance. Milne Chapter I Lemma 10.12, printed p.47, gives the coordinate induction and solves for coefficient functions at distinct interpolation nodes. Proposition 10.13, printed pp.47–48, supplies the uniform degree bound in the intended application. I made the translated induction explicit, used a fixed D+1 nodes for every slice, and proved the total-degree assertion by detecting the top homogeneous part along a radial line. This expansion is marked agent-origin, since Milne does not write that last argument. There is no statement correction.

The ancestor command reports `a node created for lem-sfb-bounded-line-polynomial-interpolation has blueprint.from.node = None`. I preserved this inherited null and the original via chain, and prepended the item for its new leaf. The explicit place continues to identify det-thm-sf-ctf-stability-direct-images proof (3) and the precise supporting Milne interpolation argument. The latest blueprint is main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). Its unit and direct-image proof were read; the split is a subsidiary algebra tool and changes no unit route or record.

Nothing mathematical remains unfinished in the item's proof. The new node is already a Mathlib leaf and carries no proof or proof dependencies.

## Searches and reuse

Read all results of the recorded searches in searches.jsonl. The item searches in two semantic phrasings do not find the bounded-line criterion: MvPolynomial.map_restrict_dom_evalₗ concerns finite fields, Lagrange.funEquivDegreeLT is univariate, and aeval_natDegree_le is the opposite direction. The new leaf searches (LeanFinder, Loogle, LeanSearch, and grep) find the exact reconstruction ingredients. Loogle's unknown-identifier result for the deprecated name is recorded as such; the second Loogle query returns eq_interpolate. The single-file grep returned misparsed file fields, so I repeated grep against LinearAlgebra and read the actual source lines. All recorded queries were run using msearch.py, without direct Mathlib search commands.

Before making the leaf I searched all DAG statements, titles and Mathlib matches for Lagrange/interpolation and polynomial determination, and ran blueprint_refs.py search for Lagrange, interpolation, interpolat, polynomial values and polynomial. The blueprint searches found no matching statement. Existing lem-trf-polynomial-infinite-evaluation-identity and lem-trf-infinite-field-top-form-direction are reused rather than duplicated. A fresh multivariable-funext node would restate the final clause of this item; I instead wrote the short coefficient induction in step 3.

## Not duplicates

lem-sfb-lagrange-reconstruction vs lem-pc-polynomial-quotient-distinct-linear-crt: the existing node is a quotient-algebra CRT isomorphism with no degree restriction or explicit reconstruction formula; the new node is the Mathlib identity reconstructing a degree-bounded polynomial from distinct-node values.
lem-sfb-lagrange-reconstruction vs lem-trf-polynomial-infinite-evaluation-identity: the existing node asserts equality on infinitely many evaluations implies equality; the new node gives an explicit finite-node reconstruction identity and works over finite fields whenever there are enough distinct nodes.
lem-sfb-lagrange-reconstruction vs lem-sfb-bounded-line-polynomial-interpolation: reconstruction is a univariate polynomial identity with a polynomial supplied, not the construction of a finite-coordinate polynomial from an arbitrary function on a vector space.

## Review by Q154

I read Milne's Lemma 10.12 and Proposition 10.13 on printed pp.47–48, not just the imported source label. The item assumes a single bound D on all affine-line restrictions, which is exactly what permits a common finite set of nodes in the source's linear-system argument. No linear independence, characteristic-zero assumption or finite-dimensionality of W is introduced. The tuple may be dependent; the argument only substitutes linear combinations into F.

For the one new node I read Mathlib/LinearAlgebra/Lagrange.lean:147–148 (basisDivisor), 199–200 (basis), 299–308 (interpolate), 362–365 (eq_interpolate), and 453–455 (interpolate_eq_sum). Over a field, distinctness makes every denominator nonzero. Specializing the latter two identities to Fin (D+1) gives exactly the statement of the leaf, including its product formula. Degree at most D is strictly less than D+1, also for the zero polynomial. This is one rewriting specialization, so no intermediate theorem or duplicated clause of the item is hidden in it. Its unsplit proof fields are empty, all objects are introduced, its two notion nodes define precisely field and polynomial ring, and TeX has one layer of backslashes. It uses no Stacks lemma and no SGA source.

Step 1 cites def-weil-pbc-mv-polynomial-ring for the finite monomial description; with no variables only the constant monomial remains. Choosing finitely many distinct elements of an infinite set and starting the induction are elementary. The induction claim quantifies simultaneously over all translates w, which is required when step 2 replaces w by w+c_j e_n.

Step 2 cites the new reconstruction node for exactly q(T)=sum q(c_j)L_j(T), and the multivariate ring definition for polynomial multiplication and substitution. At fixed preceding coordinates the supplied q_x has degree at most D and takes the required P_j(x) values. Expanding P_j L_j proves the separate exponent bounds directly; I do not infer a total-degree bound from separate degrees. The step is non-elementary because it invokes reconstruction.

Step 3 opens and uses the statement of lem-trf-polynomial-infinite-evaluation-identity, not its proof: a commutative integral domain and an infinite set of equal evaluations give polynomial equality. K is an infinite field, so all those hypotheses hold. Collecting coefficients in the last variable is the finite-monomial definition of def-weil-pbc-mv-polynomial-ring. For each fixed preceding tuple the univariate zero identity forces every coefficient value to vanish, and the explicitly stated induction forces all coefficient polynomials to be zero. This proves all of the determination clause without creating a duplicate node.

Step 4 opens and uses lem-trf-infinite-field-top-form-direction for a nonzero homogeneous polynomial in r>=1 variables over an infinite field. The hypothesis m>D>=0 ensures a positive top degree; the r=0 and zero-polynomial cases were already separated. The top form H is nonzero because the finite support contains a monomial of maximum degree. The explicit substitution X_i=T v_i has top coefficient H(v); thus P(Tv) really has degree m. The original hypothesis applies to u=sum v_i e_i and w=0, even if u=0. Univariate equality uses the same existing equality leaf under its actual field hypotheses. This yields the contradiction and the claimed total-degree bound. The homogeneous-direction lemma is already a Mathlib leaf, so it is a permissible cross-unit tool; no non-Mathlib unit route is substituted.

I tested r=0 (a single evaluation of a constant), D=0 (one interpolation node and all restrictions constant), F=0, W=0, repeated/zero e_i, constant polynomials, and positive-characteristic infinite fields. No derivatives or divisions by factorials occur, so small characteristic causes no exception. For the new reconstruction leaf, D=0 gives the empty product 1 and q(T)=q(c_0); q=0 gives zero on both sides. Finite fields are allowed in that leaf with D+1 distinct nodes, but not in the item: over F_p the nonzero polynomial X^p-X shows why determination needs infinitude.

I checked B–E against the actual files: one statement-only leaf with exact names and lines; no duplicate; no new clause-restatement; every non-elementary invocation has a node; every citation quote is copied verbatim from that node's statement; uses have no return path to the item; degree and infinite-field hypotheses are checked at their applications. All four steps are below 2000 characters. The corrections made while preparing the split were to retain the full translated induction claim, to distinguish separate from total degree, and to treat the zero-variable and zero-polynomial cases before choosing a homogeneous direction. The item statement needed no correction.
