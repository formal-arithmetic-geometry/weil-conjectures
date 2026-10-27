# Q104 stage-1 delivery: lem-sfb-abelian-trace-intersection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-trace-intersection.json`: split, unchanged statement, four proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-line-bundle-degree-square.json`: new statement-only prerequisite, unsplit, no Mathlib match. The degree of the homomorphism of an arbitrary invertible sheaf is the square of its top intersection divided by g!.
- `dag/nodes/sec-six-functors-basics/lem-sfb-isogeny-relative-tate-determinant.json`: new statement-only prerequisite, unsplit, no Mathlib match. For two maps with the same source and target, normalize by an isogeny and obtain its relative Tate determinant as a degree ratio, assigning zero to non-isogenies.
- `citations.json`: a verbatim statement quote for all 13 step/node citation pairs.
- `searches.jsonl`: actual msearch records. No service was unavailable. Read the returned signatures: trace forms, root-system polarization, determinants of base change, lattice indices and elliptic division-polynomial degrees do not state either geometric prerequisite.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, Rosati, polarization, trace/intersection, degree and determinant/Tate terminology did not give the item or either new node. The project has the Tate module, rank, componentwise action and isogeny degree material, but no closed proof of the claimed formula. Mathlib is not treated as a project attachment.

## WANTED

None. The available Milne notes supply the two mathematical inputs and the exact item statement. The calculation omitted by Milne Theorem 14.3 is supplied here as an agent proof; it does not depend on acquiring the reference Milne 1986, section 17.

## Problems found and changes

There is no statement dispute or correction. The item correctly requires g>0, keeps the given rational inverse mu, and allows all endomorphisms f. Milne Theorem 14.3 writes the product in the opposite cyclic order, but the calculation here computes mu f-dual lambda f directly, so it does not need a separate trace-cyclicity citation.

The empty imported proof is replaced by an actual determinant calculation. No proof is moved wholesale into a new node: neither prerequisite involves f, Rosati products or trace. The item creates N_r = L^r tensor f^*L, derives phi(N_r) by the representing-family tensor identity, obtains a polynomial identity from degree squares, and extracts its next coefficient.

The chapter and unit are unchanged. Read their records and the current blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; this item is a supporting calculation in the previously recorded alteration/level-rigidity prerequisite chain. The ancestor command returns None, as the existing item does; the new nodes retain that anchor and prepend the item to the existing via chain. Whole-blueprint searches for Rosati, polarization, isogeny, Riemann/Riemann-Roch, intersection, degree/homomorphism and determinant/Tate found no blueprint statement of either new prerequisite or the item. same_as remains empty.

## Not duplicates

lem-sfb-abelian-line-bundle-degree-square vs lem-sfb-abelian-trace-intersection: the new statement contains neither an endomorphism f nor a trace or Rosati product; it is the general degree formula for an arbitrary invertible sheaf, including degenerate ones.

lem-sfb-abelian-line-bundle-degree-square vs lem-sfb-abelian-polarization-calculus: the existing node constructs the dual and phi and gives its pullback formula, but does not compute its degree or any Euler characteristic/intersection square.

lem-sfb-abelian-line-bundle-degree-square vs lem-sc-riemann-roch: the existing Riemann-Roch statement is for curves and coherent sheaves on them; it is not abelian Riemann-Roch in arbitrary dimension and does not compute the degree of phi_N. The same distinction applies to sk-thm-picard-rr and sk-thm-picard-main.

lem-sfb-isogeny-relative-tate-determinant vs lem-sfb-abelian-tate-charpoly: the existing node asserts the rational/integral characteristic polynomial and its independence of ell; it does not identify its constant term with geometric degree, or compare maps from A to another abelian variety B.

lem-sfb-isogeny-relative-tate-determinant vs lem-sfb-abelian-degree-polynomial: the existing node asserts polynomiality and homogeneous scaling of geometric degree on rational endomorphisms; it does not identify that polynomial with the determinant on Tate modules.

lem-sfb-isogeny-relative-tate-determinant vs lem-sc-isogeny-degree: the latter is finite-flatness and equality of geometric rank with the kernel order, with no Tate determinant.

lem-sfb-isogeny-relative-tate-determinant vs lem-sfb-abelian-trace-intersection: the new statement concerns arbitrary homomorphisms A to B and an isogeny used as a denominator, with no line bundle, intersection or trace.

Both new sources are Milne rather than a Stacks tag. DAG statement/title searches and whole-blueprint searches found no duplicate. The existing same-unit top-intersection-multilinearity node is reused rather than recreated. General ample Hilbert positivity and Tate rank are reused as tools, declared in split_report.tool_uses, and projective Hilbert degree/dimension is reused from this unit.

## Review by Q104

I read Milne AV I Theorem 14.3 on printed p.62 and its preceding Rosati definition on p.61; the displayed identity is exactly this item after choosing the cyclic order, and its calculation is explicitly omitted. I read Theorem 11.1(a),(b) on printed p.54 for the first new node: degree(phi_N) = chi(N)^2 and chi(N) = (N^g)/g!. This has no ampleness assumption, which is essential because f^*L can be degenerate. I read the degree-zero convention before Theorem 10.9 on p.46. For the second new node I read Proposition 10.20 and its proof on printed pp.50–52, Remark 10.11 on p.47 for the rational extension and Remark 8.6 on p.36 for integral multiples of inverse isogenies. Its relative form follows by choosing an integral map nu = n mu: both nu h and nu lambda are endomorphisms of A, determinant equals degree for those endomorphisms, and dividing cancels deg(nu). For non-isogenies both degree and determinant are zero. This is a general relative-degree input, and does not smuggle in the desired trace identity.

For step 1 I opened and read every cited statement. def-sc-ample gives a very ample power. lem-sfb-projective-hilbert-polynomial-dimension gives degree exactly dim A for its embedding, hence p(at) has degree g and so does p(t). lem-sc-positive-ample-hilbert-degree then gives positivity of the degree defined by def-sc-hilbert-degree. def-sc-intersection-number identifies S with g! times that degree-g coefficient: expansion of p(t_1+...+t_g) has precisely that mixed coefficient. lem-sfb-top-intersection-multilinear states symmetry and tensor additivity, including duals, so its binomial expansion gives H(r) for positive, zero and negative integers r. I also read Stacks varieties.tex definition-intersection-number (0BEP), lemma-intersection-number-additive (0BER) and lemma-ample-positive (0BEV) to check the normalizations against the reused nodes. The degree-exactly-g justification was added during self-review, since positivity of a merely leading coefficient alone would not justify this identification without that degree check.

For step 2 I read the whole statement of lem-sfb-abelian-polarization-calculus: it supplies both the normalized representing family, whose tensor identity proves additivity in the sheaf, and the actual formula phi(f^*L) = f-dual phi(L) f. This proves h_r = r lambda + f-dual lambda f as morphisms, not just on k-points. The degree-square node applied to L itself, together with S>0 and its explicit zero convention, proves that lambda is an isogeny and computes its nonzero degree. The given two-sided inverse mu is therefore exactly the inverse required by the relative determinant node; no new inverse or changed hypotheses are introduced.

For step 3 I read prop-av-tate-rank, which actually states V_ell A is Q_ell^(2g) under our algebraically closed and ell-invertible hypotheses. I read sk-def-av-tate, which defines the inverse limit and componentwise action; additivity, identity and composition are written coordinatewise and survive tensoring. I inspected the project TateModule.lean componentwise map, identity and composition declarations for agreement. The two new cited statements give respectively det(mu h_r) = d(h_r)/deg(lambda) and d(h_r) = (H(r)/g!)^2 for every r, including those where h_r is not an isogeny. Cancelling factorials gives H(r)^2/S^2. Equality of the polynomials follows by the elementary root bound over characteristic-zero Q_ell, with no analytic density assumption on the integers.

For step 4 I read def-weil-endomorphism-trace; it defines the trace as the sum of diagonal entries. The determinant permutation expansion is written out at the coefficient actually needed. Comparing it to the coefficient of the square of H gives the factor 2g, with the denominator already known nonzero. No non-elementary fact is hidden behind a definition citation here: the coefficient argument is explicit. All citations have literal full-statement quotes in citations.json. Each proof step is under 2000 characters; neither new node has a proof sketch in its statement, proof entries or proof dependencies.

I tested f=0 (H = S X^g and trace zero), f=id (H = S(X+1)^g and trace 2g), f=[n] (mixed intersection n^2 S and trace 2g n^2), and a projection on a product of elliptic curves (possibly non-isogeny, handled by the zero convention). The first new statement includes N trivial or algebraically trivial, where phi_N and the self-intersection both vanish; on an elliptic curve it reduces to degree(phi_N) = degree(N)^2 even for negative degree. The second new statement gives 1 for h=lambda, 0 for h=0 in positive dimension, and n^(2g) for h=n lambda. Inseparable isogenies are permitted: kernel order is scheme-theoretic, not the number of k-points. No prime-to-degree hypothesis is added; only ell != char k is used. Dimension zero is deliberately excluded in both prerequisites, matching this item's positive dimension and avoiding unnecessary conventions.

The B–E audit found no hollow definition, no clause relabelled as a node, no use of another node's proof instead of its statement, no changed route, no cycle or weakened hypothesis, and no SGA source. The server check_dag already reported no finding introduced by this overlay. The required delivery dry run is the final mechanical gate before pushing.

## Unfinished work

The two new prerequisites remain unsplit, exactly as required for a one-level stage-1 split. There is no Lean work in this delivery, and no compiler, Lake or build command was run. All writes are confined to the designated sandbox. No repository or launcher file was edited.
