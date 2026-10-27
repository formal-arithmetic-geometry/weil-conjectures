## Worker report

The module `Sheaf.Algebra.GeneratorFiltrationGradedModule` states
`Module.generatorFiltrationGradedModule`, with `sorry` as its entire proof. The auxiliary
definition `Module.generatorFiltration` has actual data: the specified Mathlib submodule span.
The item's statement, proof and proof dependencies are unchanged. Its statement dependencies
gain only `def-trf-generator-filtration`.

The source places read are Stacks Algebra Tag 052N, `lemma-homogenize`, including its module
construction, and More Algebra Tag 053E, proof of (2), including passage to a polynomial ring
and torsion-freeness. This node is the accepted explicit generator-filtration variant rather
than a transcription of the source's cokernel model. I also read the current blueprint's
`sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md` for the ancestor route.

Hypotheses and clauses correspond as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A and B commutative, B an A-algebra | `CommRing A`, `CommRing B`, `Algebra A B` |
| M a B-module, regarded as an A-module | `AddCommGroup M`, `Module B M`, `Module A M`, `IsScalarTower A B M`; the tower says the A-action is the restricted action |
| n,r nonnegative and the chosen b and m | `n r : ℕ`, `b : Fin n → B`, `m : Fin r → M` |
| Those exact b generate B as an A-algebra | `hb : Algebra.adjoin A (Set.range b) = ⊤` |
| Those exact m generate M over B | `hm : Submodule.span B (Set.range m) = ⊤` |
| The specified F_d | `generatorFiltration A b m d`: the A-span of `(∏ i, b i ^ α i) • m j` with `∑ i, α i ≤ d` |
| N, finite formal polynomials with coefficients in F_d | Mathlib `⨁ d : ℕ, generatorFiltration A b m d`; its dependent finitely supported coefficients are exactly this formal direct sum |
| F_d contained in F_(d+1) | existential proof `hF : ∀ d, ... ≤ ...` |
| b_i F_d contained in F_(d+1) | existential proof `hB`, quantified over `x : generatorFiltration ... d` |
| Union of F_d is M | `∀ x : M, ∃ d : ℕ, x ∈ generatorFiltration A b m d` |
| P=A[X_0,...,X_n] | `MvPolynomial (Option (Fin n)) A`: `none` is X_0, `some i` is the remaining variable |
| Formulas define the P-module structure | existential `modN : Module P N`, with explicit constant compatibility and both variable equations on every `DirectSum.of ... d x` |
| Constants retain the A-action | `@SMul.smul _ _ modN.toSMul (MvPolynomial.C a) z = a • z` |
| X_0(xt^d)=xt^(d+1) | the equation for `MvPolynomial.X none`; `hF` supplies only the codomain membership proof |
| X_i(xt^d)=b_i x t^(d+1) | the equation for `MvPolynomial.X (some i)`; `hB` supplies the membership proof |
| G_d=F_d t^d for d nonnegative, zero for negative d | `G d = if 0 ≤ d then LinearMap.range (DirectSum.lof ... d.toNat) else ⊥` |
| The grading is internal | `DirectSum.IsInternal G`, bijectivity of the canonical map from the direct sum of components |
| P_e N_d contained in N_(e+d) | quantified `p : MvPolynomial.homogeneousSubmodule ... e`, `z : G d`, and membership of their action in `G ((e : ℤ) + d)`; `e : ℕ` is the standard polynomial grading (negative polynomial components are zero), while d ranges over all integers |
| Named degree-zero generators | `g : Fin r → generatorFiltration ... 0` with `(g j : M) = m j`, followed by `∀ z, ∃ c : Fin r → P, z = ∑ j, c j • DirectSum.of ... 0 (g j)` |
| If A is a domain and M is A-torsion-free, N is A-torsion-free | the last implication, with `IsDomain A` and injectivity of multiplication by each nonzero `a` on M and N |

The two finite-generation hypotheses are the witnesses required by the dependency notions;
adding separate finite-type or finite-module class premises would repeat information. The
existential grading is fixed by its explicit component equalities. The existential module
structure is fixed by its constants and variables on every direct-sum summand, which generate
additively. Thus no arbitrary map, choice of a module with unspecified action, or hollow
definition replaces the prescribed construction. The degree-zero lifts are also fixed by
their displayed values; they merely supply membership proofs for the named generators.

Dependency declarations inspected and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (the recorded finite-type declaration),
  `Algebra.FiniteType`, and `Algebra.adjoin`; the explicit `hb` records the chosen algebra
  generators rather than forgetting them into the finite-type predicate.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`; its finite-span definition is rendered
  by `hm` for the supplied module generators, and the conclusion gives an explicit spanning
  expression over P for exactly those generators.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`; polynomial variables, constants, and their universal property
  underlie the polynomial action. The proof uses the monomial construction in the node.
- New node `def-trf-generator-filtration`, module `Sheaf.Algebra.GeneratorFiltration`,
  declaration `Module.generatorFiltration`.
- For that new definition, `def-weil-submodule-span` is Mathlib's `Submodule.span` from
  `Mathlib.LinearAlgebra.Span.Defs`, read with its full definition and docstring.
- The grading uses Mathlib's `DirectSum.lof`, `DirectSum.IsInternal` and
  `MvPolynomial.homogeneousSubmodule`, with their source definitions read. The direct-sum
  representation agrees with the already landed `filteredModuleEvaluationPresentation`;
  that downstream theorem is not imported.

Edge cases checked: n=0 gives only X_0, with the empty product equal to one and the empty
sum of exponents equal to zero; no nonempty generator type is assumed. For r=0, `hm` forces
M to be zero, and the conclusion correctly says every element of N is the empty sum. The
zero ring is permitted by the main theorem; the domain hypothesis occurs only in the last
conditional clause. Degree zero includes all m_j with the zero exponent vector. Redundant
or zero generators and relations between the b_i are permitted. The integer grading has
zero components for every negative degree, including d=-1; multiplication into a negative
degree is therefore vacuous. A,B,M have independent universes u,v,w. No characteristic,
Noetherian, valuation-ring, flatness, injectivity-of-A-to-B or independence hypothesis is added.
There is no statement dispute or required correction.

Searches made before writing:

- `msearch.py leanfinder`: “The direct sum of the algebra generator degree filtration on a
  finitely generated module is generated in degree zero over the homogenizing polynomial
  ring” returned graded algebra generation and homogeneous localization results, not this
  specified module or theorem.
- `msearch.py loogle`: `DirectSum.IsInternal, Finsupp.supported, Module.Finite` returned no hits.
- `msearch.py grep`: `generatorFiltration|homogenizedModule|ReesModule|homogeni[sz].*module`
  under `RingTheory` returned no hits.
- `msearch.py leansearch`: “Generator degree filtration and its homogenized module of finitely
  supported coefficients” returned `Ideal.Filtration` and Rees module results. I read the
  definition: this is a decreasing ideal filtration, so it does not define this generator
  filtration. I also read `IsModuleFiltration`; it is a property of a supplied filtration.
- `msearch.py leanfinder`: “A submodule spanned by monomials of bounded total degree in chosen
  algebra generators acting on chosen module generators” returned `MvPolynomial.coeffsIn`,
  homogeneous submodules and bounded-degree polynomials, not the submodule of M here.
- `msearch.py grep`: `generatorFiltration|generator.*[Ff]iltration` returned no hits.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, the Mathlib tree, and
  `dag/lean_names_upstream.json` found no matching names or construction. The required search
  for the item id in `lean/WeilConjectures` found no declaration. DAG searches found the item,
  its parent, and the filtered-module-evaluation theorem, whose arbitrary input filtration
  is not the defining formula. `tools/blueprint_refs.py search 'generator filtration'` returned
  zero blueprint nodes. All msearch results are copied verbatim as JSON log records in the
  new node's `mathlib_searches`.

Validation: both delivered modules passed separate server compiles through `scompile.py`
against the published live library, with no error or unexpected warning. The sole theorem
has `sorry` as its entire proof; the definition contains no postponed data or proofs.

## New nodes

`def-trf-generator-filtration` defines only the degree submodule spanned by monomials in the
chosen b acting on the chosen m. Its definition is meaningful without generation hypotheses,
so it uses exactly the two scalar structures needed by the formula; the main theorem supplies
the compatible A-algebra setting. It cites the existing span node and reuses `Submodule.span`.
The source is the explicit degree-filtration realization of Stacks 052N and 053E used in the
accepted item's seven-step proof. The semantic searches, Mathlib grep, project-source grep,
DAG search and blueprint search above found no existing definition of this particular span;
the decreasing ideal filtration and the arbitrary filtered-module consumer are different.
No additional definition of a direct sum, polynomial ring, internal grading or module structure
is introduced.

## Second reading by Q70

No second worker reading: this dispatcher assignment requires delivery by the worker and
forbids starting other agents. The maintainer's independent review reads the delivery.
