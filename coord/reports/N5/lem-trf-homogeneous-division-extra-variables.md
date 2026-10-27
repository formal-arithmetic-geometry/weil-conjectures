## Worker report

Item: `lem-trf-homogeneous-division-extra-variables`, stage 2, group N5.
Module: `Sheaf.RingTheory.HomogeneousDivisionExtraVariables`.
The two named theorems state the equivalence and its field-extension preservation.
Both proofs are `sorry`; there is no new definition or proved theorem.
The item node is changed only in `lean`; its reviewed Q41/L split is preserved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field L is `{L : Type u} [Field L]`. The three nonnegative integers are
  `{m r s : ℕ}`; none is assumed positive. Variable sets are `Fin r` and
  `Fin m ⊕ Fin r`, with the left summand representing U and the right summand V.
- The ordered list of distinct vertices is `α : Fin s → Fin r →₀ ℕ` with
  `hα : Function.Injective α`. Its order is the ordinary order on `Fin s`.
  No degree-lexicographic, antichain, or minimal-vertex condition is imposed.
  `Finsupp.degree` is the sum of the coordinates, so `(α i).degree` is d_i.
- `H : Fin s → MvPolynomial (Fin m ⊕ Fin r) L` and
  `hH : ∀ i : Fin s, (H i).IsHomogeneous (α i).degree` are precisely the
  generators and their prescribed homogeneous degrees. `IsHomogeneous` includes zero;
  there is no nonvanishing or totalDegree-equality assumption.
- `generated α` is D, by its dependency definition `∃ i, α i ≤ e`.
  `quotientSupport α i` is Delta_i: `∀ j < i, ¬ α j ≤ α i + β`.
  The diagram and quotient supports are the dependency's definitions, not private copies.
- Restriction h_i(V) is the application of `MvPolynomial.eval₂Hom MvPolynomial.C`
  with variable map `Sum.elim (fun _ : Fin m ↦ 0) MvPolynomial.X` to `H i`.
  This fixes all V variables and all coefficients and kills every U variable.
- Condition (i) is the first theorem's left side, `∀ t : ℕ, HasUniqueDivision
  (generated α) α (fun i ↦ ... restriction of H i ...) t`.
  Expanding the recorded `DivisionIndex` gives exactly the left disjoint family
  indexed by `(i,β)` in Delta_i of degree `β.degree + d_i = t`, plus remainder
  monomials outside D of degree t. `divisionFamily` maps these to the stated products.
- Condition (ii) is the right side using vertices
  `fun i ↦ Finsupp.mapDomain (Sum.inr : Fin r → Fin m ⊕ Fin r) (α i)`.
  These are exactly `(0,α_i)`. Its generated set consists of all exponents with
  V component in D: there is no restriction on the U component. The same coordinatewise
  inequality calculation gives quotient support all U exponents times Delta_i.
  `DivisionIndex` therefore imposes `|μ|+|β|+d_i=t` on products and
  `|μ|+|γ|=t` on remainders. Its `divisionFamily` is exactly the stated second family.
- Under `hH`, every indexed vector lies in the homogeneous degree-t submodule;
  restriction and multiplication by monomials preserve the indicated degrees.
  `HasUniqueDivision` says every homogeneous polynomial has unique finitely supported
  coefficients in this indexed family, exactly the algebraic basis condition, including
  linear independence: the zero polynomial has uniquely zero coefficients. It retains
  repeated polynomial values at distinct indices rather than replacing the family by a set.
  Conversely a basis has exactly these unique finite coordinates. No finiteness hypothesis
  is needed beyond the finite variable and vertex sets already specified.
- `hasUniqueDivision_extraVariables_iff` uses `↔`, hence includes both directions
  and the universal quantifier over all degrees, rather than a single selected degree.
- No monotonicity, leading/first-exponent, characteristic, or finite-test hypothesis occurs.
  The generated diagram and supported division are used without `IsMonotone`,
  `IsOrderedVertexFamily`, or `IsFiniteDivisionTest`.
- `hasUniqueDivision_extraVariables_map` has `{E : Type v} [Field E] (f : L →+* E)`.
  A unital ring map from a field is injective, so this quantifies over precisely field
  embeddings and permits every field extension, with no algebra-instance requirement.
  The first conjunct preserves (i) with each restriction mapped using `MvPolynomial.map f`;
  the second preserves (ii) with each H_i mapped coefficientwise. These are precisely
  the node's two preservation assertions. The first theorem, universally quantified over
  its coefficient field, also applies to `fun i ↦ MvPolynomial.map f (H i)` over E,
  since coefficient mapping preserves homogeneity. This yields the equivalence over E
  whether or not either condition held over L. Mapping commutes with specialization at
  U=0, so its restricted polynomials are the mapped h_i as displayed in the second theorem.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, from `def-weil-field` (Mathlib leaf).
- `MvPolynomial`, `Mathlib.Algebra.MvPolynomial.Basic`; `MvPolynomial.aeval`,
  `Mathlib.Algebra.MvPolynomial.Eval`; and `MvPolynomial.algHom_ext`, Basic,
  the polynomial-ring dependency's recorded declarations. The actual restriction is
  the canonical `MvPolynomial.eval₂Hom`, and coefficient mapping is `MvPolynomial.map`,
  both in Eval. These use the recorded polynomial ring and its evaluation interface.
- `MonomialDiagram.generated`, `quotientSupport`, `DivisionIndex`, `divisionFamily`,
  `HasUniqueDivision`, in `Sheaf.RingTheory.SupportedHomogeneousDivision`;
  the whole module and docstrings were read. Only these unconditioned notions are needed.
- Proof import `Sheaf.LinearAlgebra.TriangularChangeOfBasis`, declaration
  `Module.Basis.exists_basis_of_triangular_unit_diagonal` (full signature read).
- Proof import `Mathlib.RingTheory.FiniteType`, which supplies `CommRing.orzechProperty`
  and imports `OrzechProperty.bijective_of_surjective_endomorphism`; full signatures read.
  These are the stated proof dependencies and are not public statement imports.

Edge cases checked before writing and on second reading:

- s=0: generated diagram empty; both indexed families are full monomial families.
- m=0: there are no extra coordinates and the comparison is the identity renaming.
- r=0: there is exactly the zero V exponent. Injectivity allows at most one vertex;
  the empty list and one degree-zero vertex both remain in scope.
- t=0: constants give the usual one-dimensional component; t>0 with no variables gives
  the zero component and the empty coefficient family. Unique coefficients still makes sense.
- A zero generator with a nonempty quotient support gives a zero indexed vector, so both
  basis properties fail, rather than being silently assumed. If its quotient support is
  empty it contributes no indices on either side. Zero H is admitted by homogeneity.
- A degree-zero vertex gives a constant H equal to its restriction. A nonzero constant
  behaves as a unit in a field; a zero constant destroys both properties when indexed.
- m=r=s=1, α_1=1: H=V+U gives bases {V} before restriction and {V+U,U} in degree one;
  H=U restricts to zero and both degree-one basis assertions fail.
- Arbitrary characteristic and independent field universes u,v are retained. There is
  no same-universe restriction or requirement that the field extension be finite.

Searches (no exact existing declaration found):

- msearch.py / LeanFinder: “A homogeneous polynomial division basis remains a basis
  after adding variables and perturbing generators by terms vanishing when the extra
  variables are zero”: eight hits, including submersive-presentation bases, univariate
  polynomial degreeLT bases, `MvPolynomial.basisMonomials`, and `basisRestrictSupport`.
  They are standard bases and do not state the comparison for arbitrary H_i.
- msearch.py / Loogle: `MvPolynomial.IsHomogeneous, Module.Basis`: two hits,
  `LinearMap.toMvPolynomial_isHomogeneous` and `LinearMap.polyCharpoly_coeff_isHomogeneous`,
  neither a supported division comparison.
- msearch.py / Mathlib grep, RingTheory:
  `supported.*division|division.*homogeneous|triangular.*homogeneous`: zero hits.
- msearch.py / LeanSearch: “Homogeneous polynomial division bases are preserved under
  complementary variable perturbations”: eight hits on homogenization, renaming,
  `toPolynomialAdjoinImageCompl`, homogeneous coefficients and homogeneous decomposition.
  None states the node's equivalence or field-extension preservation.
- rg over the project's `lean/WeilConjectures` and `lean/Sheaf` for supported division,
  homogeneous division and the node id found the recorded supported-division definition,
  its finite-test and Hilbert-coefficient consumers, and unrelated blowup chart division.
  No declaration for this comparison exists. In particular `homogeneousDivision` in
  RegularHilbertCoefficientDatum is a prefix property of formal series, not this result.
- The existing stage-1 searches, full accepted proof, and all three statement-dependency
  node records were read. No new definition search/node is necessary.

Source checked: the current blueprint's `sk-i-curve-zero/_section.md`, which is the
ancestor unit, and the explicit Bierstone--Milman PDF linked by the node, Lemma 7.7,
printed pp.263--264 (online pages 56--57). The precise degreewise generality is the
accepted node's agent-written algebraic refinement, not a claim that the paper states
this entire strengthened formulation verbatim. No source correction or dispute is needed.

The inherited BLOCKED ending concerned an unchanged stage-1 item, not a stage-2
statement delivery. Current `coord/brief-stage2.md` §0 explicitly resolves that handoff;
`coord/queue.tsv` lists this item at stage 2 with no Lean declaration. No split change
or released repair note is required. There was no repair note for this item locally.

Validation: scompile.py compiled this file separately in sandbox and real library module
modes against the published live server build (3.8 s and 3.2 s); clean, no errors or
unexpected warnings. Only the expected theorem `sorry`s remain.

## Second reading by N5

A separate second pass by the same dispatched worker reread the node, dependency
implementations and both final theorem signatures; no other agent was started, as the
brief explicitly forbids delegation. This is not claimed to be an independent agent review.
The maintainer's independent review remains the delivery review.

Checked every correspondence above directly against the Lean: finite sets include zero;
α has distinct entries but no unstated minimality or degree order; homogeneity admits
zero; the restriction fixes V; `mapDomain Sum.inr` introduces only zero U coordinates;
its inequalities give exactly the product diagram and quotient supports; the dependency's
sum-index type retains the indexing; the unique-coefficient predicate is exactly the
basis condition because every indexed product is homogeneous. Both directions quantify
over all t. The extension theorem separately preserves each condition and the first theorem
instantiates over the mapped field, so the independent equivalence after any extension
is covered too. E is in an independent universe, f is arbitrary, and no invertibility or
nonzero hypothesis on H was added. Reviewed the six degenerate cases again. No mismatch
was found and no statement correction, dependency repair, or new node was introduced.
