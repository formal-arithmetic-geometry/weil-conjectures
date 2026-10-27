## Worker report

The module `Sheaf.AlgebraicGeometry.CoefficientLocusUniformDivision` states
`AlgebraicGeometry.HilbertCoefficient.coefficient_locus_uniform_division` with one
`sorry`. It constructs the coefficient family, the restricted coefficient matrices,
the exact finite set of functions to invert, and the coefficient order locus. The full prefix division property uses the
recorded `HasUniqueDivision` directly. All definitions have real data. A named public
finite-subtype instance exposes the existing `EssentialVariables` definition to
Lean's finite-instance search. There are no other postponed results.

Clause-by-clause correspondence:

- A characteristic-zero field is `{k : Type u} [Field k] [CharZero k]`.
  `N : Scheme.{u}` and `[IsAffine N]` give the single affine scheme. `hsm`, `hft`,
  `hqc` give smoothness and finite type of its structure morphism, induced by the
  constants of `w`. `hw` is its étale coordinate morphism to polynomial spectrum,
  with `m` coordinate variables. All dimensions may be zero.
- The centered Taylor maps are `T b` with the existing `isTaylorMap` predicate `hT`,
  specifying constant coefficients, constants from k, and each coordinate value
  `w_j(b)+W_j`. These are the canonical maps in the étale setting, explicitly
  bound rather than chosen from a bare existence theorem. Residue fields are the
  actual `N.residueField b`. Points are arbitrary, including nonclosed points.
- The regular functions are `c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)` on the same N;
  their indices are unbounded in γ. `coefficientFamilySeries (T b) c` is the actual
  formal series specified by its W,Z coefficients using the two canonical
  `Finsupp.comapDomain.addMonoidHom` maps. No infinite sum or convergence is assumed.
- `D`, `hD : IsMonotone D`, and `hα : IsOrderedVertexFamily D α` give exactly the
  ordered minimal vertices in the Z coordinates. Their full vertices are the
  existing `fullVertex m (α i)`, so W coordinates are zero. The first-exponent
  hypothesis `hfirst` gives a nonzero coefficient there and zero coefficients
  at every earlier exponent. It explicitly uses `Sum.Lex` for W before Z,
  avoiding Mathlib's unrelated default order on a sum type.
- `coefficientFamilyOrderLocus α c` is exactly S, using actual germs and
  `IsLocalRing.maximalIdeal (N.presheaf.stalk b) ^ (d_i - |γ|)` for every |γ|<d_i.
  `ha` states a∈S. Zero germs satisfy all those ideal-power containments.
- The conclusion chooses one bound function B. Its first clause is the recorded
  `IsFiniteDivisionTest` for every essential-variable-restricted degree prefix.
  `B q` is a finite stabilization bound for that diagram; it is not an extra
  hypothesis. Bounds may be chosen separately for each prefix, just as in the node.
- `restrictedCoefficientForms` is the degree-d_i initial form restricted by setting
  W and every nonessential Z variable to zero. Its coefficients are exactly
  c_iγ for |γ|=d_i and support in the essential variables. At a point of S this
  is precisely the corresponding restricted initial Taylor form.
- `coefficientDivisionMatrix` is a square matrix indexed by degree-t monomials.
  `coefficientColumnExponent` assigns (i,β) to α_i+β and a remainder index to itself.
  Its inverse index is chosen only when an actual preimage exists. On the ordered
  vertex families in the theorem this preimage exists uniquely, because of the
  first-dividing-vertex rule; the definition is total with a zero fallback on
  other inputs. Thus no mathematical matrix is replaced by an arbitrary map and
  no hidden existence theorem with sorry supplies any data.
- `coefficientDivisionTests α c B` contains exactly one order witness c_iα_i for
  each i, and the restricted matrix determinants for every q from 0 to the maximum
  vertex degree and t≤B q. Set/finite-set duplicate removal has no effect on
  inverting functions. Prefixes after that maximum coincide; q=0 includes the
  empty prefix when there are no degree-zero vertices. Only finitely many distinct
  prefixes and finitely many degrees occur.
- The conclusion says every test function evaluates nonzero at a. Its single V is
  the principal open `N.basicOpen (∏ g ∈ coefficientDivisionTests α c B, g)`, and
  explicitly a∈V. Inverting this finite product is the same as inverting all the
  listed functions. No unrelated auxiliary open or function is introduced.
- The matrix-entry clause explicitly states that every tested entry is 0, 1, or
  c_iγ with |γ|=d_i. These c_iγ are precisely coordinate derivatives of order zero
  divided by 0!=1. The order witnesses are their Taylor coefficients at exponent
  (0,α_i), of total degree d_i. This is the particular allowed choice in proof
  step 2, rather than introducing additional positive-order derivative witnesses.
  Restricted determinants need no positive-order W derivatives because W=0.
- For every b∈S∩V, the first conclusion is `(coefficientFamilySeries ... i).order =
  ((α i).degree : ℕ∞)` for every i, using Mathlib's total order convention so zero
  series have infinite order.
- The next clause states `HasUniqueDivision` for the actual restricted initial
  forms in every q,t. The next explicit `∀ q t` clause states full division in all
  (W,Z) variables, with `prefixVertices`, `generated`, and `HasUniqueDivision`.
  Degree-d_i initial polynomials use polynomial homogeneousComponent after
  truncation at d_i+1, which retains every coefficient of degree exactly d_i.
  The recorded definition gives exactly the first-vertex quotient supports and
  remainder outside the prefix diagram, with unique finitely supported coefficients.
- The last clause quantifies over any `K : Type v` with `[Field K]` and ring map
  j:κ(b)→K, with an independent universe v. It states the same order equalities,
  full division, nonvanishing of the same finite tests, and restricted division
  for the coefficientwise mapped forms. The construction is coefficientwise,
  so both restrictions and the test matrices commute with this map. There is no
  restriction to algebraic extensions or rational/closed points.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, Γevaluation,
  the intrinsic stalk and its germ maps.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `.Derivative`, `.Order`, `.Trunc`:
  `MvPowerSeries`, `MvPowerSeries.pderiv` (through the reused coefficient-datum
  interface), `MvPowerSeries.order`, `MvPowerSeries.truncTotal`.
- `Mathlib.Algebra.MvPolynomial.Basic` and homogeneous modules: `MvPolynomial`,
  coefficient maps, monomials, and `MvPolynomial.homogeneousComponent`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.LinearAlgebra.Matrix.Defs` and determinant modules: `Matrix`, `Matrix.det`,
  the matrix realization of the recorded determinant notion `LinearMap.det`.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`: `IsMonotone`,
  `IsOrderedVertexFamily`, `generated`, `DivisionIndex`, `divisionFamily`,
  `HasUniqueDivision`, `IsFiniteDivisionTest`, `prefixVertices`, `EssentialVariables`,
  `essentialVertices`. The support is not redefined privately.
- Added landed definition dependency `def-trf-regular-hilbert-coefficient-datum`:
  `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`, specifically
  `AlgebraicGeometry.HilbertCoefficient.isTaylorMap` and `.fullVertex`. The entire
  datum is NOT assumed, since that would assume the conclusion under construction.
- Proof-only imports: `Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness`,
  `Sheaf.RingTheory.InitialDiagramStabilization`,
  `Sheaf.RingTheory.HomogeneousDivisionExtraVariables`,
  `Mathlib.LinearAlgebra.Determinant`. Their recorded theorem signatures and proof
  docstrings were read. The derivations-jacobian proof dependency has no current
  Lean record/module, so no speculative import is added for it; its statement
  is not needed to type this theorem because all selected witnesses and restricted
  entries are order-zero derivatives. Its missing proof interface is stage-3 work.

Edge cases checked before writing and during the final reading: s=0 leaves no
order witnesses and all division matrices are identity matrices; n=0 has only the
zero exponent; m=0 still permits the coefficient field itself as a zero-variable
series ring. With no essential variables positive-degree matrices have empty
indices and determinant 1. Degree zero retains the constant monomial and permits
a degree-zero vertex; its nonzero constant gives order zero. A finite prefix may
be empty. Coefficients may vanish or have arbitrarily high order; zero is handled
by ℕ∞. An empty N cannot have a point a and so is correctly vacuous. Nonclosed
points and arbitrary residue-field extensions are retained. No counterexample or
statement fault found; no statement correction needed.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "finite open tests for uniform Taylor orders and unique
   supported homogeneous division along a coefficient order locus"`: eight hits,
   analytic `HasFTaylorSeriesUpToOn`, `HasFTaylorSeriesUpTo`, and related analysis
   Taylor lemmas. None is this algebraic multivariate finite-openness assertion.
2. `msearch.py ... loogle "MvPowerSeries, Matrix.det"`: zero hits.
3. `msearch.py ... grep "Taylor|coordinateDeriv|initialExponent" RingTheory`: seventeen
   hits, including polynomial Taylor formulas in Henselian and standard-étale ring
   files; no finite regular Taylor-family homogeneous-division result.
4. `msearch.py ... leansearch "uniform order and supported homogeneous division of
   Taylor expansions of regular coefficient functions on a finite principal open
   neighborhood"`: eight hits, all analytic Taylor-series results, none matching.
5. `rg` in `lean/Sheaf` and `lean/WeilConjectures` for Taylor maps, initial exponents,
   and coordinate derivatives found and led to reading RegularHilbertCoefficientDatum,
   FormalInitialDiagram, ImplicitTaylorCoordinateCalculus, FormalHilbertStratumMinors,
   DiagonalTaylorFaithfulFlatness, and SupportedHomogeneousDivision. No existing
   declaration states this node. The exact node-id search in WeilConjectures had no
   hit. Helper-name searches in both trees had no hit.

Source read: current blueprint `literature/blueprint/latest` and its ancestor
local-term-locality route, and BM 1997 pp.263–264, 273–275, 282 online at
https://www.mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf .
The p.282 completion supplies precisely the order locus, finite open homogeneous
tests through the stabilization bound, and extension to all degrees. The node's
explicit finite-function refinement is implemented using its six-step proof.

Validation: `scompile.py Q51 lem-trf-coefficient-locus-uniform-division <file>`
compiled both the sandbox and the actual module successfully (2.2 s each), with
no errors or non-sorry warnings. `autoImplicit false` binds every variable.

## Second reading by Q51

A separate final self-audit was made with the full node and the final module open;
no independent worker was launched because the dispatch brief forbids other agents.
I rechecked the field/characteristic, smooth affine finite-type scheme, chart,
arbitrary residue fields, infinite coefficient index, W-before-Z first exponent,
maximal-ideal order locus and center membership against the theorem binders. Every
conclusion is represented: finite functions, actual open containing a, exact orders,
restricted finite matrices and their permitted entries, stabilization, all full
prefix degrees, the required supports and uniqueness, empty cases and extension
of residue fields. The final audit retained `Sum.Lex` explicitly and verified that
all determinants set the complementary variables to zero. The finite q range
represents every distinct prefix. The only compile repair exposed finiteness of
the essential-variable subtype with an actual public instance; it added no hypothesis.
The full division conclusion is written directly with the dependency predicate,
without a second definition of the existing homogeneous-division notion.
No mathematical statement change was made. The precise single degree-d_i witness
per i is c_iα_i, as allowed and used in the node's own proof step 2.
