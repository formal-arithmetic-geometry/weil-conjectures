## Worker report

The module `Sheaf.AlgebraicGeometry.HilbertMonomialNumericalCriterion` states
`AlgebraicGeometry.HilbertPlucker.stable_iff_monomial_numerical`. Its sole theorem
has proof `sorry`. Seven plain helper definitions give the actual section space,
polynomial expansion and restriction of a monomial in an arbitrary basis, the
predicate that a finite monomial set restricts to a basis, its rational weight,
the finite set of basis-weight sums, and their minimum. No definition selects data
from an existence theorem. No statement correction or dependency repair is needed.

Hypothesis and clause correspondence:

- The field k is `k : Type u`, `[Field k]`, and `[IsAlgClosed k]`.
- The integer r >= 2 is parametrized exactly as r = n + 2, with n : Nat, following
  `HilbertPlucker.Coordinates`. The coordinate model E = k^(n+2) represents an
  arbitrary r-dimensional vector space after a linear identification. The embedding
  and all bases transport under that identification; no distinguished basis is
  required by the criterion. Every ordered basis is explicitly tested as
  `b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k)`.
- The admissible coordinate Hilbert polynomial is `P : NumericalHilbertPolynomial`.
  `D : Hilbert k n P` is the recorded representing polynomial component, not an
  arbitrary scheme. `x : PGLLinearization.fieldTest k k ⟶ D.H` is an arbitrary
  rational Hilbert point. Its embedded closed subscheme is exactly the pullback
  of `D.ideal`; the component property in `D` imposes coordinate polynomial P.
  Quantifying over supplied representatives and points imposes no condition on X
  beyond the Hilbert datum. The representation classifies all such closed subschemes.
- The sufficiently large degree is `m : Nat` supplied with
  `E : HilbertPlucker.Presentation D m`. This is precisely the embedding data that
  `exists_hilbert_plucker_pgl_linearization` supplies for every m >= M(P,r).
  We do not make a noncanonical choice of M, embedding, or determinant action.
  A natural degree is the nonnegative integer degree of Sym^m and the Hilbert
  embedding in that recorded declaration. All permitted degrees are covered.
- The restricted O(1), its mth power, and H^0 are the dependency's
  `HilbertPlucker.sections D m`, pulled back at x. `pointSections` is its actual
  global section module. The `Presentation.base_change` clause identifies this
  fibre with H^0(X,O_X(m)); thus it is the prescribed Q, not an arbitrary quotient.
- `basisMonomial` expands product_i b_i^(alpha_i), using the full degree-m exponent
  type `RelativeProjectiveSpace.monomials (n+1) m`. `basisMonomialRestriction`
  sums its polynomial coefficients times the pullbacks of the dependency's
  `monomialRestriction`. `E.monomials` enumerates every monomial bijectively;
  therefore no exponents are omitted. The scalar map is the canonical
  `(Scheme.ΓSpecIso (.of k)).inv.hom : k →+* Γ(Spec k, top)`.
- `IsMonomialBasis` asks for a basis indexed by exactly a finite set of those
  monomials and equal to their restrictions. Using Γ(Spec k) as coefficient ring
  is exactly using k through the displayed canonical isomorphism.
- The weight of a monomial is `monomialWeight w a = sum_i (alpha_i : Rat) * w i`.
  `basisWeights` forms all sums over finite monomial bases. `minimumBasisWeight`
  takes their finite minimum. The default 0 only totalizes the definition on an
  empty collection; on any supplied Hilbert presentation surjectivity and base
  change make the collection nonempty for every basis. No nonempty collection or
  arbitrary minimum is assumed as extra data.
- The left side is the existing geometric predicate `E.sl_line.IsStable k x`,
  for the actual determinant linearization on `determinant D m E.p`.
  This predicate means semistability by positive-power invariant sections,
  a closed orbit inside the semistable locus, and dimension-zero full
  scheme-theoretic stabilizer. It does not use tangent dimension.
- The right side quantifies over every basis and every rational tuple w.
  `(exists i j, w i != w j)` is exactly nonconstancy. The comparison is strictly
  `<`, and its right side is `(sum_i w i)/(n+2) * m * P.eval m`, with every
  operation performed over Rat. `E.value` identifies the determinant rank with P(m).
- The equivalence is an iff. There is no smoothness, reducedness, dimension,
  characteristic-zero, or separability assumption on X or on its stabilizer.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (the declaration underlying def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`:
  `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`, the eventual dimension
  predicate of the actual coordinate pieces. It is used in the recorded Hilbert
  component convention, not redefined here.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`, the canonical integral-model twist.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `RingedSpace.moduleCohomology`.
  Only H^0 is at issue: it is written directly as actual global sections, as in
  the supplied Hilbert embedding, rather than introducing a derived-cohomology copy.
- `Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization`: `Hilbert`, `Hilbert.H`,
  `Presentation`, `sections`, `monomialRestriction`, `determinant`,
  `exists_hilbert_plucker_pgl_linearization`. The complete structure signatures and
  docstrings were read, including the rank, base change, monomial enumeration,
  determinant generator formula and stable-points clauses.
- `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`:
  `GroupSchemeLinearization.Linearization.IsStable`, reached through E.sl_line.
- The stated proof prerequisite
  `Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis` is imported without public;
  its `GmRepresentation.weightDecomposition_and_basis` signature and docstring were
  read. The other proof prerequisite
  `lem-sfb-hilbert-mumford-projective-representation` has no recorded declaration
  in the current DAG, hence no module can yet be imported for it. Its mathematical
  role remains explicit in the theorem's four-step proof docstring.

Sources and searches:

- Read the DAG statement and all four proof steps, all seven statement dependency
  records and their declared interfaces, and the two further proof prerequisites.
  Opened Morrison https://arxiv.org/pdf/0810.2340, Section 2.2, Proposition 1 and
  the determinant-coordinate and weight-normalization discussion on printed pp.5--7.
- msearch.py leanfinder query: "Hilbert point geometric stability equivalent to
  strict monomial basis weight inequality for every nonconstant weighted basis".
  Eight hits: weighted homogeneous polynomials, non-torsion weights and Lie-module
  weight spaces; none states Hilbert stability or the monomial numerical criterion.
- msearch.py loogle query: "MvPolynomial, Module.Basis, LinearIndependent".
  Zero hits.
- msearch.py grep query: "Hilbert.*[Ss]tab|monomial.*[Bb]asis|monomial.*[Ww]eight"
  in Mathlib/AlgebraicGeometry. Zero hits.
- rg of Mathlib, lean/WeilConjectures and lean/Sheaf for
  "hilbert.monomial|monomial.numerical|monomialWeight|monomialBasis|minimumWeight"
  found no existing declaration. The explicit item-id search in WeilConjectures
  also found none. Broader Hilbert/monomial searches located the recorded
  HilbertPluckerPGLLinearization and RelativeProjectiveSpace APIs used here.

Edge cases checked before writing:

- X empty and P(m)=0: the empty monomial set is a basis of the zero space, the
  minimum is 0, and the strict inequality 0<0 fails. The SL stabilizer has positive
  dimension for r>=2, so the geometric side fails as well.
- Constant weights: every degree-m monomial has weight m*d and every basis has
  P(m) elements. Both sides of the proposed strict comparison would be equal;
  nonconstancy excludes exactly these tuples.
- m=0: the only monomial is 1, with weight 0. Should such a degree admit the
  supplied Hilbert embedding data, the same formula applies; no artificial
  positive-degree hypothesis was added.
- r=2 is included by n=0, so nonconstant tuples and the SL_2 action are present.
- Repeated monomial restrictions cannot be mistaken for a basis: the existential
  Module.Basis forces both independence and spanning on the exact finite set.
- Positive characteristic, nonreduced X and finite nonreduced stabilizers are
  retained by the existing full group-scheme stability predicate. Weights and the
  inequality are rational numbers, not elements of k.

Validation: all compilation uses the prescribed scompile.py wrapper. The first
compile diagnosed the difference between tensorPullback and the pullbackΓ API;
pointSections now uses the same Scheme.Modules.pullback as pullbackΓ. Final compile
and delivery preflight results are recorded by the delivery wrapper.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
