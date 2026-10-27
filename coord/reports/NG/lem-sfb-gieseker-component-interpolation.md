## Worker report

The new module `Sheaf.AlgebraicGeometry.GiesekerComponentInterpolation` states
`AlgebraicGeometry.gieseker_component_interpolation`, with its sole proof `sorry`.
No definitions, axioms, or additional postponed lemmas are introduced. The node's statement,
source, proof, and proof dependencies are unchanged. Its statement dependencies gain the
already landed `def-weil-pure-dimension`, whose predicate expresses the word “curve”.

Clause-by-clause rendering:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- The numerical assumptions: natural numbers `g d n`, `hg : 2 ≤ g`,
  `hd : 9 * (g - 1) < d`, and `hr : n + 2 + g = d + 1`.
  There are `r = n + 2` coordinates and projective dimension `n + 1 = r - 1`.
  This reparameterization loses no case: the numerical hypotheses force r ≥ 2.
- The embedded connected reduced nodal curve: `D`, `[ConnectedSpace D]`, `[IsReduced D]`,
  closed immersion `i`, `hpure : D.IsPureDimension 1`, and `hnodal` at every point
  outside the smooth locus of its structural morphism `f`. This uses the recorded
  adic completion and two-variable power-series quotient by `uv` verbatim.
  `f` and `hf` name the composite structural map; its finite-presentation instance is
  forced by the projective closed embedding, rather than an additional geometric restriction.
- Hilbert polynomial: `hP : ProjectiveHilbertPolynomial.IsCoordinatePolynomial ...`
  with the rational polynomial `d*X + (1-g)`, the actual homogeneous coordinate polynomial.
- Hyperplane line: `hL` identifies `L` with tensor pullback of the recorded `twist ... 1`.
  Invertibility follows from this isomorphism and the hyperplane twist.
- Complete nondegenerate embedding: `hcomplete` says the actual coordinate-section map
  `k^r → Γ(D,L)` is bijective. Its summands are pullbacks of `twistOneSection` through
  the section-normalized tensor-pullback adjunction, with structural k-scalar action.
- Dimensions and nonspeciality: `h0` is the finrank of module cohomology in degree zero
  after restriction of scalars along f, equal to `n+2`; `h1` is subsingleton degree-one
  module cohomology. This does not silently substitute abelian-sheaf cohomology.
- Weighted flags and their leading coefficients: `ρ` and `hρ` give the exact same
  chart-normalized polynomial restriction arrows as the dependency theorem. `a` is a
  function of bases of `BoundedHilbertWeight.LinearForms` and natural integral weights.
  `ha` characterizes each coefficient by an eventual quadratic estimate with linear
  error for the recorded minimum `BoundedHilbertWeight.weight`. This is equivalent
  to taking the coefficient supplied by the dependency: a quadratic coefficient with
  O(m) error is unique. Existence of these arrows and estimates follows from that
  dependency. No unconstrained replacement map or weight is used.
- The leading-weight hypothesis is `hweight` for every basis and every weight function
  with `w j ≤ 4`. Natural weights encode exactly the integers 0 through 4. Its right
  side is `(d : ℚ)/(n+2) * ∑ j, w j`. The asymptotic characterization also makes `a`
  independent of compatible basis, because the recorded weighted monomial minimum
  is flag-dependent; it does not impose another semistability assumption.
- Arbitrary reduced union Y: `S : Set (Set D)` with `hS : S ⊆ irreducibleComponents D`.
  Its support is `⋃₀ S`. Every such subset of components is permitted, without
  nonemptiness, properness, or connectedness restrictions. A reduced component union
  is uniquely determined by this support, and the conclusion uses only that support.
- A component E of the normalization of the reduced complement: an arbitrary integral
  scheme `T` with a closed immersion `j`, image an irreducible component (`hT`),
  outside `S` (`houtside`); E is its canonical `T.normalization`. This parametrizes
  precisely the normalized components of the complementary reduced union, up to its
  unique isomorphism over the integral component; it also avoids arbitrary normalization data.
- Degree on E: `e : ℤ` and `he` use exactly `Scheme.Modules.degree` on E with structural
  map `T.fromNormalization ≫ j ≫ f` and tensor pullback of L.
- Boundary count: `hb` sets b equal to the ncard of the inverse image of `⋃₀ S`
  under `T.fromNormalization ≫ j`. Since T is outside S and D is nodal, these are
  exactly the distinct preimages of nodes attaching T to Y; self-nodes and nodes
  between other complementary components are excluded. This set is finite by the
  nodal boundary theorem, so ncard does not replace an infinite count by zero.
- First alternative: `(b : ℤ) ≤ e`.
- Second alternative: `IsIso T.fromNormalization` says E maps isomorphically onto T;
  `e = (b : ℤ)-1` is the asserted degree. The existential k-isomorphism φ to P¹,
  together with the isomorphism of the given hyperplane line to φ-pullback O(e),
  and surjectivity of ambient coordinate forms onto its sections, expresses that T
  is a smooth rational curve embedded in its own span by the complete degree-e
  system. This is exactly the stated rational-normal convention. The statement
  does not strengthen the exception to e=1, although the proof plan derives that.

Dependency declarations read and used:

- Mathlib `Field`, `IsAlgClosed`, `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsReduced`,
  `AdicCompletion`, and `MvPowerSeries`, from their recorded defining files.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist` and `twistOneSection`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology` and `globalSectionsFunctor`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree` (difference of Euler characteristics).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `fromNormalization`.
- `Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials`:
  `AlgebraicGeometry.BoundedHilbertWeight.exists_uniform_bounded_hilbert_weights`;
  its public dependency `WeightedMonomialBasisWeight` supplies `LinearForms`,
  `sections`, `flag`, `IsMonomialBasis`, `totalWeight`, and `weight`.
- The preceding modules publicly expose the actual coordinate Hilbert polynomial
  (`ProjectiveHilbertPolynomial.IsCoordinatePolynomial`), the section-normalized
  tensor-pullback adjunction, and `UniformProjectiveFibreVanishing.cohomology` and
  `zeroSections`. Their defining source and signatures were read.
- Added existing node `def-weil-pure-dimension`:
  `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`.

All recorded proof-dependency modules are imported without `public` (apart from
EulerChar and BoundedHilbertWeightPolynomials, also used by the statement). The three
proof nodes without a Lean module (`lem-weil-pbc-finite-type-over-noetherian`,
`lem-sfb-projective-hilbert-polynomial-dimension`, and
`lem-sfb-subcurve-span-weight-bound`) are not invented or replaced; the first is a Mathlib
leaf covered by the Noetherian/QuasiCompact imports, and the latter two await statement
attachments. They are named explicitly in the full nine-step natural-language proof docstring.

Edge cases checked: Y empty has b=0 and the positive-degree first alternative; Y all
components leaves no T satisfying houtside. Disconnected Y is admitted by an arbitrary
subset S. Irreducible D only has the empty-union case. A rational bridge line has b=2,
e=1, and the stated exception. A rational tail line has b=1 and satisfies the first
alternative. Normalization preimages distinguish branches, whereas a self-node outside
Y contributes none. The identity normalization and smooth components are admitted.
The smallest genus is 2; strict d>9(g-1) gives r≥2 and no lost small ambient cases.
No restriction on characteristic or extra independent field universe occurs.

Searches made (all in the assigned read-only trees; no Git commands):

- msearch.py leanfinder: “On a nodal curve satisfying leading Hilbert weight inequalities,
  each normalized complementary component has degree at least its boundary count except
  a rational normal component of degree one less”: eight unrelated hits, headed by
  `ChevalleyThm.degBound` and Weierstrass division-polynomial bounds; no exact statement.
- msearch.py loogle: `Scheme.normalization, Scheme.Modules.degree`: zero hits,
  unknown identifier `Scheme.normalization` in the Mathlib search service.
- msearch.py grep: `rationalNormal|componentInterpolation|gieseker`, subdirectory
  AlgebraicGeometry: zero hits.
- rg in project Sheaf and WeilConjectures for `gieseker`, `HilbertWeight`,
  `rationalNormal`, `rational.normal`, `componentInterpolation`: found the weight
  dependency and the potential-stability consumer, not this statement. Full relevant
  modules were read. Upstream grep for this blueprint id returned no matches.
- DAG search for rational normal curves found the integral-curve span-rigidity and
  subcurve-span-weight nodes, neither with a Lean attachment and neither this theorem.
  The rational-normal condition is rendered directly in the theorem, so no duplicate
  independent definition or missing-notion node was introduced.

Source verification: opened https://arxiv.org/pdf/0810.2340, printed p.14, step (9),
which states the component alternatives, as well as Definition 7 and Theorem 8.
The statement is the node's existing leading-weight formulation, not a correction.
No STATEMENT-DISPUTED flag and no dependency-interface repair.

Validation: scompile.py compiled the sandbox file and its canonical library module
separately, cleanly, in 9.7 s and 8.3 s. One preliminary elaboration error in the
component coordinate-section sum was repaired with the prescribed explicit `@id`
section type; no hidden `let` or `show ... from` appears in the signature.

## Second reading by NG

The dispatcher forbids starting other agents. This is a separate in-thread rereading,
not a claim of independent-agent review; the maintainer's independent delivery review
remains necessary. I reopened the complete node and the final signature and checked:
all numerical and field binders, closed embedding, curve purity, connectedness,
reducedness, the completed node model, exact coordinate polynomial, hyperplane
identification, actual coordinate bijectivity, H⁰/H¹, all 0..4 weighted bases and their
canonical restriction/asymptotic characterization, arbitrary component subsets,
normalized-component degree, branch inverse-image count, both alternatives and the
complete own-span rational-normal condition. No mismatch found. In particular the
exception has an actual k-isomorphism and a line-bundle isomorphism, rather than just
vanishing genus or a dimension inequality. The node only gains the landed purity
notion in stmt_deps and the Lean attachment; its mathematical statement is unchanged.
