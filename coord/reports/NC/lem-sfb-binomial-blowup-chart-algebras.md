## Worker report

Item: lem-sfb-binomial-blowup-chart-algebras. Module:
`Sheaf.AlgebraicGeometry.BinomialBlowupChartAlgebras`.
Main declaration:
`AlgebraicGeometry.BinomialBlowup.binomial_blowup_chart_algebras`.
The node's statement and dependency lists are unchanged. One postponed theorem, with
its complete eight-step natural-language proof in its docstring, states the entire node.
All 23 helper abbreviations/definitions have explicit data. They name the rings, coordinate
classes, canonical chart maps, and closed-chart maps occurring in this same statement;
none asserts an independent missing mathematical notion or chooses data from a theorem.
No new nodes or dependency-interface repairs are needed.

Notation in the file: indices 0, 1, 2 are the first, middle, third charts. In the corresponding
presentation the two coordinate classes are (x,t), (r,s), (y,h). `Ring R c` is literally
`MvPolynomial (Fin 2) R` modulo the principal ideal `(X 0 * X 1 - C c)`.
`chartVariable R a n e i j` transports coordinate j by presentation isomorphism e i.
The equivalences are ring equivalences together with their coefficient formulas, hence
are precisely R-algebra isomorphisms, without requiring a new scalar-tower instance.

Hypotheses and every clause of the node are rendered as follows:

- R a domain: `(R : Type u) [CommRing R] [IsDomain R]`, with an arbitrary explicit universe.
- Nonzero parameter and n at least two: `(a : R) (ha : a ≠ 0) (n : ℕ) (hn : 2 ≤ n)`.
- A=R[x,y]/(xy-a^n): `Base R a n = Ring R (a ^ n)`; x,y are `coord ... 0,1`.
- I=(x,a,y): `center` is the span of `Set.range generator`, with
  `generator = ![x, algebraMap R A a, y]`. There are no extra generators or assumptions.
- Ambient Frac(R)(x): `Ambient R = RatFunc (FractionRing R)`.
  The injective R-algebra hom `baseEmbedding` sends x to `RatFunc.X` and
  y to `algebraMap R (Ambient R) a ^ n / RatFunc.X`.
- The standard fraction algebras are the published `AffineBlowup.chartRing`, specialized
  to the actual centre and its three generators; `Chart` is only an abbreviation of it.
- Three forward isomorphisms: `e i : Ring R (parameter R a n i) ≃+* Chart R a n i`,
  where `parameter = ![a, a^(n-2), a]`. The coefficient compatibility conjunct gives the
  R-linearity. Each `embedding i` is injective, and its restriction along A -> Chart is
  `baseEmbedding`. Thus their composites with e i really are the asserted injective
  presentation maps into the same rational-function field.
- First forward coordinate images x,t: respectively `RatFunc.X` and a/x, in the two
  `embedding 0 (chartVariable ... 0 j)` equations.
- Middle forward coordinate images r,s: x/a and (a^n/x)/a, in the two embedding-1 equations.
- Third forward coordinate images y,h: a^n/x and a/(a^n/x), in the embedding-2 equations.
- The formulas y=x^(n-1)t^n and y/x=x^(n-2)t^n are the first `algebraMap ... coord ... 1`
  equation and `z 0 2` equation. The symmetric two equations give x and x/y in the third.
- `z i j` is the actual c/b chart element: its coercion to `Localization.Away generator_i`
  is exactly `AffineBlowup.chartFraction generator_i 1 generator_j`. It is not an
  arbitrary choice of an overlap function; this equality determines its subtype value.
- Rees standard opens: `chartOpen` is `Proj.basicOpen` of the actual `reesX` at each
  generator. Membership in I is supplied by `Ideal.subset_span ⟨i,rfl⟩`.
- The maps to the blowup: `chartMap` is Spec of the published theta equivalence, followed
  by the published `AffineBlowup.chart`. `Set.range chartMap = chartOpen` identifies
  these with the standard charts. The `iSup chartOpen = ⊤` conjunct states their cover.
- Every overlap, including b=c: `∀ i j, chartMap i ⁻¹ᵁ chartOpen j =
  PrimeSpectrum.basicOpen (z i j)`. This is the literal scheme-theoretic principal-open
  description on each actual chart, not just an equality of formal coordinate expressions.
- The adjacent inverted coordinates: `z 0 1=t`, `z 1 0=r`, `z 2 1=h`, `z 1 2=s`.
- First--middle transition: f is an equivalence from the middle localization at r to
  the first localization at t. It maps r to `IsLocalization.Away.invSelf t` and s to
  x^(n-2)t^(n-1). The global middle equation x=a*r supplies the third displayed formula.
- Third--middle transition: g maps middle localized at s to third localized at h,
  with s=h^-1 and r=y^(n-2)h^(n-1). The middle equation y=a*s gives its third formula.
- The transition maps are the actual gluing maps: the Spec.map(f) and Spec.map(g)
  composition equations commute with `overlapMap` into the blowup. Since they are
  equivalences, their inverse transitions are included, without selecting arbitrary maps.
- First--third overlap: `z 0 2=x^(n-2)t^n` and `z 2 0=y^(n-2)h^n`. h is an equivalence
  of these two localizations commuting with the maps to the blowup. Its formulas are
  y=x^(n-1)t^n, h=t/q and, inversely, x=y^(n-1)h^n, t=h/q'. Here q=y/x, so t/q=a/y
  by the already specified embeddings; the latter formula is valid without inverting
  y in a quotient ring. Both symmetric descriptions are present.
- Extended centre ideals: `extended` is `I.map (algebraMap A Chart)`. The three ideal
  equalities assert `(x)`, `(a)`, `(y)` in the actual charts. This is the affine coordinate
  description of the recorded ideal-sheaf comap, using `ideal_comap_appLE` (imported
  as a proof dependency). It does not introduce a competing definition of ideal-sheaf pullback.
- Closed inverse image: `Exceptional = Chart ⧸ extended`; `exceptionalMap` is the
  quotient closed immersion followed by the canonical chart map to the blowup.
- The three coordinate-ring isomorphisms q₀,q₁,q₂ give respectively
  `Polynomial (Residue R a)`, `Ring (Residue R a) (epsilon R a n)`, and
  `Polynomial (Residue R a)`. `Residue = R ⧸ Ideal.span {a}` and epsilon is 1 when
  n=2, otherwise 0. The variable equations send t,h to `Polynomial.X` and r,s to the
  indicated quotient coordinates. Every coefficient is explicitly reduced modulo a.
- Exceptional overlaps are restrictions of the same chart ratios:
  `∀ i j, exceptionalMap i ⁻¹' exceptionalImage j = basicOpen (exceptionalMk (z i j))`.
- At n=2 the set equality `exceptionalImage 1 = exceptionalImage 0 ∩ exceptionalImage 2`
  is accompanied by an equivalence from the entire middle exceptional ring to the first
  exceptional ring localized at t. Its formulas r=t^-1, s=t and its Spec compatibility
  identify it with the whole adjacent overlap. The compatible map from the third
  exceptional ring sends h to t^-1, explicitly stating the common-overlap transition.
- At n>2 the intersection of the two outer exceptional images is empty. For a prime
  in the middle mapping into the first (respectively third) image, s (respectively r)
  belongs to its prime ideal, stating that these overlaps lie on s=0 and r=0.

Dependency declarations read and used:

- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, for the exceptional outer rings.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, its X and C,
  and the aeval universal property, for all two-variable presentations.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: quotient algebra, `Ideal.Quotient.mkₐ`
  and ring quotient map `Ideal.Quotient.mk`; `Algebra`/`AlgHom`, ideal products and powers
  use Mathlib directly. The quotient node is a Mathlib leaf and needs no lean repair.
- `WeilConjectures.Blowup.Affine.Defs`: `AlgebraicGeometry.AffineBlowup`,
  `AffineBlowup.chart`, `AffineBlowup.toSpec`, `AffineBlowup.opensRange_chart`.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`,
  `chartFraction`, `homogeneousAwayToChart`, `coe_homogeneousAwayToChart_mk`,
  `homogeneousAwayEquivChart`. The last is the canonical equivalence whose forward
  map is exactly the dependency's recorded theta, used directly by `chartMap`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`: `Proj`,
  `Proj.basicOpen`, `Proj.awayι_preimage_basicOpen`, and Spec of homogeneous localization.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, and prime spectra underneath.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`:
  `Scheme.IdealSheafData.ideal_comap_appLE`, supplying its exact affine extended-ideal formula.
- `WeilConjectures.Blowup.FiniteDegree.Algebra`:
  `AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span`, for the finite generator chart cover.
- `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away.lift`,
  its equation and uniqueness (as recorded in the proof dependency's Mathlib match),
  `Localization.Away` and `IsLocalization.Away.invSelf` for the overlap statements.
- The Laurent-normal-form proof node has no recorded Lean declaration. It is a proof
  prerequisite only, so it is named in the proof docstring and has no fabricated import.
  All other recorded proof modules are imported. No import cycle is introduced.

Sources opened: local Stacks divisors.tex, lemma-blowing-up-affine (0804), its statement
and proof; algebra.tex definition-blow-up (052Q); constructions.tex lemma-standard-open
(01M4) and lemma-standard-open-proj (01MA); schemes.tex lemma-fibre-product-immersion
(01JU). The formulas in the node are the explicit agent calculations described in its
source record. The current blueprint does not state this extracted auxiliary lemma itself.

Edge cases checked before writing:

- n=2: the middle parameter is a^0=1, so rs=1 even before reduction; epsilon=1;
  q=t², h=t/q=t^-1, and the middle exceptional chart equals the outer intersection.
- n=3: the middle exceptional relation is rs=0; q=xt³ reduces to 0, giving empty
  outer intersection. On the first--middle overlap s vanishes after quotienting by x.
- a a unit: I is the unit ideal, all exceptional quotient rings are zero rings, and
  the exceptional-image assertions are empty-set assertions. No Nontrivial assumption
  is imposed on R/(a), the chart quotients, or their localizations.
- R=Z,a=4: R/(a) is nonreduced. No reducedness, normality, noetherianity, field,
  DVR or characteristic assumption has been added. The fibre statements use prime
  ideals/basic opens and therefore include this case.
- Repeated indices i=j: z i i=1 follows from the actual chartFraction equation; the
  overlap formula includes this case and says the whole chart.
- Arbitrary universe u: all constructed rings and schemes stay in u. There are no
  site/coefficient universe equalities or restrictions, and autoImplicit is disabled.

Searches (actual launcher msearch calls, plus local ripgrep; no exact existing result):

- leansearch: "Explicit charts overlaps and exceptional fibre of blowup xy=a^n in
  ideal x,a,y"; 8 hits concerning manifold charts and bundles, no algebraic blowup result.
- leanfinder: "Fraction algebra charts of the blowup of R[x,y]/(xy-a^n) at the ideal
  (x,a,y), with exceptional quotient rings and overlap transitions"; 8 hits including
  Proj, Proj.awayι, StandardEtalePair.Ring and an elliptic-curve quotient result, none
  gives the binomial chart calculation or all its clauses.
- loogle: "MvPolynomial, Ideal.Quotient"; 0 hits, unknown identifier Ideal.Quotient.
  Earlier "ReesAlgebra, Localization" likewise returned 0 hits/unknown ReesAlgebra.
- msearch grep: "binomial.*[Cc]hart|[Cc]hart.*binomial"; 0 Mathlib hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: binomial/Binomial and the node id;
  no existing version. Nearby results concern unit-binomial finite etale covers,
  Weierstrass coordinates, tangent-cone/formal-fibre quadrics, Lie divided powers,
  or unrelated binomial shifts, not this blowup. A more specific search for binomial
  ring presentations and X0*X1 in AlgebraicGeometry/RingTheory found no duplicate.
- DAG search for binomial notions found this item, its Laurent-normal-form proof
  dependency and parent blowup calculation, plus unrelated nodes; no independent
  missing definition is needed, since the file specializes the recorded notions.

Validation: scompile.py compiled the module both as an isolated sandbox file and under
its final library module name (34.8/34.5 s), with no errors or warnings. The only proof
is the main theorem's sorry. There are no auto-bound variables, local notation, private
copies, chosen existence data, or proof terms hidden inside the definitions.

## Second reading by NC

I reopened the unchanged node and read the final module clause by clause using the
mapping above. This is a second reading by the assigned worker; no separate agent was
started, as instructed by the dispatch brief. The maintainer supplies the independent review.

The review checked all three presentation relations and coefficient maps, all four
ambient embeddings, the universal overlap formula for nine ordered pairs including
repeated indices, the three covering opens, both adjacent transition equivalences and
the outer transition with its inverse, the extended ideals and the generator-preserving
quotient maps, and both exceptional-fibre cases. The n=2 statement has a genuine
localization equivalence and the h=t^-1 morphism equation, rather than just a statement
that two sets have the same underlying points. The n>2 branch conditions are expressed
on primes of the actual middle exceptional ring. No part of the node was dropped.

Corrections during elaboration: the Spec map defining chartMap must use theta's forward
ring equivalence, because Spec is contravariant; `variable` is a Lean keyword and the
helper was renamed `chartVariable`; the exceptional basic-open set uses its explicit
carrier. These were typing corrections in the sandbox; no mathematical statement change
or DAG correction was made. The JSON statement is extracted verbatim from the theorem
signature, and every helper declaration is listed in lean.declarations.
