## Worker report

The delivery states `AlgebraicGeometry.RelativeFermatCurve.finite_chart_cover` in
`Sheaf.AlgebraicGeometry.FermatFiniteChartCover`. Its proof is `sorry`; all 21 accompanying
chart definitions and named instances have actual data. The original node statement, proof,
proof dependencies, statement dependencies, and all other fields are preserved. Only `lean`
changes. No statement dispute or correction is needed.

The hypersurface is not redefined. The existing module
`Sheaf.AlgebraicGeometry.RelativeFermatKummerCurve` already supplies `equation`, `ideal`,
`curve`, `ι`, and `π` for EVERY natural exponent and EVERY base scheme. Its theorem has
additional assumptions, but those assumptions are absent from these definitions and absent
from this delivery. In particular, this statement does not invoke its Kummer-cover theorem.
`equation S n` is the difference of the three tensor powers of the coordinate sections of
O(1); `ideal S n` is `Scheme.Modules.Hom.zeroLocus (equation S n)`; `curve` is its actual
closed subscheme, `ι` its inclusion, and `π` its structural morphism. This is precisely the
closed hypersurface in the item, without reduction. There is no missing independent notion
and no new DAG node: the existing specialized construction is used directly, built from the
item's recorded general definitions. The tensor power O(1)^{tensor n} realizes the homogeneous
degree-n equation and is canonically O(n).

Clause-by-clause correspondence (all names in the RelativeFermatCurve namespace unless
qualified):

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Any scheme S | `(S : Scheme.{u})`; universe `u` is explicit, with no extra scheme instances |
| Integer n >= 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| D_n is the closed equation A^n-B^n-C^n in P^2_S | Existing `curve S n`, `equation S n`, `ideal S n`, and `ι S n`; coordinates use `ULift.{u} (Fin 3)` |
| D_+(C) intersect D_n and D_+(A) intersect D_n | `chartOpen S n false` and `chartOpen S n true`, defined by inverse image under the specified embedding |
| The two opens cover | First conjunct `chartOpen S n false ⊔ chartOpen S n true = ⊤` |
| There exists an S-morphism q_n to P^1_S | `∃ q : curve S n ⟶ ProjectiveLine S`; first conjunct of `HasPowerChartFormula` is `q ≫ ProjectiveLine S ↘ S = π S n` |
| Exact inverse images of the x- and y-charts | For every Bool `c`, `HasPowerChartFormula` supplies `h : q ⁻¹ᵁ lineOpen S c = chartOpen S n c` |
| x=(A/C)^n and y=(C/A)^n | Same predicate's `q.appLE ... (lineCoordinate S c) = chartCoordinate S n c (if c then 1 else 0) ^ n` |
| Uniqueness with the prescribed formulas and inverse images | `∀ q', HasPowerChartFormula S n q' → q' = q`; uniqueness is among all S-morphisms satisfying those formulas, without extra finiteness hypotheses |
| Every affine open V=Spec R of S | `∀ (V : S.Opens), IsAffineOpen V → ...` in `HasTwoRootCharts`; R is canonically `Γ(S,V)`. Every affine V is canonically Spec of this ring, so any chosen identification V=Spec R transports the same statement to R |
| The two source pieces over V are affine | `IsAffineOpen (localChartOpen S n c V)` in `HasLocalChartPresentation`; this open is the chart intersected with `(π S n) ⁻¹ᵁ V` |
| S_C=R[x,a,b]/(a^n-x,b^n-(x-1)) | For `c=false`, `chartRing R n c` is the ideal quotient of `MvPolynomial (Fin 2) (Polynomial R)` by those exact two generators |
| S_A=R[y,u,v]/(v^n-y,u^n-(1-y)) | For `c=true`, the ideal generators are u^n-(1-y), v^n-y; their order is immaterial to the generated ideal |
| These are algebras over the indicated target chart rings | The ring equivalence E in `HasLocalChartPresentation` fixes R through the actual structural `π.appLE`, sends the parameter X to a^n or v^n, and sends both root generators to the actual homogeneous fractions. Together with `HasPowerChartFormula`, this specifies the R[x]- or R[y]-algebra identification, rather than an arbitrary ring isomorphism |
| a=A/C, b=B/C, u=B/A, v=C/A | `chartCoordinate` is the pullback along `ι` of `ProjectiveSpace.coordRatio`; `chartDenominator` and `chartNumerator` encode exactly these indices |
| Overlap v=a^{-1}, u=b/a, y=x^{-1} | `HasChartOverlap`: a*v=1, a*u=b, a^n*v^n=1 in the actual section ring of the intersection. The first makes a a unit with inverse v, so the second is exactly u=b/a; the last uses the specified x=a^n, y=v^n. No division operation on a general ring is used |
| R[x]-basis a^i b^j, 0<=i,j<n | `∃ b : Module.Basis (Fin n × Fin n) (Polynomial Γ(S,V)) (chartRing ... false), ∀ ij, b ij = chartMonomial ... ij` |
| R[y]-basis u^i v^j, 0<=i,j<n | Identical explicit `Module.Basis` condition for `c=true` |
| Basis means unique finite linear combinations | Mathlib `Module.Basis` is an isomorphism to finitely supported coefficient functions; `Fin n × Fin n` gives exactly the displayed finite index set, not just freeness of unspecified rank |
| q_n finite | `IsFinite q`, the recorded definition of finite morphism |
| q_n surjective on ALL points | `Surjective q`, whose definition is `Function.Surjective q`; not just geometric or closed points |
| Every base change T -> S | Unrestricted `∀ (T : Scheme.{u}) (g : T ⟶ S)` |
| D_T is D_S times_S T | `∃ t, IsPullback t (π T n) (π S n) g` |
| This identification is the hypersurface in P^2_T | `IsPullback t (ι T n) (ι S n) (ProjectiveSpace.map (ULift.{u} (Fin 3)) g)`; hence it preserves the specified closed embedding and its scheme structure |
| Maps commute with base change | Existence of `qT` with `HasPowerChartFormula T n qT` and `t ≫ q = qT ≫ ProjectiveSpace.map ... g`. Uniqueness of the chart formulas identifies this with the uniquely characterized map over T |
| Displayed charts, presentations, overlaps commute with base change | `HasTwoRootCharts T n`, and exact preimages of each `chartOpen` under t, and `t.appLE ... (chartCoordinate S n c j) = chartCoordinate T n c j` for both generators. The structural pullback square gives coefficient compatibility. Since E in each presentation is prescribed on all coefficients, the parameter, and both generators, these equations also force naturality of its algebra presentation; overlap substitutions are preserved by these ring maps |
| No normality, reducedness, characteristic, invertibility, or roots-of-unity assumptions | No such binders or typeclass assumptions occur. Only S, n and positivity are hypotheses |

All helpers are part of spelling out this node's chart descriptions; they are listed in
`lean.declarations` and documented with this node's source and blueprint tag. The main
statement's docstring contains all seven DAG proof steps and their named dependencies.
The basis is stated for the literal quotient, and the specified ring equivalence transports
it to the actual chart sections. Naming the quotient required explicit named public
`chartRingCommRing` and `chartRingAlgebra` instances; both are the existing quotient instances
via `inferInstanceAs`, with no postponed proof or data.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its
  morphisms, read with the locally affine definition.
- `def-pc-proj`: Mathlib's `AlgebraicGeometry.Proj`, `projIsoSpec`, and
  `ProjectiveSpectrum.basicOpen` in the ProjectiveSpectrum sources. These underpin the
  recorded projective space and its genuine standard opens; no second Proj is defined.
- `def-nagata-projective-space-base-change`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace`,
  `ProjectiveLine`, `toProjInt`, and `ProjectiveSpace.map`. The coordinate index counts
  homogeneous coordinates: three for the plane, two for the line.
- `def-pc-zero-scheme`: `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`,
  `Scheme.Modules.Hom.zeroLocus`. Its full docstring and actual ideal construction were read;
  this is the nonradical ideal of the section. The existing equation uses invertible tensor
  powers, so the zero-locus definition's invertibility proviso is satisfied.
- `def-pc-projective-space-twist`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, `ProjectiveSpace.twist`, and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection`, `coordinateSection`.
  The existing equation uses these actual coordinate sections, not independent data.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (affine plus finite maps on all affine target opens).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` with its projections and universal property. Cartesian
  squares are expressed with `IsPullback`, an equivalent choice-free universal property.

Additional existing declarations used:
`RelativeFermatKummerCurve`'s `RelativeFermatCurve.equation`, `ideal`, `curve`, `ι`, `π`;
`ProjectiveSpace.OfSections`'s `standardOpen`; `ProjectiveSpace.OfInvertible`'s `coordRatio`;
Mathlib `Ideal.span`, `Ideal.Quotient.mk`, `MvPolynomial`, `Polynomial`, and `Module.Basis`.
The latter are general library notions, not specialized substitutes for a recorded dependency.

Proof-plan imports are explicit for the recorded `projectiveSpace_standardCharts`,
`exists_isEffectiveCartierCenter_hilbertPresheaf` in Picard.ZeroScheme (the current record of
lem-pc-zero-scheme-properties), `Scheme.Cover.glueMorphisms`, the finite-locality declarations
in Morphisms.Basic, `PrimeSpectrum.comap_surjective_of_faithfullyFlat`, and `pullbackSpecIso`.
The monic-quotient-faithful-tensor-coordinates node has no recorded Lean module in the read
snapshot, so there is no proof module to import yet. This is solely a future proof input,
not a missing notion for this statement. The currently recorded zero-scheme-properties
THEOREM is broader/different from the needed local formula; the actual local zero-locus
formula already exists in the recorded ZeroLocus construction and its theorems, so this
delivery does not rely on that unrelated theorem's signature for its statement.

Import-cycle note for maintenance: the existing `RelativeFermatKummerCurve` module owns the
real definitions reused here and also contains the downstream Kummer theorem. Its DAG proof
now cites this item. Adding this module as a proof import back into RelativeFermatKummerCurve
would close an import cycle and must be omitted under stages/2-statements.md §3(7). This
statement uses only that module's real definitions, not its downstream theorem. The DAG
itself is unchanged, and there is no new prerequisite edge or dependency wait.

Edge cases checked mathematically before writing:

- n=1: a=x, b=x-1, u=1-y, v=y. Each chart has the one-element basis indexed by
  `Fin 1 × Fin 1`; the map is the expected isomorphism of the line.
- Empty S and zero rings on affine pieces: the source and target are empty; surjectivity is
  vacuous. The specified finite basis is valid over the zero ring because every coefficient
  and every module element is zero; no degree or nontriviality hypothesis was added.
- A characteristic dividing n: the defining ideal can be nonradical and the map inseparable.
  Neither the quotient nor the hypersurface is reduced in the construction. Monic freeness,
  the cover, finiteness and point-surjectivity still apply.
- Characteristic 2: the signs still encode the same equation; no cancellation by 2 occurs.
- Nonreduced and non-quasi-compact S: every assertion is on all affine opens, with no finite
  cover of the base required. Nonflat T -> S is allowed by both Cartesian-square clauses.
- n=0 is excluded exactly by the node's positivity assumption.

Searches made (the prescribed msearch calls were real and logged):

1. LeanFinder: `Relative Fermat hypersurface finite surjective map to projective line two
   root affine charts`. Eight hits on Weierstrass curves, Proj chart surjectivity, and affine
   space; none states this node.
2. Loogle: `AlgebraicGeometry.ProjectiveSpace, AlgebraicGeometry.Proj`. Zero hits; the service
   reports unknown identifier ProjectiveSpace (the project defines it, not Mathlib).
3. Mathlib grep: `[Ff]ermat`, AlgebraicGeometry. Zero hits.
4. LeanSearch: `Fermat hypersurface scheme two affine charts finite morphism projective line`.
   Eight hits on the general finite-morphism class and its consequences, not these charts.
5. LeanSearch: `zero scheme of Fermat polynomial A power n minus B power n minus C power n in
   relative projective plane`. Eight hits on polynomial FLT and general projective zero loci;
   no such scheme construction in Mathlib.
6. LeanFinder: `zero scheme Fermat hypersurface relative projective plane`. Eight hits on
   Weierstrass projective equations/points and a general projective zero-locus theorem;
   no relative Fermat scheme. This supplements the actual source search.
7. `rg` in the exact live read clone's WeilConjectures and Sheaf trees, for Fermat,
   homogeneous sections, coordinate sections, ratios, and the item id. No upstream Fermat
   statement; the Sheaf tree contains the existing five real construction declarations in
   RelativeFermatKummerCurve, plus its stronger-hypothesis theorem. They were read in full.
8. DAG search for Fermat/relative Fermat/hypersurface, and `tools/blueprint_refs.py search
   Fermat` (zero blueprint matches): the current item, its Kummer consumer, and neighboring
   cohomology/smoothness nodes are distinct; no existing node/declaration states this full
   arbitrary-base finite-chart theorem. The definition already exists, so it is reused.
9. Exact name search in `dag/lean_names_upstream.json`, WeilConjectures and Sheaf for the new
   theorem and helper names found no collisions in this namespace.

Validation: the complete module compiled through scompile.py on the server in both sandbox
and final module mode (3.8 s and 4.1 s) without errors or warnings. The initial quotient
instance issue was repaired using the named actual quotient instances described above.
There are no auto-bound universes or variables (`set_option autoImplicit false`), no local
notation or local instances, no `let` or `show ... from` in statements, and no long lines.

The dispatcher requested direct worker delivery and the maintainer's independent review;
no other agent was started and no independent second-reading claim is made here.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
