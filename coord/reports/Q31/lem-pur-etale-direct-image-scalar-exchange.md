## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange` states
`AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_scalarExtension`, with its sole
proof `sorry`. It introduces no definitions and proves nothing. The original
statement is unchanged. Two already landed definition dependencies are added to
name the actual canonical scalar/pullback constructions used in the signature:
`def-pur-open-coefficient-normalizations` and
`def-pur-etale-scalar-pullback-iso`.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| Unital map of finite commutative rings A to B | `{A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)` |
| All schemes and morphisms arbitrary | `{X' X Y' Y : Scheme.{u}}` and the four morphism binders, without geometric property instances |
| Ordinary unbounded D_R(T) | `DerivedCategoryModule R T`, definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} R))` |
| Q_T is derived extension of scalars | `scalarExtension φ T`, the existing left adjoint to exact derived restriction; its representative counit and scalarTensorIso identify it with ordinary uncompleted K-flat tensor extension |
| Exact geometric inverse image | `D(upperStar (ModuleCat.{u + 1} R) u)` |
| Canonical K-flat lambda | `(properOpenCoefficientPullbackIso φ u).hom`, obtained by transporting the existing uniquely K-flat-normalized `scalarPullbackIso` through `leftDerivedUpperStarIsoMapDerivedCategory` |
| Canonical inverse-image/direct-image adjunction | `mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u+1} R) u`, canonically identified with `derivedUpperStarLowerStarAdjunction` along that same exactness isomorphism |
| chi has adjunct Q(epsilon) after lambda | `(scalarMate φ u).app E`; its definition is `mateEquiv` applied to `scalarPullbackIso`. Transporting the adjunction to exact inverse image transports lambda by precisely `properOpenCoefficientPullbackIso`, and leaves its right-adjoint mate unchanged |
| Chosen Cartesian square with h, f', f, g | `(sq : ChosenCartesianSquare h f' f g)`; `sq.toCommSq` is passed to the exchange |
| Specified unbounded counit exchanges for A and B | `exactDerivedBaseChangeMap (ModuleCat.{u+1} A) sq.toCommSq`, and the identical expression with B |
| Every M in D_A(X) | `(M : DerivedCategoryModule A X)` |
| Left-hand path: g_B^*(chi_f), Ex_B at Q_X M, Rf'_B(lambda_h) | The three factors on the left of `=`, in precisely that execution order using Lean's `≫` |
| Right-hand path: lambda_g at Rf_A M, Q_Y'(Ex_A), chi_f' at h_A^*M | The three factors on the right of `=`, in precisely that execution order |
| Common source | `(D(upperStar (ModuleCat.{u+1} B) g)).obj ((scalarExtension φ Y).obj ((R(lowerStar (ModuleCat.{u+1} A) f)).obj M))` |
| Common target | `(R(lowerStar (ModuleCat.{u+1} B) f')).obj ((scalarExtension φ X').obj ((D(upperStar (ModuleCat.{u+1} A) h)).obj M))` |
| Natural in M | All six arrows are components, functor images, or composites of the existing natural transformations. The equality for every M is their componentwise equality |
| No properness or invertibility conclusion | No properness, boundedness, flatness or nonzero-ring instance; the conclusion is equality of morphisms, with no IsIso assertion |

Dependencies read and used (module; declarations):

- `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme`, `.Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, publicly importing
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`;
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`;
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
  The usable, already published constant-coefficient specialization is
  `AlgebraicGeometry.Etale.scalarExtension` from
  `Sheaf.Paper.EtaleDerivedScalarTensor`, reexported through the normalized scalar
  comparison's module. It retains its actual scalar-extension representative
  counit, and is not a second arbitrary functor.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`;
  `AlgebraicGeometry.etaleInverseImageModulesExact` (constant-ring identification,
  module action, exactness and adjunction).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, publicly importing
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`;
  `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`,
  `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`;
  `AlgebraicGeometry.ChosenCartesianSquare`, `.toCommSq`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`;
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso`,
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`.
- `Sheaf.Paper.PurEtaleScalarMateProjection`;
  `AlgebraicGeometry.Etale.scalarPullbackIso_existsUnique`, `scalarPullbackIso`,
  `scalarMate`. The first two are recorded by
  `def-pur-etale-scalar-pullback-iso`; the last is the existing counit mate.
- `Sheaf.Paper.ProperOpenCoefficientRefinement`;
  `AlgebraicGeometry.Etale.properOpenCoefficientPullbackIso`. Despite its historical
  name, its full signature permits every scheme morphism, without openness or
  properness. It is the exactness transport of scalarPullbackIso, not an input
  comparison or a chosen unrelated isomorphism.
- Proof-only imports: `Sheaf.Paper.KFlatScalarComparisonNormalization`,
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`; and
  `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv` and its
  counit transpose formula. The former proof dependency landed while this item
  was being read; its current record and source were consulted.

The full five-step proof in the node is carried in the theorem docstring, including
the pullback cube, both defining mate equations, the two transposes and their
identification. The source's omitted verification was read at
`literature/stacks-project/sites-cohomology.tex`, remarks `remark-base-change`
and `remark-compose-base-change-horizontal` (Tags 07A7 and 0E47).

Edge cases checked semantically before writing: identity square and identity ring
map; zero object M; empty schemes; zero coefficient ring; the nonflat quotient
Z/4 to Z/2; unbounded complexes with cohomology in arbitrarily negative degrees.
None needs an omitted finiteness, flatness, nontriviality or boundedness hypothesis.
The coefficient universe u+1 follows the existing ordinary-etale encoding and
includes every finite coefficient ring by lifting; no site-universe equality was
introduced.

Searches made:

- `msearch.py ... leanfinder "Derived scalar extension commutes with counit base
  change exchange for etale sheaves"` and `"Scalar extension respects ordinary
  etale derived direct image exchange"`: ordinary ring/etale algebra results,
  no exact small-etale exchange equality.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.NatTrans"`:
  zero hits.
- `msearch.py ... grep 'scalar.*[Ee]xchange|[Ee]xchange.*[Ss]calar|mate.*[Cc]ompos'
  CategoryTheory`: abstract mate-composition lemmas, including
  `mateEquiv_hcomp`, not this normalized geometric/coefficient statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for scalar/exchange,
  scalarMate/exchange, scalarPullbackIso, derived scalar extension and the proposed
  theorem name; literal `grep -rn` of this item id in `lean/WeilConjectures`:
  no duplicate statement. Existing `ProEtale.directImageScalarExchange` is on the
  pro-etale site, so does not match. The searches located the existing etale
  scalarExtension, scalarPullbackIso, scalarMate and exactness transport; all are
  reused. The proposed declaration name is unused.

No new nodes, dependency repairs, statement correction, or disputed statement.
Only the item's Lean record and the two added landed definition dependencies
change. Compilation and delivery checks are performed with scompile.py and
deliver2.py; no local/global build or direct repository edit is used.

## Second reading by Q31

This is a separate semantic reread in the same worker session, as the dispatcher
forbids starting another agent; the maintainer supplies the independent review.
I compared the node and final signature again. In particular the top horizontal
edge is h (not g), the final scalar functor on the right is Q_Y', the last mate is
for f' evaluated at h_A^*M, and the B-exchange is evaluated at Q_X M. Both paths
have exactly the source and target shown above. The exact lambda has the required
direction because properOpenCoefficientPullbackIso first changes exact B-pullback
to L-pullback, applies scalarPullbackIso, then changes L A-pullback to exact
A-pullback. scalarMate is reused under the canonically transported adjunction,
rather than redefining chi. Finite coefficients are explicit, but no flatness,
properness, boundedness, openness, or nonzero assumption slipped in. Naturality
is built into all the displayed natural transformation components. No mismatch
or statement change was found.
