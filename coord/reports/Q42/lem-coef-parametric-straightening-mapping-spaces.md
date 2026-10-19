## Worker report

The delivery states `SSet.Enhanced.ParametricStraightening.parametric_straightening_mapping_spaces`
in `Sheaf.CategoryTheory.ParametricStraighteningMappingSpaces`. Its only theorem has proof
`sorry`. All definitions have real data, and the structures are the data and propositions
asserted to exist by this theorem. No definition chooses data from an unproved existence
assertion. The source is Gepner--Haugseng--Nikolaus, arXiv:1501.02161v3, Section 1.2,
Example 6.8 and Proposition 6.9, including the three displays in its proof, opened online
on 2026-10-17. The ancestral blueprint proof was also read in the current main-20261015
snapshot. No statement correction or disputed mathematical claim is proposed.

Hypotheses and clauses, in source order:

| Node clause | Lean rendering |
| --- | --- |
| Small quasicategories and a containing universe | `SSet.{u}` for bases and total spaces, `CatInfinity.{u} : SSet.{u+1}` for categories; independent enlargement to `max u v` |
| Quasicategory base B | `Statement.comparisons dual B hB`, with `hB : Quasicategory B` |
| Parameter C an arbitrary small quasicategory | vertices of `CatInfinity` in the full argument category, and `Comparison.currying C hC` for every actual `C : SSet.{u}` with `Quasicategory C` |
| H,G coherent diagrams on B-op | `diagrams false B`, the actual internal Hom on the lifted `oppositeSSet B` |
| Cartesian fibrations classified by H,G | `fibrations false B R` is the actual coherent nerve of naturally marked cartesian fibrations; `Comparison.straighten` is an equivalence to `diagrams false B`; `Statement.cartesian_classification` identifies it with opposite-total-space cocartesian straightening followed by the CatInfinity opposite functor |
| Original fibers, rather than opposite fibers | `Statement.reverse_objects`, `reverse_arrows`, and the final `ihom.map opposite` in `cartesian_classification`; `opposite_specification` uses the existing opposite involution predicate |
| Recorded cocartesian straightening | `Statement.cocartesian`, `cocartesian_models`, and `cocartesian_classification` identify the covariant branch with the dependency's actual straightening, rather than an unrelated equivalence |
| Full relative functor category preserving distinguished edges | `Marked.Over.cartesianFunctors X Y`, reused without a copy; natural marking distinguishes cartesian/cocartesian variance; `Comparison.fullHom_objects` fixes its actual underlying quasicategory |
| Map-cart is its core | the relative nerve uses `R.enrichment` with `R.mapping_iso` identifying enriched maps with `mapSharp`, and `R.mapping_core` identifying those with `core (cartesianFunctors X Y)`; `middleFamily` uses this same relative-nerve mapping-space model via the published coherent Hom pairing |
| C times E with projection to B | `parameter C X` has underlying `Marked.product (Marked.natural C) X.left`, and base map `snd C X.left.underlying ≫ X.hom.val`; `Comparison.tensor_objects` fixes this actual object |
| First displayed equivalence | `Comparison.first_comparison : AreNaturallyEquivalent (firstFamily fullHom) (middleFamily tensor)`; `Currying.iso` and `Currying.formula` additionally give the un-cored evaluation formula in every simplicial degree |
| Pointwise (Delta C) times H | `pointwiseProduct` is built by currying actual evaluation followed by `Products.map`; `Products.objects` fixes value `C × H(b)`, and its two globally coherent projection transformations have the actual degreewise projection components |
| Classification of that product | `Comparison.tensor_classification` is a natural equivalence on the entire parameter-times-fibration category |
| Second displayed equivalence | `Comparison.second_comparison : AreNaturallyEquivalent (middleFamily tensor) (lastFamily straighten P.map)`; `lastFamily` is Hom in the entire coherent diagram category from the pointwise product to the target diagram |
| Covariant version | all constructions quantify over `dual : Bool`; `true` uses B, cocartesian natural marking and the recorded cocartesian straightening; `false` uses B-op |
| Composition | `fullHom_arrows` is normalized by `IsPrepost` to actual precomposition and postcomposition on every relative functor simplex; the comparisons are equivalences on the whole category of three arguments |
| Change of base | `BaseCoherence` is a single coherent straightening equivalence over the entire opposite of CatInfinity; `IsPullback` fixes every enriched pullback simplex by the two actual projections; `Restriction` supplies the full coherent restriction transformation, its every-simplex pullback formula and compatibility with the parameter product; `restriction_coherence` identifies its pullback functor with the component of the global base family |
| Transformations and higher simplices in H,G,C | `arguments F` is the whole `CatInfinity^op × (F^op × F)`; both displayed comparisons are equivalences in its entire space-valued coherent functor category; the normalized full relative Hom and currying retain noninvertible relative transformations |
| Enlarging the universe | the theorem selects `small : Statement.{u}` and `large : Statement.{max u v}` together with `EnlargementComparison small large`; `mapping_objects` gives degreewise normalized isomorphisms of actual relative full functor categories and parameter objects; `cat`, `fibers`, and `diagram` specify the inclusion, with actual lifted functors fixed by `cat_arrows` and `fiber_arrows` and every-simplex diagram normalization; `classification`, `fullHom`, and `tensor` are natural comparisons on the entire corresponding coherent families |
| Small quasicategories | `Comparison.small_functor_categories` asserts quasicategory structure; `cartesianFunctors` is an actual `SSet.{u}`, so smallness is in its type, including all degrees |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.core`, `IsEquivalenceEdge`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `IsFullyFaithful`, and the coherent
  internal-Hom, mapping-space, full-subcategory and cone conventions (recorded `coneCategory`).
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, reexporting
  `Sheaf.CategoryTheory.InfinityFibrations`: cartesian/cocartesian edges, relative lifts,
  fibers and preservation. No private replacement predicate is used.
- `Sheaf.CategoryTheory.CocartesianStraightening`: `CocartesianStraightening.Statement`,
  `coCart`, `object`, `EquivalenceData`, `bases`, `IsPulledMap`, and the normalized
  equivalences and global base naturality carried by that statement.
- `Sheaf.CategoryTheory.CatInfinityLimitsCartesianClosed`: the full coherent exponential,
  actual degreewise product cones and their universal property, and enlarged universes.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`: `Marked.Over.Over`,
  `IsNaturallyFibrant`, `cartesianFunctors`, `RelativeCartesianModelStatement`,
  `mapping_iso`, `mapping_core`, `pull`, `mapSharp`, and the normalized relative enrichment.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `Marked.natural`, `product`,
  `enlarge` and the marked mapping-core convention.
- `Sheaf.CategoryTheory.CatInfinityOppositeInvolution`: `catInfinityObject`,
  `catInfinityArrow`, `catInfinityThickEdge`, `IsCatInfinityOpposite`, and `oppositeSSet`.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`: `CategoryTheory.Spaces.yonedaPairing`.
  This is the already constructed space-valued coherent Hom pairing, including composition
  and every higher simplex. Its existing definition node is added to statement dependencies.
- Proof imports: `MarkedSectionsPointwiseLimits` and `InfinityCocartesianMappingCriterion`.
  The point, relative model and opposite modules also occur among the node's proof dependencies.

The four extra statement dependencies already exist and have usable landed Lean records:
`def-coef-infinity-presheaf-yoneda`, `lem-coef-marked-relative-cartesian-model`,
`lem-coef-marked-point-cartesian-model`, `lem-coef-cat-infinity-opposite-involution`.
A dependency module repair is supplied below for the recorded cocartesian straightening interface.

Edge cases checked: an empty base admits exactly the empty total fibration; an empty parameter
produces the empty product and the terminal space of maps out of it. Empty fibers and empty
relative full functor categories are retained; no `Nonempty` hypothesis is imposed on them.
For a point base, both variances reduce to the ordinary coherent exponential on quasicategories.
A parameter arrow must be an equivalence for its product with a distinguished edge to be
distinguished; using `Marked.natural C`, rather than `Marked.sharp C`, is essential. Identity
and arbitrary base maps are included by `IsPullback` and `Restriction`. In the opposite branch
the second opposite restores the fibers; it does not replace C by C-op. Independent universes
are retained; no universe equality is imposed. Every variable and universe is explicitly bound.

Searches made with the prescribed wrapper on 2026-10-17:

- LeanFinder: `Parameterized mapping spaces for Cartesian straightening and coherent functor
  categories`; eight hits, headed by `CategoryTheory.Functor.IsCartesian.map`,
  `IsStronglyCartesian.map` and ordinary pseudofunctor Grothendieck lifts. Their signatures
  are for ordinary categories, not coherent mapping spaces. No exact match.
- LeanSearch: `Quasicategory Cartesian straightening parametrized mapping spaces`; eight
  hits for `SSet.Quasicategory`, strict Segal quasicategories, ordinary Cartesian morphisms
  and ordinary parametrized adjunctions. No exact statement.
- Loogle: `SSet, ihom, curry`; no hits, with `ihom` unknown to the remote index. The actual
  Mathlib functor-category closed structure and `Functor.HomObj` source were read directly
  to fix the every-simplex currying formula.
- Mathlib grep: `straighten|unstraighten|parametric` in `AlgebraicTopology/Quasicategory`;
  no hits.
- Source/project rg: `parametric_straightening|ParametricStraightening|Fun.*cart.*mapping|
  Parameterized mapping spaces` in the prescribed upstream and `lean/Sheaf` directories;
  only an unrelated proof comment in `MarkedSectionsPointwiseLimits`, no declaration.
- Upstream grep for the exact node id: no hits.

Validation: the module compiled cleanly through `scompile.py`, separately as sandbox and
library module, with the default per-file limit. The first mechanical delivery dry run
passed preflight and compilation (`OK (dry run)`, commit b6e8d7a18a). The final arrow
normalization refinement was compiled again; the dry run is repeated on the final files
before pushing.

## Second reading by Q42

Author's fresh rereading of the node, source display and module; the dispatch brief prohibits
starting another agent. The maintainer's independent review remains separate.

The rereading checked both variances, the full functor categories before cores, the three
mapping-space arguments, the actual product projection, composition, restriction and size.
It caught and repaired an insufficient initial universe clause (two independent existence
statements): the theorem now selects the two instances together with normalized enlargement
comparisons. It also replaced per-object choices of the base equivalence by one global edge
with all components normalized simultaneously. Cocartesian straightening is now explicitly
the dependency's datum, and Cartesian straightening is explicitly its two-opposite dual.
The currying formula was checked against `Functor.HomObj`: the simplex restriction is `a.op`,
and the resulting relative functor is evaluated at the identity simplex. The canonical
restriction formula was checked on both pullback projections, including identity base maps.
No node statement was changed and no input category was replaced by its homotopy category.
All named helpers belong to the parameter comparison itself and are listed in `lean.declarations`.

