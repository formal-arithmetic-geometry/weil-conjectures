## Worker report

This is a stage-2 statement delivery, not a new stage-1 split. The live item is
split and reviewed PASS but has no Lean record; coord/brief-stage2.md §0 explicitly
permits this handoff. No stage-1 fields or accepted proof steps are changed.

The module states `AlgebraicGeometry.AlgebraicSpace.squareZero_stalk_ideal_pullback`.
Its sole theorem has proof `sorry`. Three new definition nodes expose normalized
presentations of the objects already named in this node. They assert no existence:
the theorem supplies them. None chooses data from an unspecified existence theorem.

Hypotheses and clauses, in order:

- `S : Scheme.{u}` and `X Y X' Y' : AlgebraicSpace S` give the arbitrary base scheme
  and the four spaces in the common universe of the existing algebraic-space API.
- `f`, `f'`, `i`, `j` and `h : f ≫ j = i ≫ f'` are the given commuting square.
- `hi`, `hj : IsSpaceFirstOrderThickening ...` mean representable closed immersions
  with square-zero kernels on every scheme test. The imported definition reduces
  to `IsFirstOrderThickening`, which is exactly `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- The existential `T`, `W : ThickeningSiteModel ...` identify the small étale sites.
  Their equivalences are continuous both ways; their reductions are genuine
  scheme pullback squares and their quotient maps are regular-function pullback.
- `I`, `J : SquareZeroIdeal ...` are module sheaves on the reduced sites, with
  injective natural additive inclusions into the thickened structure presheaves.
  `kernel` identifies their images with the quotient kernels, `square_zero` states
  square-zero multiplication, `locally_surjective` is sheaf quotient surjectivity,
  and `scalar` is exactly the action through the quotient. They are not arbitrary
  ideal-labelled modules. The theorem provides these objects for the immersions.
- `SquareZeroSquareCalculation.thickMap`, `reduces`, `induced` prescribe the
  actual map induced by f' on lifted charts, compatible with f on reductions.
- `idealMap` is a morphism from the existing `moduleTensorPullback f` of I to J.
  `idealMap_normalization` sends the existing `moduleTensorSection` with scalar the
  reduction of b to b times f'-sharp(m). `lift_independence` explicitly states
  independence of b whenever its reduction is unchanged.
- `sourceStalks`, `targetStalks`, `sourceThickStalks`, `targetThickStalks` cover all
  four ringed sites on the identified étale categories. A geometric point is
  quantified as an arbitrary algebraically closed field Ω, its map b to S, and
  the Yoneda map s to the space. `SquareZeroNeighborhood` is the category of
  pointed étale scheme charts, not topological/Zariski neighbourhoods.
- `SquareZeroStalk` specifies an actual colimit cocone of the section rings and,
  for each module presheaf, an actual colimit cocone of its additive groups.
  `map_germ` and `smul_germ` prescribe maps and actions. Its presentation is fixed
  up to the unique cocone-preserving isomorphism, not by an arbitrary stalk functor.
- `SquareZeroStalkFamily.exact` gives preservation of finite limits and finite
  colimits for module SHEAVES. `conservative` is the all-geometric-points criterion
  for isomorphisms. On a thickening these are evaluated on the equivalent reduced
  site, so the same point represents its unique lift to the thickened space.
- `pointCalculation` supplies A', B', A, B as these ring colimits. Its
  `quotientX/Y_germ` and `thickMap/reducedMap_normalization` prescribe the four ring
  maps on germs. `commutes` is their commutative square, and the two
  `quotient..._surjective` fields give surjectivity.
- `inclusionI/J` are normalized on every ideal germ and injective. `kernelI/J`
  identifies their ranges with the two quotient kernels; `scalarI/J` identifies
  the quotient actions. `squareZeroI/J` is I²=J²=0, using these kernels as ideals.
- `quotientIsoI/J` and their normalization fields give A'/I ≃+* A and B'/J ≃+* B
  by the canonical quotient maps, rather than unspecified ring isomorphisms.
- `tensorComparison` is the stalk of f*I identified with I tensor_A B.
  `tensorComparison_germ` prescribes the order i tensor b for every local pure
  tensor; `tensorComparison_smul` makes it B-linear, using right-factor scalar
  multiplication via the standard tensor symmetry.
- `pointMap` is additive, `pointMap_smul` is B-linearity, and `pointMap_stalk`
  identifies it with the actual stalk of `idealMap` under that comparison.
  `pointMap_tmul` gives q(i tensor b) = f'-sharp(i) times any lift of b.
  Surjectivity of quotientX supplies lifts of every b; the equation quantifies
  over all lifts, so it does not select an arbitrary lift.
- The fibre product is the landed `enlargedFibreProduct j f'`
  (def-sfb-space-sheaf-fibre-product; review FIX replaced the delivered duplicate
  `squareZeroPullbackSpace`, which had the same body). `squareZeroPullbackMap`
  is the canonical map from the actual `pullback.lift` of the commuting square.
- `fibreIdeal` is the kernel of the actual restriction to that fibre product at
  the point, prescribed by pullback of regular functions on compatible pointed
  charts. `fibreIdeal_eq` identifies this kernel with `Ideal.map thickMap (ker
  quotientY)`, exactly IB', rather than an injective tensor product.
- `cartesian_iff` says the canonical morphism is an isomorphism iff ker quotientX
  equals that extended ideal at EVERY geometric point of X. There is no flatness
  hypothesis anywhere.

Dependency declarations used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its category.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`,
  `structurePresheaf`, `structureSheaf`, `Modules`, `IsRepresentableWith`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`, via
  WeilConjectures.AlgebraicGeometry.Thickening.`IsFirstOrderThickening`.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`, transparent to
  Mathlib `SheafOfModules`; inclusions and tensor maps use the actual module category.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the recorded
  tensor dependency, retained as a public statement import.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  `fibreProduct_isAlgebraicSpace` supplies the algebraic-space pullback object.
- Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData:
  `IsSpaceFirstOrderThickening`, `ThickeningSiteModel`, `ChartRingMap`, `Reduces`,
  `InducedBy`. Its landed definition node is added to stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  `moduleTensorPullback`, `moduleTensorSection`, `moduleChartTarget`. Its landed
  definition node is added to stmt_deps. The normalization is the existing
  adjunction unit, not a second pullback definition.

Sources read: spaces-properties.tex lemma-stalk-pullback (04K2) and
 theorem-exactness-stalks (04K5); spaces-morphisms.tex
lemma-closed-immersion-ideals (03MB) and the following inverse-image definition;
spaces-more-morphisms.tex lemma-thickening-equivalence (05ZS). The six accepted
DAG proof steps are reproduced with their dependencies in the theorem docstring.

Edge cases: identity thickenings give zero ideals and a cartesian square. Empty
spaces impose no extra nonemptiness assumptions; the geometric-point condition is
vacuous precisely when appropriate. General nilpotent thickenings are not substituted
for square-zero ones. For the nonflat example A'=k[ε]/ε², A=k, B'=k, B=k,
IB'=J=0, so the criterion says cartesian, as required. If B'=k[t]/t²,
B=k and ε maps to zero, J=(t) differs from IB'=0 and the square is not cartesian.
Neither characteristic nor a bound on the field extension degree is imposed.

Searches actually run using msearch.py:

- LeanFinder: “For a square of square-zero closed immersions of algebraic spaces
  the stalk of the ideal pullback is the tensor product and the square is cartesian
  exactly when the ideals agree”.
- LeanFinder: “geometric stalk pullback of modules on algebraic spaces square zero
  ideals”: eight results concerning scheme tilde stalks and scheme stalk maps;
  none states this algebraic-space square calculation.
- Loogle: “CategoryTheory.Sites.Point, SheafOfModules, TensorProduct”: service
  responded with unknown identifier CategoryTheory.Sites.Point, zero hits; this
  query is inconclusive, not evidence of absence.
- Mathlib grep: “stalk.*tensor|tensor.*stalk|AlgebraicSpace” in AlgebraicGeometry:
  one SurjectiveOnStalks tensor-prime-spectrum hit, no matching statement.
- LeanSearch: “Geometric stalks of algebraic spaces on the small etale site and
  modules”: eight hits, concerning scheme stalks, smallEtaleTopology and tilde
  stalks; none supplies this statement.
- rg in lean/WeilConjectures/AlgebraicGeometry found scheme ideal/stalk theorems
  and geometric-point comparison modules, but no algebraic-space theorem here.
- rg in lean/Sheaf/AlgebraicGeometry found the existing square-zero extension
  data and module operations, which are used. Searches for SquareZeroStalk and
  SquareZeroIdeal gave no prior declarations. Blueprint search for “geometric
  stalk square zero ideal” returned zero nodes. The normalized data interfaces are
  recorded in three new definition nodes so each module has its own owner.

No statement correction, disputed statement, or dependency-interface replacement.
Three new definition nodes own the normalized presentation interfaces; the theorem
asserts their simultaneous existence, as detailed below.
The inherited stage-1 BLOCKED ending is superseded by the explicit stage-2 handoff.

## New nodes

`def-sfb-space-pointed-stalk-data` records the actual pointed-chart categories,
regular-functions presheaf, normalized ring/module colimit presentations and exact
conservative geometric families. Source: 04K0, 04K2, 04K5 and 04EQ. The definition
contains only structures and explicit diagrams, without existence or chosen data.
The existing scheme-only pointed stalks do not give this algebraic-space interface.

`def-sfb-space-square-zero-stalk-data` records the square-zero ideal presentation,
explicit tensor product and right-factor scalar action, normalized stalk ring-map
interface, and the genuine fibre-product restriction kernel. Source: 03MB, 05V5 and 05ZS.
It reuses the landed thickening, module tensor and sheaf fibre-product constructions.
The interfaces are definitions only: their existence is exactly the item's theorem.

All three nodes record the actually run LeanSearch, LeanFinder and Mathlib/project grep
queries; none of their names occurs in the DAG or project, and blueprint searches returned
zero matches. The presentation definitions are split into their owning modules. All four files
passed the prescribed scompile.py check together in dependency order.

Additional successful Loogle search: `TensorProduct, RingHom.ker` returned 12
results including `Algebra.TensorProduct.rTensor_ker`, `lTensor_ker`, `map_ker`
and Kähler differential constructions. They concern algebraic tensor kernels,
not geometric stalks and module maps for algebraic spaces. The initial longer
LeanFinder search returned eight scheme pullback/closed-immersion results
including `AlgebraicGeometry.isPullback_of_isClosedImmersion`; no exact match.

`def-sfb-space-stalk-quotient-tensor-data` owns
`SquareZeroPointCalculation`: the four normalized stalk ring maps, their kernels,
quotient isomorphisms, and the normalized B-linear tensor-stalk comparison. It
uses the preceding two definition nodes and the existing module tensor pullback.
This separates the independent comparison-data definition from the ideal and
fibre-product definitions; none asserts the comparisons exist. The searches and
source are the same actual 04K2/05V5 and 03MB searches recorded above.

The first dry run required the current node-schema field `import_flags`; all three
new definition records now include its empty default, as in the landed definitions.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
