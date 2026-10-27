## Worker report

This delivery states `lem-pur-even-line-product-integration-symmetry` and supplies
`def-pur-even-line-product-maps`, the concrete map vocabulary needed to state all
its clauses without an arbitrary product map or coordinate action. No proof is
completed. All postponed applicability and geometric theorems have their asserted
clauses in the definition node and full proof docstrings. Definitions contain real
composites, recursions and canonical comparisons.

The source read is the current `literature/blueprint/latest/` affine-space
composition-law proof, Steps 1--4. The node expands its even-sign and permutation
argument by ordinary proper/open compact-support words. No statement correction
is needed. The indexing convention is r=m-1 throughout: r=0 means one factor.

Hypothesis-by-hypothesis correspondence:

- Finite conventions and arbitrary positive n are `P : PurityFiniteSetting`.
  `P.level_pos` retains n≥1. `AffineLinePurity.Ring P` is the published finite
  coefficient ring indexed by n-1, canonically the same lifted quotient of level n.
  `annihilates P` uses ell^(n+1), so no ramification-index divisibility restriction
  or choice of a special finite level is imposed.
- Y is a scheme of universe u with its named structure map `aY` to Spec k, and
  `[LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]`. Noetherianness
  needed by line integration is obtained from `tower_noetherian`, not assumed.
- X_m and p_m are `space Y r` and `proj Y r`, using the recorded iterated affine
  line construction. `tate P Y r` is p_m* of the positive tensor power of
  `shiftedLine P Y`; flatness, pullback and shift/twist additivity give exactly
  A_X(m)[2m]. This presents the twist by its defining tensor powers, rather than
  introducing a second Tate sheaf.
- V_m is `integral P Y r`; U is `integral P Y 0`. Its functor `support` is the
  actual fixed-scalar pro-etale compactification composite. The affine-line
  compactification at zero is copied only across its projection equality, so
  its extension and proper map are unchanged.
- `trace P Y aY` transports the normalized affine-line `integration` by the
  canonical shifted-line pullback, `lineCoefficientIso` and `coefficientUnitIso`.
  Its target is the canonical derived tensor unit, hence A_Y.
- `hU` asserts only an object isomorphism U≅A_Y. It does not identify that
  isomorphism with trace and does not assume trace is an isomorphism.
- `hV` uses the existing pro-etale `DerivedCategory.constructibleFiniteTor`
  predicate for each V_m. This predicate is bounded constructibility intersected
  with finite Tor amplitude, with the site's existing etale-origin convention.
- `hprod` asserts invertibility of `forward P Y aY r 0`, the specified finite
  forward word. `binaryInverse` is literally its inverse, not a chosen isomorphism
  between its endpoints. `kappa` is exactly the stated recursion, with identity
  at one factor. All other binary products use the same forward word and have
  no invertibility hypotheses added.
- `J`, `hJ₁` and `hJsucc` are exactly the given maps, their one-factor
  normalization and their recursion with the tensor-unit constraint.

Clause-by-clause correspondence:

- The first conjunct says `J r = kappa.hom ≫ powerTrace trace r`.
- The second quantifies over every nonempty binary `ProductTree`. It says the
  actual `treeForward` is invertible and is `normalize.hom ≫ kappa.inv`.
  Inverting this equality is precisely equality of every parenthesized inverse
  product with kappa after the derived associators. `normalize` uses only the
  standard associators, recursively through `appendPower`.
- The third quantifies over every permutation of Fin(m). `coordinate` uses
  the recorded affine coordinate universal constructor and the vector j↦coord(σj).
  `coordinate_geometry` supplies its genuine isomorphism and square over 1_Y.
  `coordinateAction` is inverse identity pullback, actual exchange, canonical
  compactification comparison, and `coordinateTate`; it is never defined by
  conjugating a tensor permutation through kappa. The conjunct asserts its
  invertibility, `S ≫ kappa = kappa ≫ permutation`, and `S ≫ J = J`.
- `permutation` is a concrete composition of associators and the published
  K-flat signed tensor symmetry, with the last-factor permutation decomposition.
  No symmetric-monoidal structure or coherence law is supplied as a hypothesis.
- The fourth conjunct equates the coordinate coefficient identification followed
  by the pullback of the signed Tate-factor permutation with that coordinate
  identification alone. This is equality of the actual morphisms, not just a
  parity calculation. The fifth conjunct records the even-block scalar
  (-1)^((2d)(2e))=1 for all d,e, including d=e=1; the exponent equals
  (-2d)(-2e), including in characteristic two.
- The final conjunct quantifies over all ctf K and all coordinate permutations.
  `coefficientAction` uses the actual tensor-pullback comparison and compositor
  on K, retaining K first. `coefficientTrace` is the inverse of the actual
  `VectorIntegrationSite.projection` followed by 1_K⊗J and the right unitor.
  The equality is S_(σ,K) followed by that counit equals that counit. No crossing
  with K or restriction on its cohomological degrees is made.
- No exceptional inverse image, purity comparison theorem, abstract six-functor
  datum, duality axiom, or assumed coordinate invariance is an input.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: Mathlib `AffineSpace`,
  `iteratedAffineLine`, `iteratedAffineLineProj`, `iteratedAffineLine.coord`, and
  `Scheme.Hom.toIteratedAffineLine`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its finite interfaces,
  reexported by `AffineSpacePurityComparison`: `ordinaryFiniteLine`,
  `shiftedLine`, `shiftedLinePullback`, `lineCoefficientIso`, `annihilates`.
- `Sheaf.Paper.AffineLinePurityComparison`: `AffineLinePurity.integration`,
  `coefficientUnitIso`, and the actual coefficient-first projection interface.
- `Sheaf.Paper.AffineSpacePurityComparison`: fixed-scalar `D`, `C`, `tensorIso`,
  `inverseImage`, `inverseImageComp`, `inverseImageId`, `inverseImageTensorIso`,
  `projection_geometry`, `tower_noetherian`, and `exponentUnit`.
- `Sheaf.Paper.FiniteProductCompactification`: `FiniteProductGeometry`,
  `finiteProductGeometry`, `finiteProductExternal`, `finiteProductChosenForward`.
- `Sheaf.Paper.FiniteForwardProductSymmetry`: the normalized
  `finiteForwardCompactificationComparison` (reexported by the preceding module).
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek*`:
  `rightDerivedLowerShriekOfCompactification` and its actual base-change map.
- `Sheaf.Paper.FiniteTorAmplitudeSites` reexports the fixed-module pro-etale
  `DerivedCategory.constructibleFiniteTor`; no duplicate ctf predicate is defined.
- `Sheaf.Paper.FiniteSiteTensorProjection`: `VectorIntegrationSite.projection`
  and `symmetry`, reexported by affine-line purity.
- Mathlib `MonoidalCategory` associators/unitors/whiskered isomorphisms and
  `Equiv.Perm.decomposeOption`, `finSuccEquivLast` build the tensor permutation.

Two dependency records need no repair: the compact-support record explicitly
retains its original fixed-scalar realization, which is the one used here, and
the exchange/projection record explicitly retains its finite specializations.
The relative-Kunneth node is cited by this item for its displayed forward word,
not for its abstract-datum isomorphism theorem. `finiteProductChosenForward`
is the existing concrete realization of that same word; importing or applying
`relativeKunneth` would add exactly the datum the item excludes. No such theorem
is applied and no alternate forward map is invented.

Edge cases checked by reading the definitions and signatures: n=1 and ramified
E are retained by the unrestricted coefficient presentation; r=0 gives one
factor, identity kappa, leaf tree, trivial Fin 1 permutation, and trace itself.
There is no zero-factor V_m in the statement; all binary factors are positive.
Trees permit every positive number of leaves and all planar bracketings. Empty Y
is not excluded by any instance or hypothesis. Characteristic two requires no
sign division. K may have odd shifts, zero cohomology or arbitrary finite Tor
interval; it is never interchanged with a Tate factor. The sign clause permits
zero block lengths as the harmless integer identity.

Searches actually run (the wrapper log is `searches.jsonl`):

- LeanFinder: compact-support integration of even Tate tensor powers under
  coordinate permutations: eight unrelated beta/zeta/symmetric-power/measure hits.
- LeanSearch: derived compact-support integration of even Tate tensor powers and
  coordinate permutations: eight derivative/symmetric-power/integral hits.
- Loogle: braided/monoidal categories: generic braided-category interfaces;
  monoidal category plus NatIso.app: no hits, unknown indexed identifier.
- Mathlib grep: Kunneth/Koszul: regular-sequence, local-cohomology and covariant
  derivative files; Tate-product/compact-product/coordinate-permutation under
  CategoryTheory: only a comonoid tensor-product comment. None state this item.
- `rg` under the project's WeilConjectures and Sheaf trees and literal item-id
  search under WeilConjectures: no existing statement of this item. Existing
  concrete forward and coefficient constructions were reused. The downstream
  affine-space composition module has its own coordinate presentation; it cannot
  be imported as a prerequisite of its proof, so this owning map interface uses
  the common recorded universal coordinate constructor directly.
- Blueprint searches `even line product` and `positive Tate product` returned
  zero matching blueprint nodes; DAG regex/id searches found no node for the
  assembled concrete positive Tate product/permutation map vocabulary.

## Second reading by N9

The dispatcher explicitly prohibits starting other agents and assigns the
maintainer the independent review. This section records a second self-reading,
not a claim of review by another worker. The node, current blueprint proof and
both module files were reopened for the hypothesis/clause audit above.

The second reading caught a missing `SymmetricCategory` instance in the concrete
fixed-scalar derived interface. The permutation construction now takes the
published canonical K-flat symmetry directly; the theorem supplies that actual
map and no extra structure hypothesis. It also checked the dependent Pi-binders
in the recursive permutation helpers, the r=m-1 convention, the concrete forward
orientation, and the coefficient-first order. The line-unit identification is
canonical and trace is not assumed to equal hU. The signed coefficient equality
is included explicitly, beyond the numerical sign identity. No mathematical
clause was dropped or changed. Independent mathematical review remains with the
maintainer, as specified in the worker brief.

## New nodes

`def-pur-even-line-product-maps` supplies the assembled map vocabulary needed by
this statement: positive Tate external powers, the actual forward product and
its stipulated inverses, binary tree iterations/associator normalizations,
signed finite tensor permutations, the actual coordinate-induced exchange
maps, and coefficient-first projection integration. The new module also states
the precise Cartesian geometry and bounded-origin/projection applicability
needed to make those definitions type, with full proof docstrings and without
assuming those facts in the consuming theorem. Its source is the current
blueprint's coordinate regrouping and even-sign calculation, expanded by the
item's concrete finite proper/open argument. LeanSearch, LeanFinder, Loogle,
Mathlib grep, project grep, DAG search and blueprint search found no existing
assembled interface. It reuses the existing Tate, derived tensor, affine-space,
compactification, exchange and projection notions rather than replacing them.
This separate definition node also keeps the definition module and theorem
module within the per-file compilation limit.
