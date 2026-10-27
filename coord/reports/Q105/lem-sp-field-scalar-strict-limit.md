## Worker report

The module `Sheaf.Paper.FieldScalarStrictLimit` states
`SheafOfModules.fieldScalarStrictLimit`. Its sole theorem has proof `sorry`.
The other declarations have full data: `FiniteFreeScalarArrow` bundles the existing
finite-power basis hypothesis, `ScalarStrictLimitComparison` packages the equations
of this very node, and `exactDerived`, `exactDerivedComp`, `exactDerivedUnit` expose
existing localization constructions with explicit exactness witnesses. There is no
second tensor, derived category, strict tower, Roos cone, or scalar comparison.

Source read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md`, paragraph (1),
whose finite-free argument is refined by this DAG node's six proof steps. All six
steps are reproduced in the theorem docstring. The archived source named by the node
was also checked. No statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Scheme T: `T : AlgebraicGeometry.Scheme.{t}`. A chosen small site model is
  `C : Type u`, `[SmallCategory C]`, `e : C ≌ T.ProEt`, and
  `hJ : J = e.functor.inducedTopology (Scheme.ProEt.topology T)`. Thus the site is exactly
  a small model with transported pro-etale topology, not an arbitrary site with
  an unused scheme parameter. The object and Hom universe equality is on the
  chosen small model, not on the original pro-etale category (whose two
  universes need not coincide). All rings/modules live in the common ambient
  universe u, as the node's small-site size convention requires.
* R_T and S_T are `R S : Sheaf J CommRingCat.{u}`. `a.val : R ⟶ S` is the ring
  map. `FiniteFreeScalarArrow` requires existence of d and an isomorphism from
  the finite product of d unit R-modules to the scalar restriction of the unit
  S-module. In an abelian module category this is the finite free basis, including
  d = 0. No chosen basis is part of the map.
* The categories are the recorded `ringedSiteModules` and Mathlib's unbounded
  `DerivedCategory.{w}`. The two `HasDerivedCategory` families are universe
  choices of localization, not mathematical boundedness or exactness hypotheses.
* Ordinary scalar extension is precisely existing `RingedTensor.tensorFunctor`,
  sectionwise change of rings followed by module sheafification. Scalar extension
  on strict towers is exactly `projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val)`.
  Positive paper index n+1 is Lean index n. `mapDerivedCategory` of this exact
  functor is its unbounded derived scalar extension; the existing exact-functor
  localization factorization identifies it with the universal derived tensor.
* Exactness of scalar extension and termwise extension is asserted by the first
  four conjuncts. The following ordinary witnesses `hlim`, `hcolim`, `htlim`,
  `htcolim` are universally quantified *inside the conclusion* so the later
  syntax can use the just-asserted exactness. They add no input hypothesis.
* `L R` is total right derived inverse limit, explicitly certified by
  `(L R).IsRightDerivedFunctor (roosDerivedUnit (rho R)) ...`. `rho R` is a
  natural isomorphism from localization of the actual `roosF` to Q followed
  by L. Its unit is explicitly Q of the canonical ordinary-limit inclusion
  `roosι`, followed by rho, so this fixes the required projection-normalized
  Roos realization, rather than choosing an arbitrary identification of cones.
* The family `cmp a` contains `comparison : L R ⋙ C ≅ C_tower ⋙ L S`.
  Its components are exactly lambda_K and are isomorphisms for every unbounded
  object K. The natural isomorphism lives on D(entire strict towers); this is
  naturality for roofs of entire tower complexes, not just level evaluations.
* `normalized` fixes lambda as the derived ordinary scalar/limit map through
  `limit.post`, the exact localization factors, and the two canonical units.
  `cone_realizes` identifies that SAME lambda with the actual chain comparison
  after localization and rho. Thus the theorem cannot be satisfied by an
  unrelated triangle filler.
* `beta_projection` says that its nth projection is F(pr_n).
  `beta_transition` says beta F(1-s) = (1-s) beta. Here `roosU` is the existing
  `towerTransitionEndomorphism`, literally id minus `towerProductShift`, whose
  nth projection is pr_(n+1) followed by t_n. `cone_first` and `cone_second`
  apply this same beta in both product coordinates, using the existing
  shifted-cone coordinates `roosχ`. They include the actual cone differential
  and its shift signs through a chain isomorphism, not just objectwise maps.
* For EVERY finite basis theta, the theorem supplies phi satisfying the
  pure-tensor coordinate formula using `theta.inv ≫ Pi.π`, and its finite-sum
  inverse using `Pi.lift (fun j ↦ if i = j then 𝟙 _ else 0) ≫ theta.hom`.
  These are the existing predicate's formulas expanded inline, without a new
  definition or a theorem dependency for plain definitions. The displayed (p,n,i) equation
  says beta sends each basis/product coordinate to that same coordinate.
  These equations render ((x_i,n)_n)_i -> ((x_i,n)_i)_n. Since beta and lambda
  were selected before theta and quantified independently of it, they are
  independent of basis. The product and cone maps are S-module morphisms,
  and lambda lives in D(S-modules), which renders S-linearity.
* Successive finite-free maps a,b have a finite-free composite ab with
  `ab.val = a.val ≫ b.val`. The ordinary A is fixed on every local pure tensor
  by z tensor (s tensor x) -> b(s)z tensor x, and its inverse by insertion of 1.
  AT is the same isomorphism on every tower level. `exactDerivedComp` is the
  existing `Functor.mapDerivedCategoryCompNatIso`, so the derived equation
  uses precisely the balanced derived associator and its termwise tower
  version. Its left side is the successive lambda maps followed by L(AT),
  and its right side is A at L(K), then the direct lambda.
* Identity: `a.val = 𝟙 R`, U sends r tensor x to r*x, and UT has exactly
  those components. The last equation says lambda followed by L(UT_D) is
  U_D at L(K), where `exactDerivedUnit` is the canonical localized identity
  unitor. This is the identity comparison under the standard unitors.
* There are no boundedness, constructibility, completeness, or normalization
  binders on tower complexes or on K. No source clause has been removed.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  `Mathlib...DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`, factors.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`;
  both already retained by the live `lem-pur-derived-change-of-rings` record.
  Its objects/maps are fixed, with the
  universal counit on complexes, K-flat invariance/computation and pointwise
  everywhere-defined existence, not a bare Nonempty arbitrary functor.
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, the
  recorded total-derived limit with evaluation, triangles and K-injective unit.
* `Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport`:
  `SheafOfModules.finiteFreeStrictTowerTransport`, read including the canonical
  ordinary comparison, exactness, derived tensor factorization and three
  normalized Roos squares in `FiniteFreeStrictTowerTransport`.
* `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosU`, `roosχ`,
  `roosι`, `roosDerivedUnit`; these define the actual cone and projection unit.
* `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`.
* `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `Scheme.ProEt.countableProducts_exact` (proof dependency).
* The finite-basis coordinate predicate and its basis maps are expanded inline
  using Mathlib's `Pi.π`, `Pi.lift`, identity and zero morphisms, and finite sums.
* `Sheaf.Paper.RingedTopoiTensorSections`: `ringSheaf`, `restriction`,
  `tensorFunctor`; `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram`:
  `scalarPure`. These existing notions are added to stmt_deps via their landed
  definition owner nodes, along with the landed Roos owner node.
* `Sheaf.CategoryTheory.StrictProjectionLimitData`: `projectionPost`, owned by
  `def-sbc-strict-projection-tower-data`, now explicitly cited in stmt_deps.
* `Sheaf.Paper.RingedScalarExtensionComplexAdjunction`: the existing
  `CategoryTheory.scalarExtension_additive` instance is now imported directly;
  its definition owner is cited as well.
* `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle`:
  `Functor.mapDerivedCategoryCompNatIso`; the upstream exact functor API also
  supplies `mapDerivedCategoryNatIso`, `mapDerivedCategoryIdIso`.

Edge cases checked before writing: d=0 (S is the zero module/ring; no positivity
or nonzero assumption), zero towers, constant and non-normalized towers, unbounded
complexes, empty schemes, identity scalar maps, arbitrary ramified origin of a
finite basis, successive extensions including zero ranks. The coefficient ambient
universe is allowed to be any universe large enough for the chosen small site;
no equality of the original pro-etale object and morphism universes is imposed.

Searches (all with prescribed msearch.py, group Q105/item id):

* LeanFinder: "Finite free extension of ring sheaves commutes canonically with
  strict derived inverse limits, with Roos coordinates and scalar composition".
  Eight hits: free-sheaf mapFree/ιFree, condensed-solid and ordinary adic-completion
  lemmas. No match for the whole theorem or its composition/coordinate clauses.
* Loogle: "CategoryTheory.Limits.piComparison, CategoryTheory.Limits.limit.post".
  Zero hits; source inspection confirms the canonical ingredient maps.
* grep: "finite.*free.*(limit|product)|tensor.*(lim|prod)" in CategoryTheory.
  25 hits about unrelated tensor structures/limits. No match.
* LeanSearch: "Finite free scalar extension commutes with total derived inverse
  limit of strict sheaf module towers". Eight hits, including
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat and ordinary module
  extension/restriction adjunction; no sheaf strict-total-limit assertion.
* rg in both live `lean/WeilConjectures` and `lean/Sheaf` for strict-limit/scalar/
  tower/Roos phrases, and the precise names of all new declarations. The closest
  exact building block is finiteFreeStrictTowerTransport, whose full record lacks
  the successive-extension equation and the actual two-coordinate realization.
  Existing `StrictRoosModel`, finite basis coordinates and balanced scalar section
  calculus are reused. No full match. The item-id grep in WeilConjectures and
  full-name search in dag/lean_names_upstream.json have no hit.

No STATEMENT-DISPUTED and no correction of the item's mathematical statement.

## Repair of returned delivery

H2 (scalarPure): replaced the theorem-only statement dependency
`lem-sfb-scalar-inverse-image-tower-diagram` with its existing definition owner
`def-sfb-scalar-inverse-image-normalization`. The source module is still imported
for its existing scalarPure definition.

H2 (finite coordinates): expanded IsFiniteFreeScalarCoordinateIso and its
scalarBasisCoordinate/scalarBasisInclusion formulas directly in the theorem.
The formulas are identical to the existing definitions, including the inverse
finite sum, and create no duplicate notion. Removed the coordinate theorem's
statement dependency and its import. No new definition node is needed.

H13: removed the sandbox copy of `lem-pur-derived-change-of-rings.json` from this
delivery. The current live record already lists DerivedChangeOfRingsCochainModel
and its existence theorem alongside every ModuleCat.ordinaryDerived declaration;
it is preserved in full. There is no dependency-record replacement.

Advisory: added `def-sbc-strict-projection-tower-data` as the owner of projectionPost.
The additive instance formerly imported through the coordinate module is now
imported directly from RingedScalarExtensionComplexAdjunction, with its definition
owner cited. The mathematical node statement, proof and proof dependencies are unchanged.

## Second reading by Q105

This is the dispatcher's direct-worker self-check; no independent agent was started,
as explicitly required by this assignment. Independent review is the maintainer's.
I reopened the node and module and checked the map directions in `normalized`,
`cone_realizes`, the successive-comparison equation, and the identity equation.
The ordinary formula in normalization uses `limit.post` on the evaluated complex
rather than an arbitrary map. The coordinate record was generalized over its actual
functor argument to avoid expensive unfolding of concrete module tensor data; it
is instantiated only by the fixed tensorFunctor. Exactness witnesses were moved
from typeclass families to explicit ordinary binders inside the conclusion, which
preserves the claimed exactness while avoiding repeated typeclass searches. Both
cone coordinates and their degree offset p versus p+1 are retained. Basis theta is
quantified after cmp, so it cannot choose a different lambda. All correction-free
changes to stmt_deps cite the existing definition owners and remove theorem-only
references that had supplied plain definitions.

Validation: scompile.py compiled both the renamed sandbox and the actual library
module cleanly after the direct additive-instance import. No warning or error was
reported. The node's lean.statement was extracted verbatim from the repaired
signature. The delivery wrapper dry run printed OK: commit bbd5ce99bcd passes preflight
and compiles. No mathematical clause was removed to fix elaboration.
