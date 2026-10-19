## Worker report

Item: det-lem-int-tensor-pullback. Group N3, stage 2, 2026-10-18.
Module: `Sheaf.Paper.IntegralTensorPullback`.
Main declaration:
`AlgebraicGeometry.ProEtale.IntegralTensorPullback.preserves_and_completed`.

The module states both numbered clauses, including restriction to the discrete
constant integer scalars and compatibility of completion units. All theorem
proofs are `sorry`; all definitions have actual data. The helpers belong to the
canonical arrows and coefficient specializations of this node and are listed in
`lean.declarations`. Their docstrings give source places and proof plans. There
is no change to the mathematical node, no new node, and no dependency repair.

Hypotheses, one by one:

* The prime ell is `(l : ℕ) [Fact l.Prime]`.
* An arbitrary finite extension E of Q_ell is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. E is not restricted to
  the base field or to intermediate fields of one chosen algebraic closure.
  Integers, topology and positive-power quotients use the recorded
  `Padic.coefficientExtensionIntegers` and `DerivedNakayama` constructions.
* The standing field is `(k : Type u) [Field k]`, with `(p : ℕ) [CharP k p]`,
  `_hp : 0 < p`, `_hpl : p ≠ l`. No perfectness or algebraic closedness is added.
* The schemes are `{X Y : Scheme.{u}}` with their separate
  `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]` structures. For EACH
  structure map, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` render
  separated finite type over k. The latter two jointly express finite type.
* The arbitrary k-morphism is `(g : X ⟶ Y) [g.IsOver (Spec (.of k))]`.
  No smoothness, properness, surjectivity, or nonemptiness is assumed.
* The coefficient category is `DerivedCategory (AdicCompletion.Modules l E Y)`:
  internal modules over the continuous condensed integer ring pulled from the
  point. This is not a category of modules over the discrete constant ring.
* Membership in Dbc is `_hK : constantModelBoundedConstructible
  (DerivedNakayama.integerRing l E) Y K`. This is the dependency's corrected
  finite-CONSTANT-scalar-model notion, rather than arbitrary local presentation
  matrices of the older upstream constructibility predicate.

Clauses and arrows, one by one:

1. The first conjunct is `constantModelBoundedConstructible ... X
   ((CondensedRing.upperStar ... g).mapDerivedCategory.obj K)`. Cartesian
   coefficients make this inverse image exact, so `mapDerivedCategory` is the
   exact realization of the recorded total left-derived pullback. No new
   functor or private version of constructibility is introduced.
2. For every K-flat representative P and isomorphism `Q.obj P ≅ K`, the second
   conjunct states `IsIso (Q.map (comparison l E g P))`. Quantifying all such
   representatives is how the canonical derived arrow is represented; it is
   not an extra hypothesis on K. The existing K-flat resolution API supplies
   representatives for every object of this category.
3. `tower` uses the recorded `AdicCompletion.level`, `levelStep` and `levelUnit`.
   At index n these are tensoring a K-flat representative with the quotient by
   pi^(n+1), its quotient transition, and its quotient-unit map. Omitting the
   zero quotient is the cofinal positive-exponent indexing of the paper's tower.
4. `pulledTower` applies the exact `CondensedRing.upperStar` to the ENTIRE tower,
   including all maps. `comparison` applies the generic strict augmentation to
   its pulled-back quotient-unit natural transformation. It includes the
   canonical constant-functor composition isomorphism. It is not a freely
   chosen map in a distinguished triangle.
5. The target `integralOperationsRoos (pulledTower ... P)` is the existing strict
   `Cone(1-shift)[-1]` construction. `augmentation` uses its actual product legs
   and zero degree-minus-one homotopy. The compatibility needed for the
   cocone lift is a named theorem with a proof plan. Pro-etale countable product
   exactness is imported by the existing operations module, so this strict
   Roos model computes the required derived inverse limit.
6. `constantRing` is the existing constant-ring functor applied to the integer
   ring (with the required ULift into coefficient universe u+1).
   `constantToIntegral` is constructed by sheafification from the map taking a
   scalar to its constant continuous function. It is not an unspecified ring
   homomorphism. Its multiplicativity is a named theorem. `restriction` uses
   `Mod.comap` of its pullback, and thus changes the scalar action while keeping
   the underlying additive sheaf.
7. `constantFinite` is the SAME finite quotient module with scalar action
   restricted to the constant integers. Finite continuous coefficient rings
   are the constant finite quotient rings. `constantUnit` is the actual
   inclusion of the constant regular module in the restricted continuous
   regular module, constructed with `Mod.homMk`, not a chosen module morphism.
   `constantLevel`, `constantStep`, `constantTower`, and `constantTowerUnit`
   therefore express the constant-scalar derived reductions and their units.
8. `constantPulledTower` and `constantComparison` give precisely the tower and
   unit of Stacks 099N(2),(5). Restriction of integral K-flat models computes
   these constant-scalar reductions: the constant-to-completed scalar map is
   flat, as in the recorded constant-completion equivalence.
9. The last existential is an isomorphism from the scalar restriction of the
   continuous-coefficient target to that constant-scalar completed-pullback
   target. The displayed equation equates the restricted `comparison` followed
   by this isomorphism with `constantComparison`, after the canonical source
   identification `restrictionPullbackComplex`. Thus the scalar assertion
   includes the unit, not merely an abstract isomorphism of targets.
10. `restrictionPullback` is chosen only from an EXISTENCE-AND-UNIQUENESS theorem.
    Its normalization is an equality on all scalar-extension tensor generators
    using `Mod.extendπ`; it determines the natural isomorphism itself. It is
    not a choice from a bare Nonempty type. This is the cartesian coefficient
    square's canonical restriction/inverse-image comparison.

Dependency declarations and their modules:

* `sk-def-sfb-dc-setting`: the explicit field/scheme binders follow the convention
  recorded by `CondensedRing.compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  No compactification is chosen for this arbitrary inverse-image assertion.
* `def-weil-l-adic-coefficient-extension`:
  `Padic.finite_coefficientExtensionRing` in
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, with its imported
  integer/quotient constructions.
* `sk-def-sfb-pulled-back-coefficients`: `coefficientRing`, `condensedRingObj`,
  and `upperStarFromPoint` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
* `sk-def-sfb-derived-categories`: Mathlib `DerivedCategory` and `Q`, exported
  through `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and
  the existing derived module framework. No second derived category is defined.
* `sk-def-sfb-constructible`: `constantModelBoundedConstructible` and
  `IsConstantModelConstructible`, in `Sheaf.Paper.CondensedConstantConstructibility`.
* `sk-def-sfb-module-derived-pushpull`: `moduleObjectDerivedPullback` in
  `Sheaf.Paper.CondensedModuleDerivedPushpull` names `(upperStar ...).leftDerivedFunctor`;
  we use its exact inverse-image presentation `(upperStar ...).mapDerivedCategory`.
  These have the usual canonical exact/left-derived comparison. The module is
  publicly imported and is not replaced by another derived construction.
* `sk-def-sfb-derived-tensor-hom`: the derived tensor monoidal structure and
  K-flat calculation interfaces in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`; quotient levels
  use the recorded specialization `AdicCompletion.level` of this tensor.
* `sk-def-pe-derived-completion`: `AdicCompletion.Modules`, `finiteModule`,
  `quotientStep`, `finiteUnit`, `level`, `levelStep`, `levelUnit`, and the
  strict completion convention in `Sheaf.SixFunctors.ProEtale.DerivedCompletion`.
* `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcQbarCompletedPullback`
  publicly retains the integral strict-tower completed-pullback interface. Its
  primary Qbar functor is not used as the integral coefficient category. The
  present strict tower is the internal-module presentation of that same
  quotient-tower definition, retaining the augmentation and not assuming a
  stronger coefficient datum or a chosen finite extension in Qbar.
* `def-weil-proetale-inverse-image`: `Scheme.proEtaleSheafInverseImage` in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, also represented by the
  `upperStar` inverse image in the imported internal-module framework.
* `def-weil-pbc-constant-sheaf`: Mathlib `CategoryTheory.constantSheaf`, through
  `sfbPointConstantRing` in `Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients`.
* `def-pc-sheaf-restrict-scalars`: Mathlib `SheafOfModules.restrictScalars`,
  module `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`. In the internal
  module encoding its existing operation is `Mod.comap`. The general
  `sectionModuleComapIso` in `Sheaf.Paper.ContinuousCoefficientModuleEncoding`
  identifies the two existing encodings; no new scalar-restriction operation
  or definition-node repair is needed.
* `def-weil-derived-limit`: `CategoryTheory.IsDerivedLimit` in
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`. The existing
  `WeilConjectures.integralOperationsRoos` in
  `Sheaf.Paper.IntegralOperationsWellDefined` is its strict product/cone model.

All proof dependencies with recorded modules are imported (publicly when also
used by the statement, otherwise privately). The two currently unstated
proof-only nodes `sk-lem-int-integral-heart` and `sk-lem-integral-models` are
referenced by the complete proof docstring; their statements are not needed to
elaborate this stage-2 statement. No wait or downstream completion theorem is
used to define the arrows.

Edge cases checked against the formulae before drafting and on rereading:

* Empty X, empty Y, zero K, and empty strata are permitted; no nonempty or
  invertibility-in-the-empty-field inference is introduced.
* g = identity is covered by both exact inverse image and the scalar
  comparison's tensor-generator normalization. The completed unit is the
  quotient augmentation, with zero shifted coordinate.
* Non-smooth and non-proper morphisms remain included.
* Torsion coefficients and torsion K are allowed. No finite-Tor-amplitude or
  free-module hypothesis on K has been added.
* K-flat models may be unbounded; boundedness is a property of their derived
  object K, not of the chosen resolution's terms.
* n = 0 denotes pi^1, not pi^0. Every transition is the reduction from exponent
  n+2 to n+1, in the inverse direction.
* E and schemes have arbitrary common universe u; coefficient additive groups
  use u+1, matching the recorded small-site framework. The constant scalar map
  uses ULift rather than silently equating site object and morphism universes.

Searches for an existing exact statement or construction:

* `msearch.py ... leanfinder "Integral inverse image preserves bounded
  constructible complexes and agrees with completed pullback"`: returned
  constructible-set/Chevalley results, no matching integral derived statement.
* `msearch.py ... loogle '"completion", "pullback"'`: no results.
* `msearch.py ... leansearch "Pullback of bounded constructible integral adic
  sheaves equals completed inverse image"`: ordinary TopCat sheaf and
  SheafOfModules pullback interfaces; none states the two clauses.
* `msearch.py ... grep
  'completedPullback|[Cc]onstructible.*[Pp]ullback|[Pp]ullback.*[Cc]ompletion'
  CategoryTheory`: no Mathlib result.
* `rg` of the upstream `WeilConjectures` tree for the item id,
  completedPullback, and integralTensorPullback: no exact declaration.
* `rg` of `lean/Sheaf` for the same notions found the existing strict completion,
  coefficient transport and integral-model operations. IntegralModelsOperations
  has a preservation clause for finite intermediate coefficients, but does not
  give this arbitrary-E, unit-compatible two-clause statement. Its declaration
  therefore cannot be registered as an existing match.
* The existing constant-ring functor, scalar restriction, finite reductions,
  derived category, K-flat tensor and strict Roos complex were reused. Searches
  for the new namespace/helper names found no collisions.
* Missing or stale local recorded sources were read using `scompile.py --source`,
  including the current section/internal-module scalar encoding and strict Roos
  interfaces; no declarations were inferred just from their names.

No `STATEMENT-DISPUTED` issue was found. The node statement is unchanged.

## Second reading by N3

The dispatcher explicitly forbids starting another agent, so this is an author
rereading, not a claim of an independent worker review; the maintainer's
independent delivery review remains necessary. I reread the node, its nine
proof steps, the current blueprint statement/proof, the dependency records and
the final Lean signature together. Each hypothesis and clause is matched above.

The checks specifically found and avoided three possible semantic mismatches:
(1) using arbitrary-matrix constructibility instead of finite constant models;
(2) identifying constant and continuous integral coefficient categories;
(3) choosing an arbitrary cone map or unrelated target isomorphism without its
completion unit. The delivered statement uses the corrected dependency predicate,
separate scalar categories, explicit quotient augmentations, and an equality
of the two completion units. No mathematical node correction was required.
