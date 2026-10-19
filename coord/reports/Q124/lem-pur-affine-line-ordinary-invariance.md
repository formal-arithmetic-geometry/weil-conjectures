## Worker report

The module `Sheaf.Paper.AffineLineOrdinaryInvariance` states
`WeilConjectures.PurityFiniteSetting.affineLineOrdinaryInvariance`.
The statement is unchanged. There are no new DAG nodes and no dependency-record repairs.
The sole postponed proof is this theorem; its docstring contains all eight DAG proof
steps verbatim, with line wrapping. Every helper is a concrete specialization,
composition, natural transformation, or proposition naming the canonical maps of this
same node. No helper chooses an arbitrary morphism, a trivialization, an isomorphism,
or an object from a mere existence assertion.

Hypothesis and clause correspondence:

- Finite datum, k, ell distinct from p, the fixed finite extension, and positive n:
  `P : PurityFiniteSetting.{u}`. Its field, coefficients, extension and positive level
  are precisely the recorded datum; `P.Coefficient` is ULift of O_E/(varpi_E^n).
- Arbitrary k-scheme: `X : Scheme.{u}` with `[X.Over (Spec (.of P.field.k))]`.
  The structure map passed to the conclusion is `X ↘ Spec (.of P.field.k)`.
  There is no finite-type, separated, noetherian, quasi-compact or smooth hypothesis.
- The relative dimension-one projection: `a1OrdinaryProjection X`, literally
  `AffineSpace (ULift.{u} (Fin 1)) X ↘ X`, the Mathlib definition recorded in
  `def-sbc-affine-space`.
- Every signed twist: `r : ℤ`; `a1OrdinaryBaseModuleComplex P r` uses the existing
  `Scheme.finiteEtaleTateSheaf` on Spec k in degree zero. The annihilator is
  `ringChar P.Coefficient`, with `CharP.cast_eq_zero`, not the older exponent
  ell^(n/e). A nonzero finite residue ring has positive characteristic a power of
  ell, hence invertible on k. Exponent-change in the recorded finite-twist theorem
  identifies this realization with the specified finite twist. Thus no e | n
  restriction has entered. Exact pullback gives the twist on each k-scheme;
  pro-etale realization is the actual comparison inverse image.
- The actual module-valued etale and pro-etale derived units are the two `IsIso`
  clauses using `(upperStarLowerStarAdjunction (ModuleCat P.Coefficient) p).derivedPlus.unit`.
  The target is Rp_* p^* A(r)_X, canonically Rp_* A(r)_(A1_X) by the recorded finite
  twist pullback. It is not an existential isomorphism between endpoints.
- The corresponding underlying abelian units are also explicitly invertible in
  `A1OrdinaryInvarianceAt`. They use the same adjunctions with `AddCommGrpCat.{u+1}`.
  Keeping both records the coefficient-forgetting part of proof step 5 rather
  than silently identifying the two derived coefficient categories.
- Ordinary cohomology in every integer degree: `q : ℤ`; `a1OrdinaryEtaleH` and
  `a1OrdinaryProEtaleH` apply `DerivedCategory.Plus.homologyFunctor` in degree q to
  the right-derived ordinary global-sections functor. The inputs are sheaves in
  degree zero, so this is ordinary sheaf cohomology and is zero for q < 0.
  Bounded-below injective resolutions compute the stated unbounded ordinary
  operations on these inputs; no coefficient completion is used.
- Canonical pullback is the unit followed by the canonical Leray isomorphism,
  then the canonical composition transport of the twist. The two `IsIso` clauses
  on `a1OrdinaryEtaleProjection` and `a1OrdinaryProEtaleProjection` are precisely
  p^*:H^q(X,A(r)) -> H^q(A1_X,A(r)). Leray uses the published equality of sections
  of a direct image and the exact inverse-image adjunction preserving injectives.
- Naturality in X: the final universally quantified clause ranges over every
  `X' : Scheme.{u}` and `v : X' ⟶ X`; the induced k-structure is v followed by a.
  `a1OrdinaryProjectionSquare` is Mathlib's actual affine-space base-change square.
  In both topologies, `a1OrdinaryUnitNatural` is exactly the unit/exchange equation
  of proof step 8, using the counit mate `a1OrdinaryExchange` of the specified
  inverse-image square. `a1OrdinaryEtaleBaseNatural` and its pro-etale counterpart
  state the commuting square on ordinary cohomology with all four canonical edges.
- Naturality in finite coefficient maps: the global pullbacks and projection maps
  are `NatTrans`, on the whole base derived abelian-sheaf category before evaluation
  at `P.a1OrdinaryBaseComplex r`. Their type therefore includes the naturality
  equation for every base coefficient morphism. This covers the underlying maps
  of finite coefficient extensions/reductions, including different rings and
  levels, without restricting to A-linear endomorphisms or choosing generators.
  The module units are likewise the published natural adjunction units. Ring
  actions may be forgotten for cohomology and its naturality; the module unit
  invertibility and comparison are separately retained above.
- Canonical comparison: `A1OrdinaryModuleUnitsCompared` uses the recorded
  `fixedComparisonDirectImageMatePlus` and `fixedComparisonPullbackPlus`, and
  equates their composite with the actual pro-etale module unit. The underlying
  abelian version is `a1OrdinaryUnitsCompared`, using the same underived canonical
  mate and right-derived base-change construction. On cohomology the displayed
  equation says p_et^* followed by comparison equals comparison followed by
  p_proet^*. Both comparison edges are explicitly isomorphisms. The comparison
  map is the derived comparison adjunction unit followed by Leray for its actual
  restriction functor, never a chosen map between isomorphic groups.

Dependency declarations inspected and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `forgetEtale`, the quotient-ring construction, and the existing
  field and coefficient records. Its older `twistEtale` needs e | n and is
  deliberately not used for the arbitrary-level statement.
- `Sheaf.Paper.CoefficientTwistsDetailed`: `coefficientTateTwists`,
  `finiteCoefficientTwist` and `coefficientTwistLine`, read with their signed
  tensor/dual cases. The current statement uses the explicitly prescribed finite
  small-etale realization rather than introducing a second pro-etale twist.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, including its signed powers, evaluation,
  composition, tensor and change-of-annihilator clauses; its existing
  `Scheme.finiteEtaleTateSheaf` supplies the real coefficient sheaf.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  Both retain object universe u+1 and morphism universe u.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`
  and its retained ordinary sheaf-cohomology conventions. The actual RΓ is the
  existing `Sheaf.Γ` and `Functor.rightDerivedFunctorPlus`, followed by the
  published integer-degree homology functor.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `upperStar` and `upperStarLowerStarAdjunction`; together with the exact-derived
  functor and derived-adjunction modules these give the recorded direct image,
  inverse image and named unit without a new construction of those notions.
- `Sheaf.Paper.SfDerivedDirectImage`: the finite-level ordinary image of
  `def-weil-derived-direct-image` is computed by the same ordinary right-derived
  pushforward; its additional integral Roos tower is not used at finite level.
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and its published
  `GlobalSections`/`Coherence` modules: the ordinary `ProEtale.upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction`, `upperStarComp`, and
  `globalSectionsLowerStarIso`. These are the fixed-coefficient sheaf model of
  `def-weil-pbc-proetale-operations`, equivalent to its intrinsic constant-ring
  module presentation. No new operations or extra assumptions are introduced.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its `over` instance,
  `map`, and `isPullback_map`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus` and `fixedComparisonPullbackPlus`.
  Their docstrings fix the canonical mate, and not just its endpoints.

Imports include the published statement and proof plan wherever compatible. Two
broad imports must be omitted: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
and `Sheaf.Paper.FiniteDirectImageComposition` load
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`, which
redeclarates `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` already owned by
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso` through the required ordinary
global-sections and coherence modules. The compile diagnosed that exact conflict.
Following the launcher's explicit duplicate-import repair instruction, the module
uses the smaller ordinary upstream interfaces and the generic canonical derived
compositor instead. The mathematical dependency and its node record are retained.
No shared or upstream module was edited.

Edge cases checked: X empty, disconnected, non-quasi-compact, nonseparated and
nonnoetherian; n=1 and n not divisible by the ramification index; r=0, positive and
negative r; q<0 and q=0; identity and arbitrary v. A1_X -> X is affine independently
of these properties of X. All signed twists are actual sheaf tensor powers/duals;
the base pullback and comparison preserve their canonical identities. Negative
cohomology is the homology of a nonnegative injective resolution. The zero coefficient
object and zero coefficient maps cause no choice or nonemptiness issue. Universes
are explicitly bound; the coefficient group/module categories use u+1 without
identifying the small-site object and morphism universes.

Searches performed for an existing exact declaration:

- msearch.py leanfinder: "ordinary affine line homotopy invariance finite torsion
  twists derived direct image etale proetale"; eight etale-site and etale-morphism-definition hits,
  no matching cohomology/unit statement.
- msearch.py loogle: `"AffineSpace", "rightDerived"`; OK, zero hits.
- msearch.py grep: `affine.*line|homotopy` in Mathlib/AlgebraicGeometry; one unrelated
  elliptic-curve affine-point hit.
- msearch.py leansearch: "affine line homotopy invariance finite etale sheaf cohomology";
  eight hits on affine topological homotopy, cotangent cohomology and etale stability,
  none on the required ordinary affine-line unit.
- rg in upstream WeilConjectures and lean/Sheaf for affine-line/ordinary invariance,
  affine-line units and the proposed declaration names; the existing finite-type
  affine-line statement and supported affine-line consumer are not this statement.
  The supported theorem is downstream and is neither imported nor used.
- grep of the item id in the slopmaster2 source found no exact declaration. The
  upstream Lean-name index has no `affineLineOrdinaryInvariance` or `a1Ordinary` match.

Read the item's statement, all eleven statement-dependency statements and bindings,
their source signatures and docstrings, both source blueprint proof files, and the
unit section. The item is the arbitrary-base refinement, not the unit statement
itself. The existing repair note is a resolved stage-1 re-splitting note and does
not withdraw a stage-2 interface. No counterexample or statement correction found.

Validation: the complete module passed scompile.py in both its sandbox and library
positions with no errors or warnings (9.1 s and 10.3 s for the final revision).
The prescribed deliver2.py --no-push returned OK: commit 57308753f7 passes the
preflight and compiles. Width check: no lines over 100 characters. Exactly one
sorry; only the node field lean changes. No global build or direct Git command
was run.

## Second reading by Q124

The dispatcher explicitly prohibits starting other agents, so this is a distinct
self-review pass with the final node and source open, not a claim of an independent
second worker. The maintainer's independent delivery review remains authoritative.
I checked the finite datum and positive level against the actual P fields, both
module units against their adjunction endpoints, every conjunct of
`A1OrdinaryInvarianceAt` against the original statement, and each naturality square
by its domain and codomain. This pass added the module-valued units and their
canonical comparison equation explicitly, preserving scalar actions alongside the
ordinary abelian-cohomology formulation. It also caught the older P.exponent
interface's e | n restriction, which is avoided by the existing ringChar finite
realization, and removed the two conflicting broad compatibility imports described
above. The theorem's universes, negative q, signed r, arbitrary-base quantifier,
coefficient natural transformations and canonical comparison are retained. There
is exactly one sorry, in the named theorem belonging to this DAG node.
