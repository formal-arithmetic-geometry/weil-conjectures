## Worker report

Item: `lem-pur-condensed-tate-integral-tower`. Module:
`Sheaf.Paper.CondensedTateIntegralTower`. Main declaration:
`AlgebraicGeometry.Scheme.PurityIntegralTower.condensedTateIntegralTower`.
All other declarations are in that namespace and listed in `lean.declarations`.
The node statement, proof, and source record are unchanged. Two already recorded
dependencies are added for the reused finite-model and local-generator interfaces.

The module states reconstruction of the normalized finite Tate/unit towers using
the existing strict-tower, completed-coefficient, finite-purity, and origin
interfaces. It constructs the coefficient presentations and the underlying strict
tower; it does not prove the stage-2 theorem. Eight named theorems have `by sorry`
proofs and source/proof docstrings. Definitions and instances have real bodies.
The two choices of data are from **unique**, explicitly normalized existence
statements (`residueIso_existsUnique`, `completionIso_existsUnique`); there is no
choice of an unspecified coefficient object or unspecified comparison map.

Source reading: the node's historical source filename is no longer present in
the current blueprint. I read `literature/blueprint/latest/blueprint/`
`sec-smooth-purity/sk-thm-purity-transport/_section.md` and
`sk-thm-purity-transport.proof.md`, particularly the integral normalization and
reconstruction in Steps 1--2. The node supplies the detailed eight-step argument
for this auxiliary Tate/unit case. These sources give the same objects and maps;
no correction of the node statement is needed.

Hypotheses, one by one:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Field k: `(k : Type u) [Field k]`.
- Positive characteristic: `(hchar : 0 < ringChar k)`.
- Characteristic different from ell: `[Fact (ringChar k ≠ ell)]`.
- Schemes over k: `{X Y : Scheme.{u}}`, with `X.Over (Spec (.of k))`
  and `Y.Over (Spec (.of k))`.
- Separated over k: `IsSeparated` for each structure morphism.
- Finite type over k: `LocallyOfFiniteType` and `QuasiCompact` for each
  structure morphism, the Mathlib decomposition of finite type.
- The morphism is over k: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`.
- Smooth of pure relative dimension d: `(d : ℕ)` and
  `[SmoothOfRelativeDimension d f]`.
- Quasi-compactness/separatedness of f, its compactification, and Noetherianity
  of X and Y are **conclusions**, the existential `hfq`, `hfs`, `c`, `hX`, `hY`.
  They only install the geometric instances required by the recorded APIs.
  No properness, finite-field, perfect-field, algebraic-closure, or dimension
  bound is an extra hypothesis.

Clauses and objects, in the node's order:

1. The coefficient ring is the actual `PadicInt ell`, with the harmless site-size
   lift `Ring ell = ULift.{u+1} ℤ_[ell]`. `datum ell` has the actual ideal
   `Ideal.span {(ell : Ring ell)}`. It reuses `AdicCoefficientDatum`.
   `coefficientProperties` states exactly its proof fields, following proof Step 1.
2. Positive level n in the node is indexed by `n-1` in Lean: every finite ring
   is `coefficient ell (n + 1)`, the existing lifted `ZMod (ell^(n+1))`.
   `residueIso` is uniquely specified on every quotient class by
   `PadicInt.toZModPow (n+1)`. Thus it is the specified residue ring rather than
   an abstract finite ring. `coefficientIso` is this map on constant sheaves,
   composed with the recorded continuous-function/constant-sheaf comparison.
3. The completed sheaf is `pbcAdicCompletion T (datum ell)`, the limit of finite
   coefficient sheaves. `completionIso` identifies it with `purTwistZlCompletion`
   by the equation for **each actual projection**, not with the discrete constant
   p-adic sheaf. The small pro-etale site retains object universe `u+1` and
   morphism universe `u`; its coefficient modules have universe `u+1`.
4. `finiteTwist T ell n d` is the comparison-image of the recorded
   `line (coefficient ell (n+1)) (ell^(n+1)) ... T d`. This is the actual
   d-fold finite roots-of-unity line with shift `[2d]`. At zero it is the unit.
   On Y the finite object is literally the monoidal unit in `proCategory`.
5. `integralRoot` is the recorded inverse-limit root module `purTwistZlModule`,
   restricted along the projection-normalized `completionIso`. `integralLine`
   forms its ordered ordinary tensor power, with the actual coefficient unit at
   zero. `strictTower` applies the existing `localReductionModuleTower` to this
   line and to the actual completed-ring projections. Hence its maps are strict
   quotient maps, constructed before localization. `strictDerivedTower` places
   it in degree `-(2*(d:ℤ))` using `DerivedCategory.singleFunctor`.
   `M.tower = strictDerivedTower X ell d` and the analogous equality for Y
   pin the strict objects in `ReconstructionResult`.
6. The existential `M L : AdicTower` retains quotient-linear finite levels and
   their actual strict evaluations, transitions, and full cocycle; these are
   the fields of the dependency's `AdicTower`, not fresh weakened predicates.
   `eM`, `eL` identify the levels with the specified finite objects. These maps
   together with `M.evaluation`/`L.evaluation` are now fixed by the two
   `ProjectionNormalized` conjuncts (see the H3 repair below). In
   `Reconstructed`, the all-pairs equation intertwines `M.normalization` with
   `proTwistMap d (r b a hab).twist` on X and `unitReduction` on Y.
   The twist is the dependency's `CoefficientLineComparison`: `roots_power`
   specifies the root-power map, `generators` fixes the scalar/root formula,
   and `derived_normalization` fixes its derived map. Its `tensorPower` supplies
   the ordered tensor balancing. It is not an arbitrary line isomorphism.
7. `scalarComparisonMap` is constructed as the mate of
   `derivedRestrictionComparison` under the **specified** scalar adjunctions;
   `scalarComparison` is its `asIso`. The restriction comparison is the recorded
   identity-on-underlying-additive-sheaf comparison, using `scalars_comp`.
   This transports quotient actions between the existing finite-purity and
   continuous-function module presentations without changing the statement.
8. `ReconstructionResult` retains `FiniteSmoothSystem ell f d`. For every family
   of normalized `Level`s and `ReductionData` from that interface, it gives the
   reconstruction conclusion. Thus it applies to the finite smooth purity of
   the node. Each `Level` includes the diagonal/Kummer normalization; each
   `ReductionData` includes its actual finite coefficient square. Quantifying
   over these specified data adds no assumption or arbitrary alternative map.
9. `gammaUnit` is `proGamma` at the unit, preceded by `unitSource.inv`, where
   `unitSource` uses the recorded comparison-unit, pullback-unit, and tensor-unit
   isomorphisms. `exceptionalReduction` is the actual `proCoefficientMap`
   followed by exceptional image of `unitReduction`. Thus gamma and c have the
   precise source/target and normalization in the node.
10. The derived limits are literally `uniformReconstructionLimit (datum ell) M`
    and the analogous object for L. That definition is the recorded derived
    `Rlim` on strict towers, not a new limit object chosen by an existence theorem.
11. Membership in the completed integral constructible categories is
    `PbcIsBoundedConstructibleComplete T (datum ell) (uniformReconstructionLimit ...)`.
    This is the recorded generic predicate, specialized to the explicit p-adic
    datum. It includes intrinsic derived completeness, uniform constructible
    canonical reductions, and compatible retained etale-origin witnesses.
12. Canonical reduction is `uniformReconstructionCounit ... M n`, the adjunct of
    the actual `Rlim` projection through `M.evaluation`. `Reconstructed` requires
    it to be `IsIso` at every n. Its separate all-pairs normalization equation
    is written with `pbcReductionNormalization`, not just existence of unrelated
    finite isomorphisms. `ProjectionNormalized` additionally fixes the composite
    with `eM/eL` by the ordinary projection-induced balancing map, thereby
    identifying reductions with the named finite objects with their trace
    normalization, rather than only up to a scalar unit.
13. `reconstructedGamma` is exactly canonical counit, then `eM`, then realized
    `gammaUnit`. `IdentifiesExceptional` makes every such map an isomorphism and
    writes the all-pairs square with the realized `exceptionalReduction` and
    the canonical reduction normalization. This gives the finite exceptional
    tower identification and its composite/identity transitions. It asserts no
    integral exceptional inverse-image functor.
14. Every finite level has constructible cohomology by the universal `n q`
    `IsConstructibleProEtaleFixedModuleSheaf` clause. The `IsZero` clauses impose
    vanishing for `q ≠ -(2*d)` on X and `q ≠ 0` on Y. The same degree bound
    is retained on the reconstructed objects, as in proof Step 6. The exceptional
    values have their own explicit constructibility and degree clauses.
15. Compatible etale-origin witnesses for the canonical reductions are part of
    `PbcIsBoundedConstructibleComplete`, using the recorded bounded origins,
    coefficient reductions, unit, and quotient cocycle. Transport by the
    displayed projection-normalized `e` and counits gives the witnesses for
    the named finite levels; transport by `reconstructedGamma` gives them for
    the exceptional tower. No weaker degree-only constructibility condition
    replaces this origin condition.

Dependency declarations read and reused (module names have prefix `Sheaf.` unless
shown otherwise):

| DAG notion | Module and declaration |
| --- | --- |
| Adic datum | `Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficientDatum`, `pbcAdicRings`, `pbcAdicCompletion`, `pbcAdicProjection`, `pbcAdicQuotient` (datum structure is reexported from `CompletedAdicCoefficientDatum`) |
| Constructible tower | `Paper.BoundedConstructibleTower`: `Scheme.AdicTower`, `IsUniformlyBoundedConstructibleAdicTower`, `localReductionModuleTower` |
| Complete constructible | Recorded `Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`; underlying `Paper.BoundedConstructibleComplete`: `PbcIsBoundedConstructibleComplete`, `PbcHasCompatibleEtaleOrigins` |
| Finite smooth purity | `Paper.FiniteSmoothAdjunctionGeneralBase`: `Etale.FiniteSmoothPurity.finiteSmoothAdjunctionGeneralBase`, `FiniteSmoothSystem`; reexported `Level`, `ReductionData`, `proGamma`, `proCoefficientMap`, `proTwistMap` |
| Actual Tate lines | `Paper.PurTwistSheafLocallyFree`: `Scheme.pur_twist_sheaf_locally_free`; `Paper.PurTwistSheaves`: `purTwistZlModule`, `purTwistZlCompletion`, `purTwistZlProjection`, `purTwistFiniteRing` |
| Reconstruction | `Paper.ReconstructionUniformTower`: `Scheme.reconstructionUniformTower`, `uniformReconstructionLimit`, `uniformReconstructionCounit` |
| Smooth relative dimension | Mathlib `AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.SmoothOfRelativeDimension` |
| Scheme conventions | The node is a collection of Mathlib scheme/morphism conventions, used directly in the main signature, without inventing another definition |
| Roots | `AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`: `Scheme.proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityTransition`; finite purity uses the recorded etale roots and its comparison |
| Strict derived limit | `CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`: the independent-universe ringed strict-tower homotopy-limit construction, used through the reconstruction API |
| l-adic numbers | Mathlib `NumberTheory.Padics.PadicIntegers`: `PadicInt`; `NumberTheory.Padics.RingHoms`: `PadicInt.toZModPow`, its kernel and quotient compatibility |
| Sheaf tensor | `Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal`; ordinary sheaf tensor, not an invented bifunctor |
| Etale origins | `AlgebraicGeometry.FixedEtaleOriginWitness`: the recorded origin notion; `Paper.BoundedConstructibleComplete` retains its normalized compatible families |

The extra helper theorems are subclaims of this node's proof, not new mathematical
prerequisites. `coefficientProperties` and `residueIso_existsUnique` implement
Step 1; `completionIso_existsUnique` implements Step 2's projection comparison;
`scalars_locallyBijective`, `realization_exact`, `scalars_comp`, and
`scalarComparisonMap_isIso` implement the finite coefficient-presentation
transport used by Steps 2--6. Every theorem has a natural-language proof in its
docstring. Every helper has this item's source/blueprint attribution. The scalar
maps, restriction comparisons, mates, integral line, and strict towers are actual
constructions. No additional definition node or dependency repair was necessary.

Edge cases checked against the signature and definitions:

- The first index is `0`, representing exponent 1, never the zero coefficient ring
  of exponent 0. All comparable pairs use `Nat.add_le_add_right hab 1`.
- Equal indices and three-level composites are retained by `AdicTower.cocycle`
  and the equations quantified over all `a ≤ b`; they are not dropped.
- At `d=0`, `integralLine` is the unit and the shift degree is zero; finite
  reduction uses the scalar-unit comparison. Etale smooth maps are included.
- The prime 2 is allowed; no sign or odd-prime hypothesis occurs.
- Empty schemes and the empty smooth morphism are allowed: degree concentration
  is vanishing outside the degree, not an assertion of nonzero cohomology there.
- Arbitrary positive-characteristic fields such as `F_p(t)` are allowed. No finite
  field datum or perfectness hypothesis occurs in the main signature or result.
- Source/target universes are the genuine small pro-etale ones. The explicit
  essentially-small witness on derived restriction prevents accidental inference
  of equal site object/morphism universes.

Searches for an existing statement and notions:

- `msearch.py ND <item> leanfinder` with query
  `normalized inverse system of finite coefficient Tate twists reconstructs an integral l-adic object with canonical reductions`.
  Result: eight generic hits, including `BDeRhamPlus`, `InverseSystem.globalEquiv`,
  `InverseSystem.invLimEquiv_apply_coe`, and `AdicCompletion.piEquivOfFintype_apply`;
  none states this reconstruction with the finite-purity comparisons.
- `msearch.py ... loogle` with query
  `PadicInt.toZModPow, CategoryTheory.Limits.limit, SheafOfModules` returned no match.
- `msearch.py ... grep` with query
  `Tate.*[Tt]ower|[Tt]ower.*Tate|PadicInt.toZModPow` returned nine generic/p-adic
  occurrences; the residue API in Mathlib was reused, but no matching theorem.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Tate/integral/tower and
  reconstruction names, and exact-item `grep` on `lean/WeilConjectures`, found
  no exact declaration. `NativeIntegralTateTowerLimit` concerns inverse-image
  preservation for a different native finite-E tower.
  `SmoothPurityTowerReconstruction` uses a different normalized condensed ctf
  interface; neither states this node's strict-tower completed-category result.
- The project's existing datum, line, roots, finite purity, completed category,
  reconstruction, tensor, and origin definitions were reused instead of copied.

No `STATEMENT-DISPUTED` issue was found. The historical source pathname is noted
above; it does not require a change to the mathematical statement.

Validation: the repaired module is compiled with `scompile.py` at both the
sandbox and final library module names. All variables and universes are bound
explicitly; both `autoImplicit` and `relaxedAutoImplicit` are disabled. The file
has no line longer than 100 characters. Only the eight named stage-2 theorem
proofs are postponed. The final delivery dry run is recorded below.

## Second reading by ND

This is the worker's final clause-by-clause rereading, not a claimed independent
review by another agent. The dispatcher explicitly prohibits starting other
agents and assigns independent review to the maintainer.

I reopened the node and the final module. The rereading checked all hypotheses,
actual coefficient rings, the inverse-limit root object, zero-fold tensor,
strictness before localization, all comparable quotient indices, full cocycles,
canonical projection-induced reduction counits, the actual finite gamma and c,
the completed-category predicate including origins, and both cohomological
degrees. It also checked that geometric instance requirements are conclusions.
During preparation I pinned `M.tower` and `L.tower` to the explicitly constructed
strict quotient towers, so the result does not merely ask for unspecified towers
with isomorphic finite levels. The two coefficient-presentation comparisons
are normalized by residues/projections and restriction-adjunction mates.
The maintainer subsequently identified the H3 gap in this first rereading:
pinning the strict tower alone left the comparison `eM` free up to a unit. The
following repair supersedes that earlier assessment.


## Repair of H3

Return reviewed: immutable head `a09472f6d417`. The retained packet was inspected
and initially passed the delivery dry run, but that automated check does not
resolve H3. This delivery changes the Lean statement's normalization predicates;
it is not an unchanged re-push. No change of the mathematical node is needed.

`finiteSheaf` is the comparison-image of the existing ordinary finite root
power. `finiteModelIso` uses `CoordinateCounitArrows.baseTateIso`, exact site
comparison, exact coefficient realization, and their canonical shift/single
comparisons to identify the *specified* `finiteTwist` with the single complex of
that sheaf in degree `-2d`. It introduces no choice of a derived isomorphism.
`integralPure` is the actual sheaf-tensor pure section through the sheafification
unit; `integralGenerator` orders the integral root factors exactly as
`integralLine`, with scalar 1 for the empty tensor.

For every etale test U, pro-etale test W over U, finite roots z_i, and compatible
integral roots x_i, `ProjectionBalanced` requires the ordinary comparison b to
send the sheafified local generator `t • (a tensor z_1 tensor ... tensor z_d)`
to `(t * scalars(a)) tensor (x_1 tensor ... tensor x_d)` in the actual quotient
line. Compatibility is tested by `finiteTateLimitRootValue`: its construction
uses the actual `limit.π` of `purTwistZlOne`, not an abstract isomorphism between
lines. Both arbitrary coefficient sections t and finite scalar a are quantified.
These local root generators generate the finite root-tensor sheaf; after the
common pro-etale root cover, integral lifts exist and the formula determines b.
Thus its existential quantifier supplies a map characterized by its values, not
an arbitrary line isomorphism. This is Step 2's tensor-balanced projection map.

`ProjectionNormalized` pins the composite `finiteModelIso.inv`, `e.inv`,
`M.evaluation`, and exact evaluation of the specified strict-tower equality to
that ordinary b through the canonical restriction/single-complex comparisons.
Consequently the reconstruction counit followed by e is the projection-induced
map. The old transformation `(M,L,-eM,eL)` now violates this equation. If both
e and the abstract evaluation are simultaneously rescaled, their factors cancel
in the actual counit followed by e, so this cannot rescale `reconstructedGamma`.
The same argument applies to every coefficient unit, including nonconstant ones.

The Y conjunct uses d=0 and `finiteZeroIso`, itself the specified comparison-unit
isomorphism. There are no roots and the local formula is precisely the scalar
ring projection; in particular it fixes the unit generator to 1 tensor 1. This
pins eL together with L.evaluation. The invertibility facts `hXT`, `hYT` required
by `baseTateIso` are existential conclusions of `ReconstructionResult`, derived
from the original field/characteristic hypotheses; they add no assumptions.

All old constructibility, degree, compatible-origin, transition/cocycle,
exceptional-comparison and finite trace clauses are retained. The main theorem's
signature is unchanged. The main proof docstring's Step 2 now explains how to
prove the two projection normalization conjuncts from the local generators.
No new theorem is postponed and no definition contains `sorry`.

Additional dependencies read and reused:

- `def-trf-coordinate-counit-arrows`, module `Sheaf.Paper.CoordinateCounitArrows`,
  declaration `AlgebraicGeometry.Etale.CoordinateCounitArrows.baseTateIso`:
  the canonical regrouping of the ordered finite tensor and its shifts.
- `def-amb-finite-tate-site-comparison-data`, module `Sheaf.Paper.FiniteTateSiteDescent`,
  declarations `finiteTateEtalePowerGenerator`, `finiteTateEtaleRootValue`, and
  `finiteTateLimitRootValue` in `AlgebraicGeometry.Scheme`: the existing local
  finite root generators and the actual inverse-limit root projection.
- Existing Mathlib `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`,
  `Functor.commShiftIso`, and `DerivedCategory.singleFunctors.shiftIso` fix all
  exact functor and shift comparisons used in the displayed normalization square.

Repair searches:

- `msearch.py ... leanfinder` query `canonical tensor reduction of inverse limit
  of roots of unity normalized by its limit projections`: eight generic
  cyclotomic-character hits, including `toZModPow_toFun`; no matching theorem.
- `msearch.py ... loogle` query
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`: twelve hits,
  including this exact comparison, which is reused.
- `msearch.py ... grep` query
  `rootsOfUnity|singleFunctorCompHomologyFunctorIso`, subdirectory `Algebra`:
  four generic single-complex homology hits, no statement of this normalization.
- `rg` in the project's `Sheaf/` and `WeilConjectures/` located the actual
  finite-model, tensor-sheafification and inverse-limit root interfaces above;
  they are reused, with explicit independent site/coefficient universes.

Second reading of the repair: checked directions of b, the restriction of
`e.inv` followed by evaluation, the strict-tower equality transport, and the
shift degree `-2d`. Checked d=0 (empty tuple, ring projection), ell=2 (the first
level alone may hide a sign, but all positive levels are pinned), arbitrary
units (the formula tests every local generator), empty schemes (vacuous local
sections cause no nonzero assertion), and arbitrary positive-characteristic k.
No citer is edited: `def-pur-condensed-smooth-purity-iso` obtains exactly the
finite normalized reduction it needs. No `STATEMENT-DISPUTED` issue remains.

Final validation: repaired dry run `000c0b5eacf` passed server preflight and all
per-file compiles. Final self-check confirmed the exact signature record, all
48 declaration names, eight named postponed proofs, no diagnostic commands, and
100-character line width. Only `lean` and the two landed `stmt_deps` additions
differ from the read clone; the mathematical statement is unchanged.


## Repair of H2 (R1)

Return reviewed: immutable head `722ef048ce59`. The retained packet first passed
server preflight and compilation in dry run `3d2ee9abbc5`. That mechanical success
did not resolve the returned dependency ownership issue.

Replaced `lem-amb-finite-tate-site-descent` in the item's `stmt_deps` with the
already landed definition node `def-amb-finite-tate-site-comparison-data`.
Its `lean` record has `existing: true` and lists exactly the three definitions
used here: `AlgebraicGeometry.Scheme.finiteTateLimitRootValue`,
`AlgebraicGeometry.Scheme.finiteTateEtaleRootValue`, and
`AlgebraicGeometry.Scheme.finiteTateEtalePowerGenerator`.
I read their signatures and bodies in `Sheaf.Paper.FiniteTateSiteDescent` at
lines 114, 129, and 135, and checked their uses in `ProjectionBalanced`.
These are plain definitions; the module does not choose or use the conclusion
of `finite_tate_site_descent`. The existing public import remains appropriate.

The Lean file and the complete `lean` record are unchanged, as the return asks.
No mathematical statement, proof, other dependency, normalization predicate,
or previously accepted H3 repair was changed. The dependency table above now
names the definition node that owns these reused declarations. Final self-check
confirms that the three names are listed by that node, the obsolete theorem
citation is absent from `stmt_deps`, and the theorem signature still matches
`lean.statement` verbatim. The final repaired dry run is recorded below.

Final H2 validation: `scompile.py` passed at the sandbox and library module
names (53.7 s and 54.5 s). Repaired dry run `7231b639e6f` passed server
preflight and per-file compilation. Only the requested dependency ownership
replacement and this report changed relative to the retained packet.
