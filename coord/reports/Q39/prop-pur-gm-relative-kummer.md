## Worker report

The delivery states `prop-pur-gm-relative-kummer` as
`WeilConjectures.PurityFiniteSetting.relative_kummer` in
`Sheaf.Paper.PurityRelativeKummer`. The statement is unchanged. The two missing
statement-dependency interfaces are supplied in this delivery. No new DAG node is
introduced. This is stage 2: theorems have `sorry`; definitions contain real data.

Hypotheses and objects:

- The binder `P : PurityFiniteSetting` bundles the existing `FiniteFieldDatum`
  (`p,a,q,k₀,k`, primality, cardinality and algebraic closure), its existing
  `CoefficientDatum` (`ell` prime and different from `p`, fixed algebraic closure of
  `Padic ell`), a literal `IntermediateField` in that closure, its `FiniteDimensional`
  instance, and `level >= 1`. The ring `P.Ring` is precisely the published
  `Padic.coefficientExtensionRing`; `P.Coefficient` is its standard `ULift` for
  module sheaves on a site with objects in universe `u+1` and morphisms in `u`.
  This lift changes no coefficients. It imposes no equality of site universes.
- `h : P.ramificationIndex ∣ P.level` is the divisibility already explicitly assumed
  by the statement dependency `def-pur-affine-line-datum`. The ramification index
  is the order of ell in the existing DVR, with its existing uniformizer;
  `kummerLevel = level / ramificationIndex`, and `exponent = ell ^ kummerLevel`.
  There is no additional assumption that the characteristic does not divide N.
- `Y.Over (Spec k)`, `LocallyOfFiniteType (Y ↘ Spec k)` plus `QuasiCompact (Y ↘ Spec k)` and
  `IsSeparated (Y ↘ Spec k)` render exactly “separated finite-type k-scheme”.
- `Line Y` is Mathlib's `AffineSpace (ULift (Fin 1)) Y`;
  `lineProjection`, `zeroSection`, `Punctured`, `openImmersion` and
  `puncturedProjection` are respectively p, s, the basic open of the coordinate,
  j and j followed by p. `coordinateUnit` is the existing `Scheme.basicOpenUnit`. The optional
  torsor description uses `coordinateRootCover` and its projection, literal
  specializations of the published `Scheme.kummerCover` and `kummerCoverπ`.
- `twistEtale` is the published `Scheme.finiteEtaleTateSheaf` in degree one,
  built from the actual roots-of-unity kernel, its Z/r-module structure and
  sheafified scalar extension to A. It is not an arbitrary rank-one sheaf.
  `twist` and `constant` apply the exact canonical etale/pro-etale comparison
  inverse image to these sheaves. These are the usual finite pro-etale coefficients.
- `kummerEtale` applies `Scheme.kummerδ₀` to the actual unit, then
  `Sheaf.H.map rootCoefficientMap`. `rootCoefficientMap` is uniquely fixed by
  the formula `z ↦ 1 tensor z` on every etale section. The canonical map from
  module Ext to abelian Ext is `moduleClassToAbelian`: exact scalar forgetting
  followed by precomposition with the constant free-generator map Z to A.
  Its bijectivity theorem determines the module class uniquely. Thus the
  inverse used here is a specified bijection, not a choice of an unspecified
  class. `kummer` uses `Ext.mapExactFunctor` for the canonical site comparison;
  `coordinateKummer` uses the actual coordinate unit. No `HasKummerClass`
  hypothesis or unspecified Kummer generator is introduced.

Every conclusion is rendered as follows:

1. `RelativeKummerConclusions` first asserts `IsIso (relativeUnit ... p false)`
   and `IsIso (relativeUnit ... p true)`. These are precisely the untwisted and
   twisted derived units: the actual derived adjunction unit, followed by
   derived direct image of the canonical coefficient pullback. Its next
   conjunct is `∀ m : ℕ, 0 < m → IsZero (H^m (Rp_* A(1)))`.
2. Its fourth conjunct asserts invertibility of `H^0.map` of the twisted pi-unit.
   The source is canonically the twisted sheaf by
   `DerivedCategory.singleFunctorCompHomologyFunctorIso`. This is exactly the
   stated sheaf unit. It is also restriction through j after the p-unit:
   these are the units of the specified adjunctions and pi is literally j;p,
   so the adjunction composition law gives the stated equivalent description.
   `kummerGenerator` transposes `coordinateKummer.hom` along the actual derived
   pi-adjunction, takes H0 and applies `H0(K[1]) ≅ H1(K)`. Its source is the
   constant A-module sheaf using the same single/homology comparison. This is
   the Leray edge map followed by the section map sending 1 to kappa(t), not
   an abstract isomorphism of rank-one objects. The fifth conjunct says this
   exact map is an isomorphism of A-module sheaves.
3. The last conjunct is `∀ m : ℕ, 2 ≤ m → IsZero (H^m (Rpi_* A(1)))`.
4. `KummerBaseChangeConclusions` first gives an equality of derived morphisms:
   pull back the actual coordinate class, commute pullback with shift and use
   the canonical twist identification; this equals the coordinate class on Y'
   after the canonical constant identification. Its remaining two conjuncts
   assert `IsIso` of the actual `ProEtale.derivedBaseChangeMap` evaluated on
   the twisted coefficient object, for the affine and punctured Cartesian
   squares. The exchange is tested before the canonical target coefficient
   identification; composition with that identification is an isomorphism
   exactly when this exchange is. Thus it is precisely the displayed
   `g^* Rf_* A(1) → Rf'_* A(1)` assertion.
5. The first universal block quantifies all separated finite-type k-schemes Y'
   and all `g : Y' ⟶ Y` with `g.IsOver (Spec k)`, exactly the finite-type
   base-change quantifier. The last block separately quantifies every
   algebraically closed field Ω and every `Spec Ω ⟶ Y`. It has no finite-type
   hypothesis. It asserts the same base-change conclusions and clauses (1)-(3)
   over Spec Ω with its induced map to Spec k. On this geometric point the
   constant sheaf/global sections comparison identifies these with constant
   H0, affine-line positive vanishing and punctured-line H1 generated by the
   actual coordinate class and higher vanishing, as in the final paragraph.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`, including their full algebraic closure
  and characteristic/prime hypotheses.
- Published coefficient extension construction, imported by that module:
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers` and
  `coefficientExtensionUniformizer`; Mathlib `emultiplicity` gives the DVR order.
- `Sheaf.Paper.PurityFiniteSetting` supplies the previously unstated
  `def-pur-conventions` fixed finite setting. Its derived operations are the
  published operations; it introduces no parallel six-functor formalism.
- `Sheaf.Paper.PurityAffineLineDatum` supplies the previously unstated
  `def-pur-affine-line-datum` concrete geometry, coefficient sheaves, class and
  canonical etale pullback maps. The pro-etale and derived pullback helpers are in
  `PurityRelativeKummer`; the general scalar and derived coefficient objects live in
  `PurityFiniteSetting`; the scalar extension and roots are reused from
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf` and
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`.
- `def-weil-derived-cohomology-sheaves` is a Mathlib leaf. Its recorded
  `DerivedCategory.homologyFunctor`, in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, is used at
  every degree, not replaced by a private cohomology definition.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: the full signature of
  `Scheme.kummerδ₀` takes `IsUnit (r : Γ(T,⊤))`; the latter is supplied by the
  named theorem `exponent_isUnit` from the actual k-structure map.
- `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`, `derivedBaseChangeMap`, and
  `singleFunctorCompLeftDerivedUpperStarIso`; coefficients are actual ModuleCat A.
  `WeilConjectures.SixFunctors.ProEtale.Derived.Shift` supplies the published
  shift compatibility of both derived functors and their adjunction.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`:
  `comparisonUpperStarCompUpperStarIso`. The functor
  `ProEtale.comparisonUpperStar` is the published exact inverse image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget`:
  `upperStarForget₂Comparison`; `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.upperStarConstantSheafIso`. These fix the canonical maps used by
  the scalar-extension pullback construction.
- The main module imports the compatible recorded proof-dependency modules.
  The thirteen-step natural-language proof is in the theorem's docstring and
  preserves the split's strict-local, rotated smooth-base-change route.

Edge cases checked: the empty base gives zero sheaves and the unique zero-module
isomorphisms, so it is retained. Nonreduced and disconnected bases are retained;
no connectedness, smoothness or regularity of Y is assumed. Level zero is excluded
exactly by the conventions. For ramified E, arbitrary positive levels divisible
by e are retained; no unramifiedness or N=1 assumption is made. The residue
characteristic may divide N; invertibility is of ell^N, not of N. Geometric points
have their own quantifier, so algebraically closed residue-field extensions need
not be finite type over k. Kummer pullback is an equality of the actual classes,
and base-change invertibility refers to the specified mates. All binders and
universes are explicit with `autoImplicit false`; the two small-site universes
are not identified.

Searches: the required `msearch.py` LeanFinder query “Relative etale cohomology of
affine line and punctured line Kummer generator and arbitrary base change” returned
eight unrelated etale-locus/standard-etale hits. Loogle query
`"AlgebraicGeometry.Etale", "affineLine"` returned zero. Mathlib grep for
`kummer|multiplicativeGroup|rightDerivedLowerStar_affineLine` in AlgebraicGeometry
returned zero. LeanSearch for the relative etale Kummer computation returned
“service unavailable: Internal Server Error”. Direct `rg` of the upstream
WeilConjectures tree and side Sheaf tree found the abstract upstream
`EtaleCohomology.Purity.Smooth.AffineLine` theorems. Their full signatures give
abstract nonempty isomorphisms under `HasTateTwist`, without the specified
coordinate Kummer map or arbitrary canonical base change, so they are not exact
matches. The upstream `HasKummerClass` is likewise abstract and is not used.
The live `scompile.py --source` lookup found no completed relative-Kummer module;
the previously reported “live completion” was a stage-1 split, not a Lean statement.

The blueprint unit `dag/units/sk-prop-a1-kummer.json`, the full source markdown
in the obtained blueprint checkout, the item's thirteen proof steps and the
stage-1 report were read. No fault was found in the item's statement, and no
statement correction is made. A pre-existing notational fault in the dependency
identifies G_m(Y) with units on G_m,Y; the stage-1 report already flags it. The
actual unit on G_m,Y is used throughout this delivery.

## Dependency modules

`def-pur-conventions`: no Lean record or Mathlib match was available. The
`PurityFiniteSetting` module bundles the existing finite-field/coefficient data,
finite subextension and positive level, and reuses the existing quotient ring.
It also owns the general finite coefficient sheaves, scalar-forgetting comparison,
and degree-zero derived coefficient objects used by the affine datum.
The module imports the published coefficient and derived sheaf operations used
by this proposition. There is no new version of the six functors.

`def-pur-affine-line-datum`: no Lean record or Mathlib match was available. The
`PurityAffineLineDatum` module gives the actual affine-space geometry, coordinate
basic open and unit, finite root-tensor coefficients, their canonical comparison
pullbacks, and the actual Kummer boundary with its uniquely determined module
lift. Named existence-and-uniqueness theorems used by definitions characterize
the relevant map by all sections, a kernel inclusion, scalar-extension generators
or factorization through a monomorphism; they do not choose arbitrary maps or
objects. Each postponed theorem has its own source/proof docstring and is listed
in this dependency node's `lean.declarations` as part of that concrete datum.

The module's auxiliary invertibility and exactness statements justify the
canonical constructions only; they do not assume relative acyclicity, the Kummer
generator calculation or the main theorem's base-change assertion.

Completion of the interrupted attempt: the node copies were refreshed from the
current shared DAG and differ only in `lean`. The required searches were repeated;
LeanFinder, Loogle and Mathlib grep again found no exact statement, while LeanSearch
again reported its service unavailable. Current server source lookups found none
of the three proposed modules. The available N9/NQ/NS delivery references concern
stage-1 work; they supply no Lean record for these missing interfaces.

The first compile exposed a 60-second timeout in the affine datum after the finite
setting compiled. The repair gives the coefficient sheaves and derived objects
explicit result types and names their inherited `coefficientCommRing` structure
once. This structure is exactly `inferInstance` for the ULift quotient; it adds no
coefficient datum or hypothesis. The generator's result type is also written out.

The derived coefficient pullback and its pro-etale constant/twist comparisons now
belong to the proposition module, where its units and base-change assertions use
them. The affine datum retains the actual geometry, root coefficient extension,
Kummer boundary and canonical etale root-line comparison. This removes derived
six-functor imports from the affine datum without altering any canonical map.

The kernel-checking profile led to replacing expanding abbreviations (`Ring`,
`Coefficient`, `forgetEtale`, `derivedSheaf`, `Line`, `Punctured`) by named definitions
with exactly the same bodies. `ringCommRing` and `coefficientCommRing` expose the
inherited ring structures explicitly. The affine projection uses the published
projection of `AffineSpace` directly, so it needs no additional `Over` instance.

One proof-only import is omitted: `Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate`.
Its current import closure combines `ComparisonPullbackCoherence`, which imports
`ProEtale.FiniteCoefficient.UpperLowerStar.Defs`, with the legacy derived
`ProEtale.UpperLowerStar.Defs`. The prescribed compiler reports that both declare
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. The statement uses the canonical upstream
adjunctions and exchange interfaces, all retained. No canonical map is replaced.
This omission needs revisiting when that published proof dependency's imports are repaired.

Validation: the prescribed `scompile.py Q39 prop-pur-gm-relative-kummer`
compiled all three delivered modules cleanly (finite setting 14.8 s, affine datum
35.5 s, relative Kummer 40.8 s in its server confirmation). Only the permitted
postponed-proof warnings occur. No global build was run.


## Second reading by Q39

I read the current node, its three statement dependencies, all three delivered
modules, and the original blueprint node and unit. The obtained blueprint lives
in the launcher's literature checkout; the shared clone contains the citation
records but not those obtained texts. I also read the cited Stacks source at
Tags 03PL (Kummer exactness), 03Q8 (higher-image presheaf), 03Q9 (strict-local
stalk formula), 0EYU (smooth base change), and the comparison framework notes.
There is no statement correction, new node, or citer audit to perform: the
item's natural-language statement is unchanged.

The source/node checklist and its Lean rendering are as follows. Each verdict
below concerns the actual expanded definitions, not just a similar declaration
name.

1. Fixed fields p,a,q,k0,k, a prime ell different from p, E inside the fixed
   algebraic closure of Q_ell, its valuation ring and uniformizer, and n>=1:
   `P : PurityFiniteSetting` has the existing `FiniteFieldDatum` and
   `CoefficientDatum`, `extension : IntermediateField (Padic ell) Qbar`, its
   `FiniteDimensional` instance, and `level_pos`. `P.Ring` is the existing
   `Padic.coefficientExtensionRing ell E n`. I opened `FiniteFieldFiber` and
   its coefficient construction. Verdict: these are the node's objects;
   no arbitrary ring, field, uniformizer, or extra unramifiedness assumption.
2. The affine datum's standing e|n hypothesis and finite twist exponent:
   `h : P.ramificationIndex ∣ P.level`, `kummerLevel = level / ramificationIndex`,
   and `exponent = ell ^ kummerLevel`. The index is `emultiplicity varpi ell`
   in the actual DVR. Thus N=n/e agrees with n*v_ell(varpi). The source
   explicitly assumes e|n from this datum onward. Verdict: required standing
   hypothesis, not an added restriction. No assumption p does not divide N.
3. Separated finite-type k-scheme Y: `Scheme.{u}`, `Y.Over (Spec k)`,
   `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on its structure map.
   The first two morphism properties mean finite type together. Verdict:
   exact; no nonemptiness, connectedness, reducedness, regularity, smoothness,
   or separate Noetherian instance is required.
4. A1_Y, p, s, Gm_Y, j, pi, and coordinate t: `Line Y` is existing
   `AffineSpace (ULift (Fin 1)) Y`; `coordinate` and `zeroSection` use its
   published coordinate and zero section; `Punctured` is its coordinate basic
   open; `openImmersion`, `lineProjection`, `puncturedProjection` are j, p,
   and j followed by p. The existing zero-section zero-locus description
   identifies this basic open with the stated complement. `coordinateUnit`
   is `Scheme.basicOpenUnit`. Verdict: the actual geometry and actual unit.
5. A(1) and kappa(t): `twistEtale` specializes the published
   `finiteEtaleTateSheaf` to degree one. I opened `FiniteEtaleTateSheaf` and
   `FiniteEtaleTateTwist`: they sheafify A tensor_(Z/r) the existing roots
   kernel. The tensor symmetry identifies this with the node's mu_r tensor A.
   `rootCoefficientMap` is fixed uniquely on all sections by z->1 tensor z.
   `kummerEtale` applies the existing `Scheme.kummerδ₀` to the actual unit,
   extends these coefficients, and inverts the specified bijective
   `moduleClassToAbelian`. `kummer` applies exact comparison inverse image;
   `coordinateKummer` specializes to t. Verdict: the specified boundary
   class, not a chosen rank-one generator or a `HasKummerClass` hypothesis.
6. R^m f_* = H^m Rf_*: every occurrence uses the dependency's existing
   `DerivedCategory.homologyFunctor` and the existing
   `ProEtale.lowerStar(...).rightDerivedFunctor`. `derivedSheaf` is the
   existing degree-zero single functor applied to the coefficient sheaf.
   Verdict: the stated cohomology sheaves, with cohomological shift sign.
7. Clause (1), both derived units and positive twisted vanishing:
   the first two conjuncts of `RelativeKummerConclusions` are `IsIso` of
   `relativeUnit` for `lineProjection`, respectively false and true; the
   third is `∀ m : Nat, 0 < m -> IsZero (H^m Rp_* A(1))`. I expanded
   `relativeUnit`: the published derived adjunction unit is followed by
   Rf_* of the canonical single/pullback coefficient map. Verdict: both
   actual units and all stated positive degrees, not bare object isomorphisms.
8. Clause (2), degree-zero pi-unit: the fourth conjunct is invertibility
   of H0 of the twisted `relativeUnit`. The source is canonically A_Y(1)
   by `singleFunctorCompHomologyFunctorIso`. Composition of the published
   adjunctions identifies it with restriction through j after the p-unit.
   Verdict: the stated map, including its normalization.
9. Clause (2), specified Kummer generator: `kummerGenerator` transposes
   `coordinateKummer.hom` along the actual derived pi-adjunction, takes H0,
   and uses H0(K[1])=H1(K). Its source is exactly `P.constant Y`; the
   single/homology comparison uses its inverse in the required direction.
   This is precisely the A-linear sheaf map whose value at 1 is the Leray
   edge section. The fifth conjunct asserts its `IsIso`. Verdict: the
   specified generator, not merely existence of a free rank-one object.
10. Clause (3), all m>=2: the last conjunct universally quantifies natural
    m with `2 ≤ m`, then `IsZero` of H^m Rpi_* of the twisted coefficient
    object. Verdict: every claimed degree; nothing is omitted or added.
11. Clause (4), finite-type base changes: the middle universal block has
    all separated finite-type k-schemes Y' and all `g : Y' ⟶ Y` with
    `g.IsOver (Spec k)`. `KummerBaseChangeConclusions` first equates the
    actual pulled-back derived class (including shift and coefficient
    comparisons) with `coordinateKummer` on Y'. Its other conjuncts test
    `IsIso` of the published `ProEtale.derivedBaseChangeMap` for the
    affine-space Cartesian square and the actual punctured square.
    `puncturedMap` is uniquely fixed by its composite with the monic open
    immersion, so it is the canonical base-change arrow. The target
    coefficient comparison is invertible because r is invertible; testing
    before that comparison is equivalent to the displayed exchange to
    Rf'_* A(1). Verdict: actual classes and canonical exchange morphisms,
    with the same order of quantifiers and no restriction on g.
12. Geometric points and fibre calculations: the final universal block
    separately has `Ω : Type u`, `Field Ω`, `IsAlgClosed Ω`, and every
    `g : Spec Ω ⟶ Y`, with no finite-type hypothesis. It asserts the same
    exchange/class naturality and `RelativeKummerConclusions` over Spec Ω
    using its induced k-map. Over this algebraically closed point,
    constants/global sections identify these with the final H0/H1/higher
    cohomology statements. Verdict: the independent geometric-point
    clause is present; it is not hidden inside the finite-type block.

Edge cases: an empty Y remains allowed, giving zero coefficient sheaves and
unique maps between zero objects. Nonreduced and disconnected Y are allowed.
There is no index set in this node. n=0 is excluded by the source's n>=1;
ramified extensions are retained whenever e divides n. The hypotheses imply
N>=1 and ell^N is invertible, without a condition on the integer N modulo p.
The coefficient lift `ULift.{u+1} P.Ring` is the usual ring-equivalent size
lift, not a different coefficient ring. The small-site object and morphism
universes stay u+1 and u. Schemes and geometric fields use the same arbitrary
universe u, as the project's geometric-point convention; no equality of the
site's two universes or a lower independent test-object universe is imposed.

Dependency-module reading: no new definition nodes are introduced. For
`def-pur-conventions`, the module supplies its literal fixed finite setting
and uses the published coefficient quotient, derived single functor, and
comparison functor. The ambient six-functor constructions continue to be
those owned by the conventions' existing dependencies, not fields of P.
For `def-pur-affine-line-datum`, the geometry, root line, coordinate class,
and canonical maps above agree with its source. I checked every `choose`:
rootCoefficientMap, rootPullback, twistEtalePullback and puncturedMap are
selected from specified unique-map theorems; the cohomology lift is the
inverse of a specified bijection. Thus none chooses unspecified data from
mere existence. The helper theorems have proof docstrings and appear in
these nodes' `lean.declarations`. All theorem bodies remain `sorry`; no
proof was supplied. The prose typo Gm(Y)=units on Gm_Y is identified in
`lean.note`; its intended coordinate unit is unambiguous in the source.

Independent searches: I repeated LeanFinder with the different query
"Cohomology of relative multiplicative group, coordinate root torsor
generates R1 and arbitrary pullback commutes with derived direct image".
The eight results were group-cohomology, cotangent and scheme-pullback
cocycle declarations, not this theorem. Loogle query `"kummer", "homology"`
returned zero. Direct rg over Mathlib AlgebraicGeometry and the upstream
Purity and shared Sheaf trees for Kummer, multiplicativeGroup and homotopy
invariance found the upstream Smooth/AffineLine and KummerClass interfaces.
I opened their signatures: the former gives Nonempty object isomorphisms
and vanishing under abstract normalized twist data, with no specified
coordinate generator or canonical base-change assertion. The latter takes
the Kummer class as data. Neither is an exact match. I also checked the
existing finite root-line construction and use it rather than duplicating it.
The new search outputs are recorded by the prescribed msearch wrapper.

Mismatch and repair: all mathematical hypotheses, objects and conclusions
above pass. The import audit found that one recorded proof dependency,
`Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate`, had been
omitted to avoid an import-environment collision reported by the first
worker. The stage-2 contract requires stated proof-dependency imports; I
restored it in `PurityRelativeKummer.lean`. No theorem signature or
correct mathematical definition was rewritten. I read the current server
source with `scompile.py --source` too: it still imports
`ComparisonPullbackCoherence`, whose closure includes the finite-coefficient
upper/lower-star framework, as well as the older derived framework.
Compilation and preflight results for this restoration are recorded below.

Validation: all three delivered modules passed the prescribed `scompile.py`
with the restored proof import: PurityFiniteSetting 14.4 s,
PurityAffineLineDatum 33.0 s, PurityRelativeKummer 42.2 s. The wrapper also
compiled the canonical-mate dependency successfully in 2.4 s. The earlier
reported duplicate-declaration collision therefore no longer reproduces;
it is not a reason to omit this import. There were no errors or warnings.
Every delivered Lean line is at most 100 characters, `autoImplicit` is false,
and the node's `lean.statement` equals the final theorem signature verbatim.
