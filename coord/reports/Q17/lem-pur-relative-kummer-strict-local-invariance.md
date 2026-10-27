## Worker report

The explicit predicate `RelativeKummerPullbackInvariance` packages the four per-curve
conjuncts below without changing their content. `RelativeKummerClassInvariance` packages
the coordinate-class equality. It is an irreducible definition to keep
elaboration inside the file limit.

The main module states `AlgebraicGeometry.Etale.relativeKummer_strictLocal_invariance`.
It retains the ordinary bounded-below derived category of module-valued small-etale
sheaves, the specified adjunction unit, the canonical derived cohomology pullback, and
both normalizations. There is one postponed theorem, with the seven-step DAG
argument grouped into six paragraphs in its docstring. Helper definitions contain concrete constructions only.

Hypothesis/clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [hk : IsAlgClosed k]`.
- Prime ell invertible in k: `(ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))`.
- N >= 1 and r = ell^N: `(N : ℕ) (hN : 1 ≤ N)` and the literal `ℓ ^ N` throughout.
- Finite free commutative Z/r-algebra A: `[CommRing A] [Algebra (ZMod (ℓ ^ N)) A]`,
  `[hfree : Module.Free (ZMod (ℓ ^ N)) A]` and
  `[hfinite : Module.Finite (ZMod (ℓ ^ N)) A]`. No nonzero or positive-rank assumption.
  The annihilator is the image of `ZMod.natCast_self` under the actual algebra map.
- Primitive root: `(ζ : k) (hζ : IsPrimitiveRoot ζ (ℓ ^ N))`.
- Strictly henselian local k-algebra H: `[CommRing H] [Algebra k H]`
  `[hH : IsStrictlyHenselianLocalRing H]`. There is no Noetherian or finite-type binder.
  `include hN hk hfree hfinite hH` explicitly retains hypotheses needed by the proof
  although helper expressions do not otherwise mention them.
- Both curves: `∀ b : Bool`, using `KummerLine.curve k false = Spec k[t]` and
  `KummerLine.curve k true = Spec k[t,t^-1]`, with their actual standard structure maps.
- C_S and h: `relativeKummerBaseCurve` is the actual categorical pullback with Spec H,
  and `relativeKummerProjection` is its first projection.
- L_T: the already published `Scheme.finiteEtaleTateLine T r A hA`, the sheafification
  of the scalar-extended root module. `relativeKummerLinePlus` places it in degree zero
  via the existing `DerivedCategory.Plus.singleFunctor`.
- h* L_C = L_CS: `relativeKummerLinePullback` uses the exact-functor/single comparison
  and the existing normalized `finiteEtaleTwistPullbackData.c` at exponent one.
- Actual unit invertible: first conjunct `IsIso (relativeKummerUnit ...)`. Its definition
  is exactly the derived adjunction unit followed by Rh_* of the coefficient comparison.
- RΓ of that unit identifies with canonical pullback: the second conjunct is equality
  of RΓ(unit) followed by `moduleLerayPlus` with `relativeKummerGlobalPullback`.
  The latter derives the ordinary section map by right-derived descent; it is not defined
  to be the same displayed derived-unit composite.
- The specified derived pullback is an isomorphism: third conjunct `IsIso` of that arrow.
- Every constant zeta tensor a is preserved: fourth conjunct `∀ a : A`, equality under
  `relativeKummerCohomologyPullback ... 0`. `relativeKummerConstant` takes the image of
  one through the published primitive-root trivialization, inserts the scalar a through
  `finiteEtaleTateOneGenerator`, and uses the standard H0/sections equivalence.
- Gm coordinate class: the final conjunct applies degree-one canonical cohomology
  pullback to `relativeKummerClass` of `KummerLine.coordinateUnit k`, and identifies it
  with `relativeKummerClass` of that unit pulled back by `h.appTop`. This class is exactly
  `Sheaf.H.map (ordinaryFiniteRootMap ...) 1` of the ordinary `kummerδ₀`. The root map is
  z -> 1 tensor z (the symmetric scalar-extension presentation of z tensor 1).

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing` extends
  henselian local rings with separably closed residue field.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.rootsOfUnitySheaf`,
  `Scheme.kummerSequence`, `Scheme.kummerδ₀`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public tensor
  imports: the existing sheaf tensor construction (no new tensor definition).
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: existing small-etale categories;
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the module-valued D and D+.
- Mathlib `CategoryTheory.Limits.pullback`, `pullback.fst`; Mathlib AffineSpace is imported
  as the recorded affine-space dependency; the already landed polynomial-spectrum model
  `KummerLine.curve` supplies the precise chosen coordinate presentation.
- `Sheaf.AlgebraicGeometry.KummerLineGeometry`: `curve`, `structureMap`, `coordinateUnit`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `finiteEtaleTateOneGenerator`; its public
  `FiniteEtaleTateTwist` supplies `finiteEtaleTateLine`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: normalized
  `Scheme.finiteEtaleTwistPullbackData.c` and its pure-tensor law.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `ordinaryFiniteRootMap`.
- `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`: `forget`, `pullbackIso`.
- `WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`:
  `Scheme.constantZModIsoRootsOfUnitySheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`: `cohomologyMap`.
  Its missing module-derived clause is supplied by the dependency module below.
- `Functor.mapDerivedCategoryPlusSingleFunctor`,
  `upperStarLowerStarAdjunction.derivedPlus`, `Sheaf.H.equiv₀`, and
  `Functor.rightDerivedFunctorPlusCompIso'` provide the canonical comparison constructions.

Every recorded proof dependency with a module is imported privately, except dependencies
also needed publicly for statement types. The withdrawn `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
is replaced by its official `WeilConjectures` twin as directed by the forwarding file.

Edge cases checked: A = 0 is allowed (free rank zero), N = 1, H = k, a strictly henselian
nonreduced H, non-Noetherian H, and H an arbitrarily large algebraically closed extension.
Both Bool cases and the full coordinate-pullback map are present. No finite-type assumption
is introduced and all sheaf coefficients retain the site-size u+1 convention. Transport of
invertibility along structure maps also works on empty schemes; strict local H itself is
nontrivial by the existing henselian-local class. No STATEMENT-DISPUTED issue found.

Searches: msearch LeanFinder query "Base extension of affine line or multiplicative group
over an algebraically closed field to a strictly henselian local algebra preserves the
canonical derived etale pullback with finite free Kummer coefficients" returned algebraic
etale base-change facts, no cohomological match. Loogle query
"AlgebraicGeometry.Etale.cohomologyMap, IsIso" returned no hit (project identifier unknown
in the Mathlib index). Grep query "kummer|strict.*hensel.*cohom" returned Kummer-Dedekind
arithmetic facts, no sheaf theorem. LeanSearch query "etale derived cohomology pullback along
a strictly henselian local base extension of the affine line" returned etale base-change
and differential lemmas, no same-object statement. Local rg searches of WeilConjectures and
Sheaf for relative Kummer, strict henselian cohomology, scalar Kummer coefficients, and
canonical derived pullback located the reused modules above. The exact node-id search in
WeilConjectures had no match. `blueprint_refs.py search 'Kummer line'` found no blueprint
node; DAG grep located the landed definition nodes subsequently added to stmt_deps.
The upstream AffineLine module proves affine-line cohomology, not this arbitrary-H,
actual-unit and derived-pullback-normalization statement.

## Dependency modules

`def-weil-pbc-cohomology-pullback`: the old record names `Etale.cohomologyMap`, which
accepts an abelian sheaf and a nonnegative degree. Its note explicitly reports the missing
D+ derived arrow. `ModuleDerivedCohomologyPullback` retains that existing map by public
import, and supplies `abelianDerivedCohomologyPullback` and `moduleDerivedCohomologyPullback`,
the right-derived descent of the
ordinary section-pullback transformation for all abelian and module-valued D+ objects. It also supplies
`moduleLerayPlus`, the canonical composition isomorphism with its usual derived-unit
normalization built into `rightDerivedFunctorPlusCompIso'`. These are concrete definitions
using existing localization APIs. No new theorem is postponed in the dependency module.
Only this dependency's lean record changes; its statement and every other field remain.

## Second reading by Q17

The dispatcher forbids starting other agents; the maintainer performs the independent
reading. I reread the DAG statement, the source Step 2 and every helper body against the
final signature. This exposed the need to explicitly include hN, algebraic closedness,
finite freeness and strict henselianity (Lean would otherwise omit unused section variables).
Those hypotheses are now retained. I also checked the final coordinate is the Units.map
of t through precisely the first fibre-product projection; the equality is in H1 of the
same finite root line, not an abstract identification. The derived pullback is defined
by right-derived descent, independently of the unit-composite equality asserted here.


## Resumed compilation repairs

Kernel profiling located expensive specialization of `Sheaf.H.map` to the concrete
scalar-extension sheaf. `relativeKummerMapOnCohomology` is the same existing map behind
an abstract site interface; it supplies real data and assumes precisely the sheafification
and Ext instances already provided by the small etale site. The specialized pullback is
written pointwise. No conclusion or mathematical hypothesis changes. The compilation
also corrected docstring placement around local options and `include`, and uses the
current `Nat.cast_pow` parameter name. All declaration names and the verbatim main
signature are synchronized in the node's Lean record.
