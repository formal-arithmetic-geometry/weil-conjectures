## Worker report

The module `Sheaf.Paper.CoefficientHeartFiltration` states
`AlgebraicGeometry.ProEtale.coefficientHeart_filtration`, with its sole postponed
proof `sorry`. The four helpers transparently specialize existing constructions:
`coefficientHeartOpenTerm` is `v_! v^* F`, `coefficientHeartOpenCounit` is the actual
adjunction counit, `coefficientHeartFiltrationStep` is its image subobject, and
`coefficientHeartLocallyClosedExtension` is open extension into the canonical
scheme-theoretic closure followed by its closed direct image. These are presentations
of objects explicitly introduced by this node, not independent new notions.

Hypothesis and clause correspondence:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The condensed coefficient ring is `L`;
  `hL` is exactly either a finite subextension E of `PadicAlgCl ℓ` over `ℚ_[ℓ]`,
  using `Profinite.padicSubfieldCondensedRing`, or the specified finite-subextension-valued
  `Profinite.padicAlgClCondensedRing`. `coefficientHeartRingObj L` is the existing
  underlying commutative ring object. There is no invertibility-on-X hypothesis.
- Noetherian X is `(X : Scheme.{u}) [IsNoetherian X]`, not just a topological
  Noetherian assumption. All scheme object universes are u; pro-etale sheaves and
  condensed coefficients have the framework's `Ab.{u + 1}` size.
- F in Cons is an actual module object F with
  `hF : IsConstantModelConstructible (coefficientHeartRingObj L) X F`, the recorded
  definition of `sk-def-sfb-constructible`. This is equivalent to giving an object
  of its full subcategory and keeps the ambient module morphisms visible.
- The supplied stratification is `R : X.FiniteLocallyClosedStratification`. Its
  `domain`, `immersion`, `isImmersion`, `stratum`, covering and disjointness fields
  give precisely the locally closed scheme strata and their maps to X.
- Adaptedness is `hadapt`: the restriction to each stratum has the recorded
  `HasFiniteConstantLocalModel`. For these field coefficients these are precisely
  the lisse restrictions. In particular lisseness is a conclusion, not assumed.
- The ordered open-prefix condition is a family `V : Fin (R.n + 1) → X.Opens`
  with `hV` equating its underlying sets to the union of all `R.stratum a` with
  `a.val < k.val`. Thus V is a presentation of the stated open union, not an
  extra restriction on it. `V 0` is empty and `V (Fin.last R.n)` is all X by
  the stratification covering field. No further connectedness condition is needed.
- `coefficientHeartOpenTerm` is defined using the published
  `CondensedRing.openImmersionLowerShriek` and `CondensedRing.upperStar` at `V.ι`.
  The map into F is the counit of their specified adjunction, not an arbitrary mono.
  The first conclusion asserts it is mono for EVERY prefix, so its image subobject
  represents exactly `v_!v^*F` with the stated map to F.
- `F_0 = 0` is equality of its image subobject with bottom; `F_m = F` is equality
  with top. These are equalities of subsheaves, not arbitrary object isomorphisms.
- The existential `h` asserts every adjacent subobject inequality. Transitivity
  gives the entire increasing chain. `≤` is non-strict, as required.
- For `a : Fin R.n`, `a.castSucc` is k-1 and `a.succ` is k in the source's
  indexing. The quotient is `cokernel (Subobject.ofLE ... (h a))`, the cokernel
  of the actual inclusion of subobjects of F. Its isomorphism target is the
  extension by zero of the actual restriction
  `(CondensedRing.upperStar ... (R.immersion a)).obj F`.
- The locally closed extension helper uses the exact formula `i_*u_!`: `u` is
  `a.toImage`, `i` is `a.imageι`, and the closure is `a.image`, cut out by `a.ker`.
  The immersion embeds S topologically into Noetherian X, so the existing
  `Topology.IsInducing.noetherianSpace` supplies topological Noetherianity of S.
  Mathlib's `quasiCompact_of_noetherianSpace_source` then supplies quasi-compactness
  and its existing instance makes `a.toImage` open. These instances are constructed
  inside the definition, not imposed as additional theorem hypotheses.
- The last conjunct is the dependency's `IsLisseCoefficientModule` for each actual
  restriction. Reading `Mod.IsFree` in its source confirms it means isomorphic to a
  FINITE biproduct `finiteFree R n`, with n a natural number. The covering definition
  therefore states pro-etale locally free of finite rank, including rank zero.

Dependency declarations and source signatures were read in full:

- `Sheaf.Paper.CoefficientHeartCommonStratification`: `coefficientHeartRingObj`,
  `IsLisseCoefficientModule`, `CoefficientHeartStratificationAssertions` and
  `coefficientHeart_commonStratification`. Their module supplies the exact admissible
  coefficient convention and finite locally closed stratification interface.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`,
  `IsConstantModelConstructible`, and the full subcategory `ConstantModelConstructible`.
  These are the recorded declaration of `sk-def-sfb-constructible`; the older upstream
  constructibility predicate is not substituted for them.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` (publicly imported by
  the first module): `Scheme.FiniteLocallyClosedStratification` and all its fields.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek` and its actual
  `openImmersionLowerShriekUpperStarAdjunction`. These use restriction through the
  canonical coefficient comparison, followed by the projection-formula module lift.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar` and `CondensedRing.lowerStar`, with their stated coefficient
  actions. The former is the mapMod inverse image followed by canonical scalar change;
  the latter is mapMod direct image followed by scalar restriction.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFree` and
  `Mod.IsFinitelyPresented`, confirming finite ranks and finite matrix presentations.
- Proof imports: `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf` and
  `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`, whose recorded theorem
  statements and supporting interfaces were read. The latter normalizes both
  factorizations and pure-open composition, as required by the DAG proof.
- Mathlib proof leaves: `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`,
  the open-subscheme locally-Noetherian instance,
  `AlgebraicGeometry.IsNoetherian.noetherianSpace`,
  `TopologicalSpace.NoetherianSpace.isCompact`, and `isCompact_iff_compactSpace`.
  Their signatures/docstrings were read from Noetherian.lean, NoetherianSpace.lean,
  and Topology/Compactness/Compact.lean.
- `sk-prop-sfb-cartesian-coefficients` and `det-lem-coefficient-heart-closure` have no
  complete recorded Lean statement, so there is no additional module to import for
  them. The actual cartesian coefficient map and its `IsIso` instance already occur
  in the imported upstream ModuleObject.Basic; those declarations were read too.
  No new prerequisite is necessary to TYPE this statement.

Edge cases checked before writing: empty X permits R.n = 0; `Fin 0` makes the
quotient/lisse assertions empty and the coincident bottom/top endpoints are valid
in the zero module category. F = 0 gives zero terms and rank-zero restrictions,
with all inclusions equal. R.n = 1 gives the single quotient F/0. Empty individual
strata contribute zero quotients. Arbitrary nonreduced stratum scheme structures
are retained through `R.domain`, `R.immersion`, and their scheme-theoretic closure.
No connectedness, positive rank, positive length, reducedness or strictness is added.
The coefficient alternatives cover E = Q_ell as well as Qlb, with no characteristic
restriction on X. Every universe and variable is explicit (`autoImplicit false`).

Searches for an existing statement:

- `msearch.py leanfinder`: “filtration of constructible pro-etale sheaf with quotients
  extension by zero of lisse sheaves”. Eight hits, including BDeRhamPlus,
  localCohomology, condensed-module constructors and smallEtaleTopology; none states
  this filtration.
- `msearch.py loogle`: `"Subobject", "cokernel"`. One hit,
  `ModuleCat.cokernel_π_imageSubobject_ext`, concerning element equality in a cokernel;
  it is not a sheaf filtration theorem.
- `msearch.py grep`: `constructible.*filtration|filtration.*constructible|extensionByZero.*[Ff]iltr`.
  No Mathlib hits.
- `msearch.py leansearch`: “constructible sheaf finite filtration by extensions by zero
  of locally free sheaves on locally closed strata”. Eight hits about finite
  presentation/quasicoherence, free sheaves, TopCat.Sheaf.forget and AB5; no match.
- `rg` on the upstream source and the project's Sheaf source for
  `coefficientHeart.*[Ff]iltration`, `[Ff]iltration.*[Cc]oefficientHeart`, and
  `constructible.*[Ff]iltration`; no exact statement. The nearby
  `Etale.exists_constructible_sheaf_devissage` was opened: it concerns finite discrete
  coefficients on the SMALL ETALE site, finite-type schemes over a field, and existence
  of some filtration, not the specified filtration for an arbitrary given adapted
  pro-etale coefficient stratification. It is not a usable match.
- Upstream blueprint-id search for `det-lem-coefficient-heart-filtration` and the
  upstream name index had no hit. Further searches for open-counit, image-filtration
  and locally-closed-extension helper definitions found only different-site, finite
  discrete-coefficient, or abstract coherence interfaces, not these specializations.

The main-20261015 source statement and proof and the node's revised proof were read.
The resolved stage-1 repair note only requested re-splitting; its current four-step
proof is retained verbatim in the node, with its full plan in the theorem docstring.
The current DAG already permits non-strict inclusions, resolving the older blueprint's
zero-sheaf issue. No statement correction, disputed statement, new DAG node, or dependency
record repair is needed. Only the item's `lean` field changes.

Validation: the prescribed scompile.py compiled the module against the published side
library, including its library-name check, without errors or warnings. All definitions
contain real constructions. The only postponed theorem is the item itself.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
