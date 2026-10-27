## Worker report

The module `Sheaf.WeilSheaf.NativeProperNaturalBaseChange` states
`AlgebraicGeometry.nativeWeil_proper_natural_baseChange`. Its sole proof is `sorry`.
There are no new definitions, dependency repairs, or statement corrections.
The eight-step natural-language proof in the declaration docstring is the node's proof,
including the coefficient comparison, derived adjunct normalization, affine-chart
reduction for nonseparated bases, and conservativity argument.

Hypotheses and clauses, checked against the node and its cited current blueprint proof:

- Finite field k₀: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime ℓ distinct from the characteristic: `(l : ℕ) [Fact l.Prime]`
  and `[Fact (ringChar k₀ ≠ l)]`. Ω is the framework's `PadicAlgCl l`;
  the geometric fibres use its chosen `AlgebraicClosure k₀`.
- The native coefficient sheaves and abelian Weil categories are precisely
  `ProEtale.AdicSheaf` and `ProEtaleWeilSheaf k₀ l X`, reused from the framework.
  `WeilComplex.objectProperty` is boundedness intersected with the condition that
  every cohomology sheaf has constructible underlying native adic module.
- Four k₀-schemes: `{Z' Z T' T : Scheme.{u}}` and their four `.Over (Spec …)` instances.
- Four k₀-morphisms: the binders `v`, `p'`, `p`, `u`, each with `.IsOver (Spec …)`.
- The cartesian square: `_sq : ChosenCartesianSquare v p' p u` includes its
  commutativity, chosen fibre-product isomorphism, and both projection equations.
- Proper p: `[IsProper p]`. Properness of p' is a consequence, not an extra hypothesis.
- Quasi-compact, quasi-separated T and T': the respective `QuasiCompact` and
  `QuasiSeparated` instances on their structure morphisms to `Spec k₀`.
  Over a field these express the absolute qcqs conditions.
- Locally finite type T and T': the two `LocallyOfFiniteType` structure-map instances.
  No absolute `IsSeparated` instance is required, and u has only its k₀-linearity instance.
  Local finite type of Z and Z' follows from properness and the cartesian square;
  the ambient operations themselves need no extra finite-type instance.
- The source is the full `WeilComplex k₀ l Z` category: it is definitionally
  `(WeilComplex.objectProperty k₀ l Z).FullSubcategory`, included by `.ι`.
- The left composite is `.ι ⋙ (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor`
  followed by `(ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory`.
  It is the actual ordinary Rp_* followed by the exact termwise u^*.
- The right composite is `.ι` followed by the termwise derived v^*, then
  `(ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor`.
- `Nonempty (left ≅ right)` states existence of an isomorphism of functors,
  rather than just objectwise isomorphisms. The two natural transformations,
  inverse laws, and naturality equalities all live in the ambient ordinary
  `DerivedCategory (ProEtaleWeilSheaf k₀ l T')`. No category of fixed pairs of
  geometric derived objects is substituted. No component normalization was added:
  the node's conclusion asserts existence of a natural isomorphism.

Dependency declarations read and used:

- `WeilConjectures.WeilSheaf.LowerShriek` is the framework's recorded entry module.
  Its imports provide `ProEtaleWeilSheaf`, `WeilComplex.objectProperty` and `WeilComplex`
  from `WeilConjectures.WeilSheaf.Category`, and `ProEtaleWeilSheaf.upperStar` there.
  `ProEtaleWeilSheaf.lowerStar` comes from `WeilConjectures.WeilSheaf.LowerStar`.
  Its `.rightDerivedFunctor` is the ordinary total right-derived construction;
  `.mapDerivedCategory` on the exact upperStar is the termwise construction.
  The full signatures and defining bodies of these categories and operations were read.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `AlgebraicGeometry.ChosenCartesianSquare`:
  the recorded chosen cartesian square, used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  separated, universally closed, locally finite type (universal closedness implies qc).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`: quasi-compact diagonal.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and the imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- The native coefficient and constructibility defining signatures were also read in
  `Adic.ConstantSheaf`, `Adic.Module`, and `Adic.Constructible`: locally finite
  continuous functions on the whole site object's underlying space; module objects;
  locally finite constructible strata and pro-etale finite-free local models.
- Every recorded proof-dependency module is imported without `public` unless already
  a statement import. The mathlib matches without module records are imported using
  their recorded source files. The upstream attached constructible-pullback declaration
  is already in the imported `Adic.Constructible` module.

Edge cases checked before writing:

- Identity u: the two actual functors are related by identity pullback comparisons.
- Empty Z or T': neither nonemptiness nor positive rank is assumed; the zero-object
  case and empty coefficient-local-model sums are included.
- Zero complexes: bounded constructible support includes them, and both functors are additive.
- Rank-zero strata: `IsAdicLisseSheaf` allows `n = 0`.
- Nonseparated qcqs bases, such as the affine line with doubled origin: all binders
  permit them; the proof plan uses affine charts rather than assuming affine intersections.
- Arbitrary base map u: no properness, smoothness, separatedness, or flatness is imposed on it.
- Universes: u is explicit, with the framework's native site, coefficients and derived
  localization universes inferred from its recorded constructions, without identifying
  distinct site object and morphism universes.

Searches for an existing declaration:

- `msearch.py … leanfinder "Natural proper base change isomorphism of functors on ordinary
  derived categories of Frobenius equivariant pro etale adic module sheaves"`: eight hits,
  including `SheafOfModules.pushforwardNatIso`, `SheafOfModules.pullbackComp`, and
  `Condensed.profiniteSolid`; none concerns these native equivariant derived functors.
- `msearch.py … loogle "CategoryTheory.NatIso, CategoryTheory.Functor.rightDerivedFunctor"`:
  zero hits, unknown identifier `CategoryTheory.NatIso`; no match established by this search.
- A second Loogle query, `CategoryTheory.NatTrans, CategoryTheory.IsIso`, returned
  zero hits without an unknown-name diagnostic.
- `msearch.py … grep "properBaseChange|proper_base_change|ProperBaseChange" CategoryTheory`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for `properBaseChange|proper_base_change` found ordinary
  etale/condensed-module results and generic compact-support formalisms, not this statement.
  The narrower `WeilSheaf` and native `ProEtale/Adic` searches had no such result.
- `rg` in `lean/Sheaf` for native/proper combinations found related finiteness,
  compactification, and projection statements; none states this natural base-change theorem.
- Exact node-id search in `lean/WeilConjectures` and full new declaration-name searches
  in Mathlib, `WeilConjectures`, and `Sheaf` found no existing declaration.

Validation: the prescribed server `scompile.py` run exited 0. The delivered library
module compiled in 3.3 seconds with no diagnostics. Newly required published-source
overlays were built automatically; their existing line-length warnings are outside
this delivery. Every delivered Lean file (one) was compiled.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NH

This is a same-worker final consistency reading; the dispatcher expressly prohibits
starting another agent, and the maintainer supplies the independent delivery review.
I reopened the node and final signature and checked the four scheme structures,
four over-morphism structures, chosen square orientation, proper p, and all six
base conditions against the node. I traced both functor composites in order and
checked their shared full source and native ambient target. `Nonempty` of the
functor isomorphism includes inverse naturality and all inverse equalities. No
mismatch, strengthening, source restriction, or statement correction was found.

### Independent second reading (maintainer second reader, 2026-10-27, delivery a7813317)

The paragraph above is the same worker's consistency check, not an independent reading
(delivery-errors H11). This section is the independent clause-by-clause reading. It replaces
that paragraph as the second reading of record. The Lean, node and records are unchanged.

Node statement, item by item, with the Lean that renders it:

- Finite field k₀: `(k₀ : Type u) [Field k₀] [Finite k₀]`. OK.
- Prime ℓ ≠ char k₀: `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`. These are the
  framework's own binders (`WeilConjectures/WeilSheaf/Category.lean` l.124, 181). OK.
- Ω = Q̄_ℓ, B_{T̄}, 𝒲_T, D(𝒲_T), WC^der(T) (def-sf-native-weil-derived-framework): these are
  `ProEtaleWeilSheaf k₀ l T` = `IsoAlgebra (WeilSheaf.frobeniusPullback …)` over
  `ProEtale.AdicSheaf l T̄`, its Mathlib `DerivedCategory`, and
  `WeilComplex.objectProperty` = `t.bounded ⊓ homologyProperty (WeilSheaf.objectProperty)`
  (Category.lean l.157). `WeilComplex` is its `FullSubcategory`, so `.ι` is the inclusion of
  the full subcategory. All are recorded declarations of the framework node. OK.
- Four k₀-schemes and k₀-morphisms: `Scheme.{u}` with `.Over (Spec k₀)` and `.IsOver`. OK.
- Cartesian square (def-weil-pbc-cartesian-square): the recorded structure is
  `ChosenCartesianSquare g' f' f g` for X'→X, X'→Y', X→Y, Y'→Y. `ChosenCartesianSquare v p' p u`
  matches the node's square Z'→Z (v), Z'→T' (p'), Z→T (p), T'→T (u). OK.
- p proper (def-weil-proper-morphism): `[IsProper p]` (Mathlib, existing record). Nothing on p'
  or v. OK.
- T, T′ qcqs and locally of finite type over k₀: `QuasiCompact`, `QuasiSeparated` and
  `LocallyOfFiniteType` on `T ↘ Spec k₀` and on `T' ↘ Spec k₀`. Spec k₀ is affine and a point,
  so the qc/qs structure-map conditions are the absolute ones. OK.
- No separatedness of T, T′, and u arbitrary: no `IsSeparated` binder, and u has only
  `IsOver`. Z and Z′ also carry no finite-type binder. The framework's `lowerStar`/`upperStar`
  need none (LowerStar.lean l.71ff, Category.lean l.443ff), so nothing is stronger than the node. OK.
- Rp_*, Rp'_*: `(ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor`. This is the same
  ambient total right derived functor that the framework's `WeilComplex.derivedLowerStar`
  restricts (LowerStar.lean l.172–178). OK.
- u^*, v^* termwise: `(ProEtaleWeilSheaf.upperStar k₀ l _).mapDerivedCategory`. This is the
  same construction that `WeilComplex.upperStar` restricts (Category.lean l.472). OK.
- Conclusion: `Nonempty (ι ⋙ Rp_* ⋙ u^* ≅ ι ⋙ v^* ⋙ Rp'_*)`. It is an isomorphism of functors
  WC^der(Z) → D(𝒲_{T'}), with the target the ambient native derived category and not
  WC^der(T′). The order of composition is right: u^*Rp_* on the left and Rp'_*v^* on the right.
  The node asserts existence only, so `Nonempty` is neither weaker nor stronger. No fixed-pair
  identification is used. OK.

Statement field: `lean.statement` is byte-identical to the declaration in the file. Compared
with the live node, the node copy changes only `lean`. The statement, proof, source and
stmt_deps are unchanged.

Edge cases: u = id; Z or T′ empty; K = 0, since WC^der contains 0 and all functors are additive;
rank-0 strata; and a nonseparated qcqs T such as the affine line with doubled origin. The
binders allow all of these. Universes: one universe u, as the framework requires for k₀ and the
schemes; the site and coefficient universes are inferred from the framework. No variable or
universe is left unbound.

One definition per notion: no new declarations beyond the theorem. I found no existing
declaration of `nativeWeil_proper_natural_baseChange` or any natural-isomorphism form of proper
base change on the native derived Weil categories in the live/side `lean` trees. The landed
objectwise sibling `WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`
(lem-weil-pbc-weil-complex-proper-base-change) cites this item and is weaker
(objectwise, WC^der codomain).

Docstrings: the module and the declaration carry the source place and
`(blueprint: lem-sf-native-weil-proper-natural-base-change)`. The declaration docstring
reproduces the node's eight proof steps with their dependencies. Proof is `sorry` only. No
hollow definition, no global build, no pro-étale substitute. All imported Sheaf/WeilConjectures
modules exist in the published trees.

Mismatches found: none in the Lean or the records. The only change is this report section.
