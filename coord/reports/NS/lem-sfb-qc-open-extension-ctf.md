## Worker report

The module `Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor` states
`AlgebraicGeometry.ProEtale.CondensedRing.qcOpenExtension_constantModelConstructible_finiteTor`
with one `sorry`. It introduces no definitions and changes only the item's `lean` record.
The source is the current main-20261015 refinement proof, paragraph (2), read in full,
and the extracted six-step proof in the item. Its complete natural-language argument is
in the theorem docstring. No statement correction or disputed statement is needed.

Hypotheses and clauses, checked against the node:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The condensed commutative ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` is the recorded
  coefficient convention of `sk-def-localizing-closure`, including finite discrete rings
  killed by an ell power, continuous ell-adic integers and rationals, finite subextensions
  in the fixed `PadicAlgCl`, their valuation rings, and the algebraic-closure conventions
  retained by that recorded predicate. The finite extension and its valuation ring are
  parameters of the corresponding alternatives of that predicate; neither needs an
  unrelated binder in the consumer.
- The schemes are `{U X : Scheme.{u}}`, and the geometric hypotheses are exactly
  `(j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]`. There is no global qcqs,
  Noetherian, finite-type-over-a-field, separation, or characteristic assumption.
- The actual pulled-back coefficient rings are `condensedRingObj Λ U` and
  `condensedRingObj Λ X`, the unbundled forms of `coefficientRing`. Their modules
  are the existing `Mod (Sheaf (Scheme.ProEt.topology _) Ab.{u + 1}) ...` objects,
  and the ambient categories are ordinary `DerivedCategory` of those modules.
  The scheme universe `u`, profinite point universe `u`, and abelian coefficient
  universe `u + 1` follow the existing small-site framework and size convention.
  No independent site universe or equality of object and morphism universes is added.
- The underived functor `j_!` is `openImmersionLowerShriek Λ j`. The derived functor
  `J = D(j_!)` is precisely `(openImmersionLowerShriek Λ j).mapDerivedCategory`,
  the existing exact termwise derived functor, not a chosen arbitrary functor or
  a separately derived pushforward of abelian sheaves.
- The first conjunct quantifies over every module `M` and sends
  `IsConstantModelConstructible Λ U M` to
  `IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M)`.
  This is the dependency's finite constant scalar-model predicate, including its
  finite constructible locally closed stratification on qcqs schemes and its
  affine-local interpretation on other schemes. It is not upstream's weaker
  arbitrary finite-presentation constructibility predicate.
- The second conjunct is `∀ n : ℤ, Nonempty (J ⋙ homologyFunctor _ n ≅
  homologyFunctor _ n ⋙ openImmersionLowerShriek Λ j)`. The isomorphism is between
  functors on the whole derived category, hence includes naturality in `K` and
  yields exactly `H^n(JK) ≅ j_!H^n(K)` upon evaluation. This is an existence
  statement about a natural isomorphism, not a family lacking naturality.
- The third conjunct quantifies over every derived object `K` and every integer
  pair `a b`; `DerivedCategory.homologyConcentratedIn a b K` implies the same
  predicate for `JK`. No ordering condition `a ≤ b` is added.
- The fourth conjunct uses exactly `DerivedCategory.torAmplitudeIn _ a b` on
  the same two objects. This predicate tests the actual derived tensor product
  against every degree-zero module sheaf, with no constructibility, flatness,
  completeness, or boundedness assumption on the test sheaf or on `K`.
- The final conjunct quantifies over every `K` in the ordinary derived category.
  The premise is `(constantModelBoundedConstructible Λ U ⊓
  DerivedCategory.finiteTorAmplitude _) K` and the conclusion is precisely the
  corresponding intersection on `X` for `JK`. This is the object predicate
  defining `ConstantModelConstructibleFiniteTor`, so it states Dctf preservation
  without adding a second definition or an unnecessary functor construction.

Dependency declarations used (their source signatures and docstrings were read):

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, and
  `condensedRingObj` (also publicly provided by the constructibility framework).
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback` give the node's ambient ordinary module-derived
  pushpull framework; this item uses the exact open extension's `mapDerivedCategory`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact import:
  `AlgebraicGeometry.QuasiCompact`. The dependency also defines locally finite type;
  that property is deliberately not imposed, since the item requires only quasi-compactness.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`, its additive,
  finite-limit, finite-colimit, homology-preserving, and adjunction interfaces.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and
  `ConstantModelConstructibleFiniteTor` in `AlgebraicGeometry.ProEtale`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, used by the
  stratification definition and the Boolean-algebra argument. The size convention
  node is metatheoretic and has no module/declaration; explicit universes render it.
- The shared predicates `DerivedCategory.homologyConcentratedIn`, `torAmplitudeIn`,
  and `finiteTorAmplitude` come from the recorded constructibility dependencies,
  respectively `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
  and `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.

The stated proof-dependency modules are imported without `public`, including the
finite scalar local-model interface, localization, projection formula, disjoint
vanishing, cartesian coefficients, and reduced closed subscheme construction.
Mathlib imports supply the affine qcqs, spectral, retrocompact and constructible-image
facts. `lem-sfb-constructible-zariski-locality` has no Lean record on the read base;
it is a proof dependency only, not an absent notion needed to type this statement.
Its two clauses are explicitly retained in the proof docstring for stage 3; there
is no nonexistent import and no replacement definition.

Edge cases checked before writing: empty `U`, empty `X`, the identity open immersion,
zero modules and complexes, the zero finite coefficient ring, empty strata and an
empty complement, `n = 0` and arbitrary negative cohomology degrees, and `a > b`.
There is no nonemptiness restriction on any of them. Zero scalar models have empty
finite presentations; exact extension preserves zero, including empty-domain extension.
The Tor test ranges over all degree-zero modules. The proof uses affine qcqs neighborhoods,
so non-qcqs schemes are included; ell equal to a residue characteristic is not excluded.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query: "Quasi compact open extension by zero preserves
  finite constant model constructibility cohomological intervals and Tor amplitude for
  condensed coefficient modules". Eight hits, including `CondensedMod.IsSolid`,
  `Condensed.finFree`, and `CondensedMod.LocallyConstant.functor`; no matching statement.
- `msearch.py ... leansearch`, query: "Extension by zero for quasi compact open immersions
  preserves constructible sheaves and finite Tor amplitude". Eight hits, including
  `HasCompactSupport.extend_zero`, `RingedSpace.res_zero`, and quasi-compact scheme
  restriction facts; none states the module-object conclusion.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsOpenImmersion, CategoryTheory.Functor`. Twelve hits, including
  `Scheme.Hom.opensFunctor` and gluing functors; no matching statement.
- `msearch.py ... grep`, query `extensionByZero|extension_by_zero|torAmplitudeIn`,
  Mathlib subdirectory `CategoryTheory`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for constant-model and
  lower-shriek combinations found `OpenExtensionConstantModelConstructible`,
  `IntegralExtensionByZero`, `RationalExceptionalRestriction`, and
  `OpenImmersionLocalizing`. Read the relevant declarations: the existing
  `constantModelConstructible_openImmersionLowerShriek` requires schemes of finite
  type over a field with characteristic distinct from ell, and a supplied global
  stratification. It does not cover arbitrary schemes in this node. Upstream's
  `isConstructibleModuleObject_openImmersionLowerShriek_obj` uses its distinct
  constructibility predicate. Neither is an exact match.
- `rg -n 'lem-sfb-qc-open-extension-ctf' lean/WeilConjectures` found no node-tag match;
  the proposed declaration name has no match in `dag/lean_names_upstream.json` or
  either source root. The exact-functor library already supplies
  `mapDerivedCategoryHomologyFunctorIso` and interval preservation generically;
  those are not redefined here. The theorem assembles the node's complete assertion.

Validation: `scompile.py NS lem-sfb-qc-open-extension-ctf <module>` passed both the
sandbox and library-module compilation (4.6 s and 3.0 s), with no errors or warnings.
Every universe and variable is explicitly bound; `set_option autoImplicit false` is set.

## Second reading by NS

The dispatched brief forbids starting another agent and assigns the independent delivery
review to the maintainer. This is a second self-reading of the node and the completed file,
not a claim of independent review. I compared each clause again: the coefficient convention
is the dependency predicate; the open immersion is genuinely quasi-compact; the categories
and extension functor are the actual coefficient-module objects; constructibility uses
finite scalar models; the cohomology assertion is a natural functor isomorphism; both
intervals retain the identical endpoints; and Dctf uses the existing bounded constructible
and finite-Tor predicates. No field/Noetherian/global-qcqs or characteristic hypothesis
has slipped in. The only proof is the expected named `sorry`, with the entire six-step
argument documented. No mismatch was found and no statement changes were made.
