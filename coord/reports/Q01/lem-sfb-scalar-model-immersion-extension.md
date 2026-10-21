## Worker report

Item: lem-sfb-scalar-model-immersion-extension. The module
`Sheaf.Paper.ScalarModelImmersionExtension` states
`AlgebraicGeometry.ProEtale.scalarModelImmersionExtension` with proof `sorry`.
Its helper `ScalarModelImmersionExtensionAssertions` is the explicit conjunction of
this node's conclusions for one coefficient ring, not a replacement construction of
constructibility, pullback, extension, or scalar models. Both declarations are listed
in the node's `lean.declarations`. No new DAG nodes or dependency repairs are needed.
The node changes only in `lean`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| T is a Noetherian scheme | `{U Z T : Scheme.{u}} [IsNoetherian T]` |
| j is an open immersion | `(j : U ⟶ T) [IsOpenImmersion j]` |
| i is the complementary closed immersion | `(i : Z ⟶ T) [IsClosedImmersion i]` and `Set.range j = (Set.range i)ᶜ` |
| admissible condensed coefficient ring | theorem conjunction over precisely the rings in `CartesianUntwistedAssertions`: finite discrete commutative A, Z_ell, Q_ell, O_E and E for every finite intermediate field, and finite-subextension-valued Qbar |
| prime ell for the adic coefficients | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| R_V = Lambda_V and Cartesian identifications | every module category uses `condensedRingObj Λ V`; the canonical `CondensedRing.upperStar`, `lowerStar`, and `openImmersionLowerShriek` use the published coefficient maps, not arbitrary maps |
| finite constant scalar-model constructibility | `IsConstantModelConstructible`, with adapted strata expressed using `HasFiniteConstantLocalModel` |
| exact j_! and i_* | first four conjuncts of the helper: `PreservesFiniteLimits` and `PreservesFiniteColimits` for each of the two module functors |
| j_! takes constructible sheaves to constructible sheaves | first universal F implication in the helper |
| i_* takes constructible sheaves to constructible sheaves | universal G implication in the helper |
| any adapted finite stratification on the source | universal `(S : Scheme.Stratification U)` or `... Z`, followed by the hypothesis giving `HasFiniteConstantLocalModel` on every stratum |
| original strata viewed in T and supplemented by the complement | existential target `R`, equivalence `Fin R.n ≃ Option (Fin S.n)`, and `Over.mk` isomorphisms to the composite old immersion for `some a`, and to i (open extension) or j (closed extension) for `none` |
| extended stratification is adapted | explicit `HasFiniteConstantLocalModel` for the restriction of the extension to every stratum of R |
| old local models retained | for every original a, module isomorphism between the extension pulled back along the composite immersion and the original restriction to a |
| additional locus has zero model | `IsZero` of restriction along i for j_!F, and along j for i_*G |

The original-stratum isomorphisms retain *every* preselected scalar-model witness:
for any original cover member v, apply `(CondensedRing.upperStar Λ v).mapIso`
to the displayed isomorphism, use the canonical pullback-composition isomorphism,
and compose with the original model isomorphism. The cover v and point module P
are unchanged. This includes the matrices over Lambda(*) encoded by
`Mod.IsFinitelyPresented Λ P` in the dependency's definition. `IsZero` gives the
zero local model on the identity cover with zero point module and its rank-zero
presentation. Thus these clauses specify the old models and zero new model, rather
than merely asserting existence of unrelated stratifications.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (the recorded open-immersion definition).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (the recorded closed-immersion definition).
- `Sheaf.Paper.CartesianCoefficients`,
  `AlgebraicGeometry.ProEtale.cartesianCoefficients`,
  `CartesianUntwistedAssertions` and `cartesianFinitePointRing`. The theorem's list
  is exactly the untwisted list in that dependency. In particular Qbar is
  `Profinite.padicAlgClRingObj ℓ`, not all continuous maps to the algebraic closure.
- `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`,
  `IsFiniteConstantStratified`, and `HasFiniteConstantLocalModel`.
  Their actual `Scheme.Stratification` interface already requires constructible
  locally closed strata. This is precisely the constructible stratification
  required here; the weaker locally-closed-only interface is not substituted.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.upperStar`, `lowerStar` and `upperStarComp`; this module is public
  through the constructibility dependency.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `CondensedRing.openImmersionLowerShriek` and its specified adjunction.

Proof dependencies with recorded project modules are imported privately:
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, and
`Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`. The constructibility,
Cartesian coefficient and module-pullback proof dependencies are already public
imports. The Mathlib proof leaves are available through Noetherian, Proper,
NoetherianSpace and Constructible. The complete six-step proof plan is in the
main theorem's docstring, including the original covers and rank-zero model.

Edge cases checked before writing:

- Empty T, U, or Z is allowed. Neither nonemptiness nor a base field is imposed.
- A stratification with zero strata can occur only on an empty source; Option
  adds the one complementary stratum. Empty strata are permitted by the existing
  `Scheme.Stratification` definition, including when the complement is empty.
- For an isomorphic open immersion the closed complement is empty, and conversely
  the closed immersion can have empty open complement. The same formulas apply.
- Zero coefficient rings and zero modules are included. No nontriviality, rank
  positivity or nonzero presentation assumption occurs.
- Closed schemes can be nonreduced: the existential over-category isomorphism is
  to the specified i, not to an arbitrarily chosen reduced closed complement.
- Covers can be infinite; only the number of strata and the scalar presentations
  are finite. There is no added bound on cover cardinality.
- No invertibility of ell on T, U, Z, and no ell-primary restriction on the finite
  ring A, is imposed: this is the untwisted coefficient assertion.
- Universes match the published small pro-etale framework: schemes in u, site
  objects in u+1 and abelian values in u+1. No universe equality or small test
  algebra restriction is added.

Searches (2026-10-21):

- `msearch.py ... leanfinder`, query “Open extension by zero and closed direct
  image preserve finite constant scalar model constructibility on Noetherian
  schemes”: eight hits, mainly constructible images/preimages and Chevalley;
  none states this assertion.
- `msearch.py ... leansearch`, query “Open and closed immersion extension preserve
  constructibility with finite constant scalar models”: eight hits concerning
  closed/open immersions and their base change; no scalar-model extension result.
- `msearch.py ... loogle`, query `IsConstantModelConstructible, openImmersionLowerShriek`:
  zero hits; Loogle does not index this project-specific identifier.
- `msearch.py ... grep`, query `constructible.*(extension|lowerShriek)|[Ss]tratification`
  in Mathlib/AlgebraicGeometry: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `IsConstantModelConstructible|IsFiniteConstantStratified|[Ii]mmersion[Ee]xtension`:
  read `CondensedConstantConstructibility`,
  `CoefficientHeartLisseExtensionConstructible` and
  `OpenExtensionConstantModelConstructible`. Existing open-extension preservation
  results do not state the present joint assertion with retained strata for all
  Noetherian T and exactly the full admissible coefficient list. The recorded
  open-extension result has finite-type-over-a-field hypotheses and only the open
  half. The heart-closure helpers do not include the retained-stratification data.
- Exact item-ID search of `lean/WeilConjectures` returned no declaration.
- Full-name search in Mathlib, `WeilConjectures` and `Sheaf` for
  `scalarModelImmersionExtension|ScalarModelImmersionExtension` returned no hits.

No statement fault or dispute was found. The source paragraph and the expanded
six-step node agree on the constructibility assertion being formalized here.

Validation: prescribed `scompile.py` compiled the sandbox probe and the actual
module independently in 3.4 s and 3.5 s with no errors or warnings. The only
postponed proof is the named theorem `scalarModelImmersionExtension`. The helper
is a fully written proposition with no sorry or choice of data.

## Second reading by Q01

Worker consistency reread, not an independent agent review: the dispatcher brief
forbids starting other agents and assigns the independent review to the maintainer.
I reopened the node, its source paragraph, and the full module. The table above
matches all hypotheses and conclusions. In particular the two Option-indexed
stratifications really use the specified complementary scheme, all old strata
have module isomorphisms retaining their original models, exactness is present
for both functors, and the coefficient list uses the correct Qbar construction.
No statement or dependency-node correction was needed. Proof-docstring notation
for closed inverse/direct image was clarified to avoid reading both as i-star.
