## Worker report

The module `Sheaf.Paper.InterchangeProperPasting` states
`AlgebraicGeometry.ProEtale.CondensedRing.interchangeProperPasting` with a `sorry`
proof. It constructs only two supporting pieces of data: the specialization of the
existing universal derived direct-image compositor and the outer compactification.
No theorem is proved. The node changes only in `lean`.

Hypothesis and clause correspondence (namespace below is
`AlgebraicGeometry.ProEtale.CondensedRing`):

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field k of positive characteristic distinct from ell | `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`; positive characteristic of a field is prime |
| Fixed algebraic closure and finite intermediate E | The recorded algebraic closure `PadicAlgCl ℓ` and `(E : PadicAlgCl.FiniteIntermediateField ℓ)` |
| Lambda is E or Qbar with the specified condensed conventions | `_hΛ` is the disjunction of internal-ring isomorphisms to the underlying ring of `Profinite.padicSubfieldCondensedRing ℓ E.1` or `Profinite.padicAlgClRingObj ℓ`. The latter uses finite-subextension-valued sections, not all continuous Qbar-valued maps. `Λ` has explicit `MonObj` and `IsCommMonObj` instances. |
| All schemes separated and finite type over k | The six objects `P`, `P'`, `Y`, `B`, `c.obj.obj.Z` (W), `d.obj.obj.Z` (W') have explicit `Over`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure-map instances. |
| All maps are k-morphisms | `IsOver` instances for `p`, `h`, `i`, `c.obj.obj.i`, `c.obj.obj.g`, `d.obj.obj.i`, `d.obj.obj.g` |
| p and h proper; i quasi-compact open | `[IsProper p] [IsProper h] [IsOpenImmersion i] [QuasiCompact i]` |
| P --u--> W --r--> B compactifies ip | `c : Compactification.BoundaryCompactification (p ≫ i)`; `u = c.obj.obj.i`, `r = c.obj.obj.g`, commuting triangle `c.obj.obj.comm` |
| P' --v--> W' --s--> W compactifies uh | `d : Compactification.BoundaryCompactification (h ≫ c.obj.obj.i)`; `v = d.obj.obj.i`, `s = d.obj.obj.g`, triangle `d.obj.obj.comm` |
| u,v quasi-compact dense open; r,s proper | Quasi-compactness is the object property of each boundary compactification; open immersion and properness are the underlying compactification instances. The two `IsSchemeTheoreticallyDominant` binders give exactly scheme-theoretic density. |
| Ordinary unbounded D_T | `DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))` |
| I, J, I' and their displayed sources/targets | The natural-transformation binders `I`, `J`, `I'` have the corresponding composite functors; `I.app (Rh.obj A)` is I at Rh_*A. |
| Normalized restriction identity for all three | `hI`, `hJ`, `hI'` apply the dependency's exact `compositionInterchangeIsNormalized` predicate to every input. The outer predicate uses `interchangeOuterCompactification p h i c d`, whose open is definitionally v and whose proper map is definitionally s followed by r. |
| i_!(kappa_ph inverse) followed by I' followed by kappa_rs | The left side maps `(interchangeDerivedLowerStarComp Λ h p).inv.app A` through i_!, then composes with `I'.app A`, then `(interchangeDerivedLowerStarComp Λ d.obj.obj.g c.obj.obj.g).hom.app (v_!.obj A)`. Lean writes composition in traversal order with `≫`. |
| I at Rh_*A followed by Rr_*(J_A) | Right side `I.app ((lowerStar Λ h).rightDerivedFunctor.obj A) ≫ (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (J.app A)` |
| Every A, naturally | Final `∀ A` ranges over the full ordinary unbounded derived category; the three maps are natural transformations and all other factors are functor maps or components of canonical natural isomorphisms. Thus this is equality at every component of the two natural composites. |
| No finite-Tor, constructibility or localizing restriction | There is no such binder or condition, and no invertibility assumption on I, J, or I'. |

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField`; the standing setting is rendered by the explicit binders,
  and the input compactifications are retained, not replaced by the chosen ones.
- `sk-def-sfb-condensed-ring`: `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`,
  `Profinite.continuousCoefficientRingObj` and its commutativity instance; the present
  finite intermediate coefficient is the already recorded EllAdic specialization.
- `sk-def-sfb-qlbar-condensed`: closed upstream audit declarations in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`.
  Read the current source through `scompile.py --source` because the older checkout
  lacks that file. This definition has exactly finite-subextension-valued sections.
- `sk-def-sfb-derived-categories`: `DerivedCategory`, the generic
  `Functor.rightDerivedFunctor`, and the recorded generalized convention interface
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
  The module categories here have the upstream K-injective resolution instances;
  the generic functor is their existing canonical total derivation.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`, `lowerStarComp` and the
  exactness instance `preservesHomology_upperStar`.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `openImmersionLowerShriek` and its exactness/adjunction instances; the derived
  functor is its existing `mapDerivedCategory`, with no new extension construction.
- `sk-def-nagata-sketch-data`: `Sheaf.Compactification.BoundaryRefinement`,
  `Compactification.BoundaryCompactification`; the outer object uses the upstream
  `Compactification.postcomp` and `Compactification.copy` and equality composition.
- `det-sf-comp-composition-interchange`: `Sheaf.Paper.ProEtaleProperOpenInterchange`,
  `compositionInterchangePullback`, `compositionInterchangeRestriction`,
  `compositionInterchangeIsNormalized`, `properOpenInterchange`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`:
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
  `CategoryTheory.ringedToposDerivedPushforwardComposition`. Its kappa is characterized
  by the derived units and K-injective resolution equation. Our helper is the
  computational specialization of that canonical comparison to the already existing
  internal modules: `Functor.rightDerivedFunctorCompIso'`, transported along the
  dependency's `lowerStarComp`, with inverse orientation. It is not a chosen arbitrary
  isomorphism. `Adjunction.preservesKInjectiveComplexes` uses the recorded exact
  `upperStar` adjunction, so it works in the full pro-etale site universes without
  identifying object and morphism universes. No module category or ringed-topos
  notion is redefined and the general dependency theorem remains unchanged.

The other recorded proof dependencies are imported directly or through the above
public dependency modules: `ProEtaleOpenRestrictionCounit`,
`ProEtaleOpenClosedSequenceRingSheaf`, Mathlib's `mapDerivedCategoryFactors` in
`Algebra.Homology.DerivedCategory.ExactFunctor`,
`Adjunction.preservesKInjectiveComplexes` in the generic right-derived `Comp` module,
`derivedUpperStarLowerStarAdjunction` in the published derived `UpperLowerStar`,
and the cartesian-coefficient maps/exactness in the published module-object framework.
The docstring follows all seven proof steps, including the explicit kappa restriction
identity and the two normalization calculations.

Edge cases checked before writing: zero A is allowed; all identity proper maps and
identity opens are allowed; empty schemes and the empty dense compactification are
allowed; no nonempty-space or nonzero-complex condition is present. A dense empty open
in a nonempty ambient scheme is correctly excluded by the original density condition.
Both coefficient alternatives are retained; E is still introduced when Lambda is Qbar,
as in the node. There is no bounded-below restriction and no identification of the
small site's object universe u+1 with its morphism universe u.

Searches for an existing statement, all on 2026-10-18:

- `msearch.py ... leanfinder`: query “Normalized proper open interchange on unbounded
  derived categories of condensed coefficient module sheaves respects successive proper
  direct images”; 8 hits concern LightCondMod/CondensedMod and their monoidal or
  Grothendieck structures, no match.
- `msearch.py ... loogle '"mate", "comp"'`: 12 hits including `mateEquiv_vcomp`,
  `mateEquiv_hcomp` and conjugate-mate identities; generic mate laws, not this normalized
  pro-etale condensed coefficient statement.
- `msearch.py ... grep 'interchange|extensionByZero|lowerShriek'`: 25 hits, mostly
  unrelated usages, with generic categorical square interchange; no match.
- `msearch.py ... leansearch`: query “Normalized proper open interchange for condensed
  coefficient module sheaves respects vertical composition of proper direct images”;
  8 hits on underived pushforwardComp, pullbackComp, restriction/gluing, and condensed
  module naturality; no match.
- `rg -n 'lem-sfb-interchange-proper-pasting'` in the prescribed upstream WeilConjectures
  source: no hit. Concept searches in its derived `Comp` module found the reusable
  universal compositor, not the proper-open pasting statement.
- `rg -n 'compositionInterchangeIsNormalized|interchangeProperPasting' lean/Sheaf`:
  only the dependency `ProEtaleProperOpenInterchange` gives normalization/existence,
  not the pasting law. Broader proper/open interchange searches found finite-coefficient
  and other tower statements, with different categories or hypotheses.
- Searches for the three new declaration names in `dag/lean_names_upstream.json`,
  `lean/Sheaf`, and the prescribed upstream source: no collisions.

No statement correction, disputed statement, new independent definition node, or
unusable dependency record was found. The two helpers only assemble existing objects
and specialize an existing canonical construction, as authorized by the helper rule.

## Second reading by NL

A separate rereading of the node and the completed file checked the six scheme-setting
binders, seven k-morphism binders, both proper hypotheses, quasi-compact/dense open
conditions, the exact three normalization predicates, and both compositor directions.
In particular kappa_ph is inverted inside i_!, kappa_rs has forward orientation after
I', and the final codomain is Rr_*Rs_*v_!A. The two helpers have concrete data and no
sorry. All source conditions and both coefficient cases are retained. No mismatch was
found. This is the worker's own rereading; the dispatch brief prohibits starting another
agent and assigns the independent mathematical reading to the maintainer's delivery
review. No independent second worker is claimed here.
