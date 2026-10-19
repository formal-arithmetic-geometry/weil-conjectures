## Worker report

This delivery states all three clauses of `det-thm-sfb-proper-base-change-rational` in
`Sheaf.Paper.ProperBaseChangeRational`. There are six theorems, each with `sorry`, and three
helpers specializing the existing comparison or packaging existing preservation proofs. No node statement is changed. Two already landed
nodes are added to `stmt_deps`: `def-sfb-module-object-projection-map` and
`def-sfb-derived-push-hom`. No new notion or private coefficient construction is introduced.

Hypothesis and conclusion matching:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The standing base is `{k : Type u} [Field k]`
  with `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`, so the characteristic is positive
  and differs from ell; k is not assumed closed, perfect, or finite.
- Standing schemes are objects `X Y : Over (Spec (.of k))` with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`, and the same for Y.
  This is exactly separated finite type over k. A morphism `p : X ⟶ Y` is automatically a
  k-morphism; properness is `[IsProper p.left]`. The square adds the same standing
  hypotheses for X' and Y', and uses morphisms in that same Over category.
- Finite coefficient fields are `PadicAlgCl.FiniteIntermediateField ℓ`, hence finite
  subextensions of the fixed algebraic closure with their induced norm. The node's E is
  understood with its fixed embedding in that closure, as in the coefficient dependencies.
  A finite extension F/E is `E ≤ F` between such finite subextensions. This includes F=E;
  every finite extension of E embeds in the fixed algebraic closure over E, so the
  presentation does not impose a Galois or normality hypothesis.
- The integral and rational coefficient rings are respectively
  `Profinite.padicIntegersRingObj ℓ E.1` and `Profinite.continuousMapRingObj E`, with their
  published pulled-back ring objects `condensedRingObj ... X.left`. Qlbar is exactly
  `Profinite.padicAlgClRingObj ℓ`, whose sections take values in one finite subextension.
  No discrete constant field or all-continuous-functions Qlbar is substituted.
- All complexes live in `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left)
  Ab.{u + 1}) (condensedRingObj ... X.left))`: the ordinary unbounded internal-module
  derived category on the small pro-etale site. `DerivedCategory.TStructure.t.plus K`
  is precisely existence of a lower cohomological bound. It imposes no upper bound,
  constructibility, or completeness in clause 1.
- Clause 1, localization: `isIso_rationalizationPushHom_boundedBelow` states invertibility
  of `(rationalizationPushHom ℓ E p.left).app K`. The helper is the existing
  `derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) p.left`, with its required
  flatness proof obtained by projecting the last clause of `padicIntegers_invertEll`.
  Its explicitly declared endpoints are `(Rp_* K)[1/ell] -> Rp_*(K[1/ell])`, using total
  left-derived extension along the recorded coefficient inclusion. Invertibility states
  precisely the source's isomorphism, irrespective of which direction its text writes.
- Clause 1, finite extension: `isIso_finiteCoefficientPushHom_boundedBelow` uses the actual
  `(derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) p.left).app K`.
- Clause 1, Qlbar extension: `isIso_algClCoefficientPushHom_boundedBelow` uses the actual
  `(derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K`.
  Both retain precisely the bounded-below hypothesis of the node. Current upstream proves
  the finite comparison on unbounded objects and the Qlbar comparison on proper,
  bounded-below objects; neither is the whole three-clause node.
- In clauses 2--3, `(Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}))`
  bundles the coefficient sheaf and its actual multiplication and unit. The displayed
  hypothesis `(∃ E, Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
  Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)` expresses exactly "Λ=E or Qlbar".
  Equality of bundled rings fixes the ring operations; equality of underlying sheaves alone
  would not suffice. `[IsCommMonObj Λ.X]` supplies the commutative-ring operation interface.
  There is no arbitrary coefficient class, no IsFinitenessCoefficient assumption, and no
  arbitrary comparison map in these theorem hypotheses.
- Clause 2 is `properPushforward_boundedConstructible_rational`. The only complex hypothesis is the recorded
  `boundedConstructible (condensedRingObj Λ.X X.left) K`; the conclusion is membership of
  `(lowerStar Λ.X p.left).rightDerivedFunctor.obj K` in the same predicate on Y.
  This uses the general ring-object constructibility predicate required by the current
  dependency node, not the stricter constant-matrix-model predicate.
- Clause 3, projection, is `isIso_properProjectionMap_boundedConstructible_rational`.
  It quantifies independently over K on X and M on Y, requires exactly their bounded
  constructibility, and asserts
  `IsIso (moduleObjectProjectionMap Λ.X p.left K M)`. Its definition is the transpose of the
  published K-flat pullback tensor comparison followed by counit tensor identity. Thus
  the actual specified map `(Rp_* K) tensor^L M -> Rp_*(K tensor^L Lp^* M)` is inverted.
- Clause 3, base change, is `isIso_properBaseChange_boundedConstructible_rational`.
  `sq : IsPullback g' p' p g` expresses a cartesian square
  of k-schemes. The forgetful functor from Over creates limits, so these are exactly the
  underlying cartesian scheme squares equipped with the standing k-structures. No
  properness, smoothness, or other condition is imposed on g or g'. The conclusion is
  `IsIso ((boundedConstructibleBaseChangeOfPreserves Λ.X ℓ ... sq.toCommSq).app K)`,
  for every `K : ProEtale.BoundedConstructible (condensedRingObj Λ.X X.left)`. This is exactly
  the recorded unit--square-comparison--counit map on every Dbc object. Componentwise
  invertibility is equivalent to invertibility of the natural transformation. The named
  preservation proof is `rationalCoefficientPushforwardPreservation ℓ Λ hΛ`: case elimination
  on the ring equality reduces it to `rationalFinitenessPushforwardPreservation`, itself just
  the existing finiteness-coefficient preservation theorem. These abbreviations contain
  actual proof terms, no sorry, no new assumption and no chosen map. Clause 3 therefore does
  not depend on choosing a proof of the separate clause 2 theorem in this statement stage.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField`, the standing Over interface, restricted operations,
  `boundedConstructible_rightDerivedLowerStar_obj`, and the restricted adjunction.
  Current source was read via `scompile.py --source`: the local copy has older signatures.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its publicly imported coefficient constructions.
  This is the coefficient-extension dependency; the finite-subextension presentation
  supplies the same finite-dimensional fields and valuation-ring construction used here.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and the public
  continuous-function constructions. `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicIntegersRingObj`, `padicAlgClCondensedRing`, and `padicAlgClRingObj`.
  The Qlbar node is closed upstream and has no lean record, as the brief permits.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, its commutativity instance and the coefficient pullback comparison.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and the recorded derived-category
  convention. The actual geometric functors use the dependency's upstream total derived
  interfaces, as its lean.note prescribes.
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`: reexported `boundedConstructible`,
  `BoundedConstructible`, `mem_boundedConstructible_iff`; the weak-Serre closure theorem is
  retained as a proof import. No noetherian-only closure assumption is added to the statement.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`, `lowerStar`, `upperStar`, and their total derivations.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`: `coefficientMap`,
  `derivedPushHom`, and `derivedComapLowerStarIso`. The actual derivedPushHom requires flatness
  on all schemes; this is supplied, never assumed of the theorem's input.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `derivedTensor`,
  `derivedHom`, and their relative monoidal/closed structures. ProjectionMap publicly imports
  the current `Derived.Monoidal.leftDerivedUpperStarTensor`, whose signed total-complex and
  two-derived-counit characterization was read through `scompile.py --source`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.BoundedConstructibleBaseChange`: `boundedConstructibleBaseChangeOfPreserves`
  and its three component maps. This is the current dependency record, rather than a copy
  of the older coefficient-restricted interface.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` (lines 84--100), whose unit/transport/
  counit formula agrees with `det-def-sfb-base-change-morphism-bc`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`, providing the
  canonical tensor/shift/mate proof input. Its ringed-site categories are not substituted
  for the module-object categories in the theorem statements.
- Added landed node `def-sfb-module-object-projection-map`, module
  `Sheaf.Paper.ModuleObjectProjectionMap`, declaration `moduleObjectProjectionMap`.
  Added landed node `def-sfb-derived-push-hom`, module `ChangeOfCoefficients`, declaration
  `derivedPushHom`. These name the actual canonical maps referred to by the node.
- `Sheaf.Paper.PadicIntegersInvertEll`: `padicIntegers_invertEll` supplies the rationalization
  flatness proof. `ModuleObjects.EllAdicRationalization` supplies the canonical integral
  inclusion; `ModuleObject.Colimit.Compatibility` supplies finite/Qlbar flatness instances
  and reexports the two coefficient inclusions from `Condensed.FiniteSubextension`.

All already stated proof-prerequisite modules are imported; unstated
`det-prop-scalar-six-pullback`, `det-lem-integral-models-generators`, and
`det-thm-sfb-proper-base-change-integral` have no module to import. The docstrings follow
all eleven proof steps: coefficient normalization and qcqs/Noetherianity; localization;
finite extension; cofinal Qlbar colimit; constructible preservation by generators;
canonical scalar/pull/tensor coherence; base change on generators; common finite field
for generator pairs; projection on pairs; shift compatibility including connecting maps;
and the one-variable and successive two-variable cone/shift inductions.

Edge cases checked: K=0; M=0; empty schemes and empty strata; p=id; g=id and arbitrary g;
E=F (the identity coefficient inclusion is allowed); rank-zero lattices; bounded-below
complexes with infinitely many nonzero positive cohomology groups; Qlbar generators over
different finite fields (handled by a common compositum in the proof, not an input
restriction). None is excluded. The site object/morphism and coefficient universes remain
those of the recorded framework, Scheme.{u} and Ab.{u+1}; no equality of independent site
universes is imposed.

Searches performed before drafting:

- `msearch.py ... leanfinder "proper pushforward commutes with extension of condensed l adic
  coefficients and projection formula"`: eight condensed-category hits (profiniteSolid,
  profiniteSolidCounit, profiniteSolidification, its Kan-extension instance, LightCondensed
  ihomPoints_symm_comp, lanPresheaf, LightCondMod.hom_naturality_apply, lanCondensedSet),
  none stating this node.
- `msearch.py ... loogle "IsProper, IsIso, derivedPushHom"`: zero, unqualified IsProper unknown.
  Repeated with `AlgebraicGeometry.IsProper`: twelve proper-morphism class/property hits;
  no rational coefficient comparison or projection theorem.
- `msearch.py ... grep "derivedPushHom|boundedConstructibleBaseChange|projectionFormula"
  AlgebraicGeometry`: zero Mathlib hits. Direct reading of Mathlib Proper.lean confirms the
  properness class, not a matching sheaf theorem.
- `rg` in the slopmaster2 `WeilConjectures/` for the exact node id, derivedPushHom and candidate
  rational theorem names: no complete match. The current shared framework Proper.lean has
  just the two proper base-change statements. Current Compatibility.lean has the finite
  comparison on all unbounded objects and the proper Qlbar comparison at bounded-below
  objects, but no complete localization/constructibility/projection conjunction.
  Neither is this node as a whole.
- `rg` in `lean/Sheaf` found the existing canonical projection helper in
  RationalLocalizingProjectionFormula and, by DAG and blueprint search, the separately
  landed `def-sfb-module-object-projection-map`. The latter is used. The downstream
  localizing projection theorem is not imported or made a statement prerequisite.
- `python3 tools/blueprint_refs.py search "projection formula"`, and DAG searches for the
  projection and coefficient maps: reused the existing definition node, no new node.
- Candidate declaration names were searched in `dag/lean_names_upstream.json`, Mathlib,
  slopmaster2, and `lean/Sheaf`; none of the final six theorem names or three helpers
  already exists.

There is no statement dispute, statement correction, or dependency-module repair.
Compilation: the final module passes the prescribed scompile.py checks without errors
or warnings (library export 51.2 s, under the fixed 60 s compiler limit).

## Second reading by NY

This is the author's separate second pass with the node and module open; the dispatcher
brief forbids starting other agents, and the maintainer supplies the independent reading.
I checked all hypotheses and all three clauses against the current source blueprint.
The three bounded-below hypotheses are retained. The final three theorems quantify over
precisely the two rational coefficient cases by equality of bundled rings, fixing their
multiplication and unit. Projection has independent Dbc arguments on X and Y. Base change
quantifies over every cartesian square of standing k-schemes and every Dbc object; the
componentwise conclusion is equivalent to the natural-transformation assertion.

I checked the directions of the coefficient maps (extension after pushforward to pushforward
after extension) and projection mate (Rp*K tensor M to Rp*(K tensor p*M)). The specified
canonical maps are inverted, not unspecified isomorphisms between their endpoints.
The current bounded-constructible dependency requires the general internal-module predicate;
that predicate is used throughout. The current base-change dependency is the OfPreserves
construction, used with the named existing preservation proof and no preservation assumption.
The existing projection definition is reused. The rationalization helper uses the recorded
mate and extracts flatness from the recorded localization theorem by existential elimination;
no coefficient object, morphism, or proof data are sorry inside a definition.

The final formulation uses three coefficient theorems and three rational theorems, rather
than duplicating the last three for each field case. This is the source's own disjunction
"Λ=E or Qlbar". Local irreducibility attributes and synchronous elaboration avoid unnecessary
expansion during compilation; they impose no mathematical hypothesis and change no definition.
No mathematical mismatch requiring a statement correction was found.

## Final validation

Ran `scompile.py NY det-thm-sfb-proper-base-change-rational` on the final module and a
separate temporary importing consumer. The final module passed preliminary, sandbox, and
library-export compilation without warnings. The consumer imported it successfully and
printed all nine recorded declarations with universes visible. Every declaration has one
explicit scheme universe; all six statements retain the base field characteristic facts,
the separated finite-type standing hypotheses, and properness of p. Base change additionally
retains all four standing schemes and the cartesian square, with no condition on g.
The preservation and projection statements have only the displayed rational-coefficient
case hypothesis; the base-change statement supplies preservation as a proof term, not as
an additional hypothesis. The development-only consumer (including its pretty-print
option and style warnings) has been removed and is not delivered.

Rechecked all final declaration names in Mathlib, slopmaster2, shared lean/Sheaf, and the
upstream name index: no collision. Rechecked the current DAG: all recorded statement and
stated proof dependency modules are directly imported. The item differs from the shared
node only in `lean` and the two permitted landed definition dependencies in `stmt_deps`.
