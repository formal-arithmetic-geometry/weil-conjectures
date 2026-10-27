## Worker report

The module `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` states the coefficient
compatibility square, both of its canonical restrictions, and the two Dctf endpoint
assertions. Every theorem proof is `sorry`; the three helper definitions have actual
composite-map data. The node statement and all dependencies are unchanged.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-compact-support.proof.md`, Composition, together
with the complete six-step proof in the assigned node. The module docstring identifies
this source; the theorem docstring gives all six proof steps and their dependencies.

Hypotheses, in node order:

* Prime ell is `(ell : ℕ) [Fact ell.Prime]`; the field and characteristic are
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]`.
  A positive prime characteristic is precisely positive characteristic p with p prime.
* The four schemes X (the node's Xbar), Y, Ybar and `c.obj.obj.Z` (W) have explicit
  `.Over (Spec (.of k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  binders on their structure maps. Locally finite type plus quasi-compact is finite
  type. The four `.IsOver` binders put p, i, j' and r over the same k.
* `Λ Λ' : ScalarSixRing.{u}` are bundled commutative condensed rings. The morphism
  `a : Λ ⟶ Λ'` has `_ha : ListedCoefficientMap ell a`. Its six constructors give
  precisely finite ell-primary maps, finite-extension valuation-ring and field maps,
  valuation-ring localization, finite-field-to-Qbar inclusion, and continuous
  integral-to-finite maps. `comp` allows finite composites and the identity cases
  are retained. Qbar is `Profinite.padicAlgClRingObj`, the finite-subextension convention.
* `[IsProper p]`, `[IsOpenImmersion i]`, `[QuasiCompact i]` render proper p and
  quasi-compact open i. `c : Compactification.BoundaryCompactification (p ≫ i)`
  supplies the commuting triangle, proper r and quasi-compact open j'.
  `[IsSchemeTheoreticallyDominant c.obj.obj.i]` is scheme-theoretic density.
  No arbitrary Cartesian-square or comparison-isomorphism hypothesis is added:
  the open-subscheme equality follows from properOpenInterchange with these hypotheses.
* `A` is an object of the ordinary unbounded derived category of internal modules
  over `condensedRingObj Λ.X X`. `hA` is the conjunction of
  `constantModelBoundedConstructible Λ.X X A` and `DerivedCategory.finiteTorAmplitude _ A`.
* `m` and `m'` are the iota maps at A and T A, respectively. `_hm` and `_hm'` use
  `compositionInterchangeIsNormalized` at their two coefficients. These are the
  exact defining normalization of the node's canonical maps, not additional freedom
  to select an unrelated morphism. The recorded properOpenInterchange gives their
  existence and uniqueness on the entire unbounded category. Quantifying over the
  uniquely characterized arrows avoids a new choice-based definition of iota.

Conclusions and maps:

* `scalarSixChange a V` is definitionally the published total derived scalar extension
  along `coefficientMap a.hom.hom V`, with no completion.
* `RootCoordinateFace.lower Λ.X f` abbreviates `moduleObjectDerivedPushforward`,
  whose real body is `(lowerStar Λ.X f).rightDerivedFunctor`.
* `scalarDirectImageMate a f` is exactly the unit / inverse normalized pullback
  comparison / scalar extension of counit map used by scalarSixDirectImage.
* `derivedOpenImmersionShriekIso a.hom.hom j` is the recorded canonical open
  conjugate, definitionally at these scalar functors. Its `.hom.app` is delta.
  The newer scalarSixOpenScalarIso alias is not needed: the published build does
  not expose that recent alias yet, so the module uses the upstream declaration directly.
* `scalarProperOpenLeft` is T(m), then gamma_r at j'_! A, then Rr_*(delta_j',A).
  `scalarProperOpenRight` is delta_i,RpA, then i_!(gamma_p,A), then m'.
  The first conjunct asserts equality of these routes, in Lean's left-to-right
  composition order. Their type is precisely T_Ybar i_! Rp_* A to Rr_* j'_! T_X A.
* `scalarProperOpenRestriction` first uses the Lambda' i-open unit, then i* of
  delta_i inverse, then i* of the supplied route, then the recorded canonical
  `compositionInterchangeRestriction` rho. Its source is T_Y Rp_* A; its target
  is Rp_* j'^* j'_! T_X A. The second and third conjuncts assert that this is
  gamma_p,A followed by Rp_* of the actual j'-open unit. That unit is invertible,
  so these are exactly the two claims that restriction is gamma_p,A under the
  canonical identifications. No arbitrary isomorphism or extra IsIso binder appears.
* The fourth and fifth conjuncts give bounded constructibility and finite Tor
  amplitude over Λ' of the exact common source and exact common target separately.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `derivedOpenImmersionShriekIso` (the recorded coefficient-change
  and open-comparison nodes). Their full signatures and conjugate formulas were read.
* `Sheaf.SixFunctors.ScalarSixDirectImage`: `scalarSixDirectImage`; its public
  `ScalarDirectImageMateCoherence` supplies `scalarDirectImageMate` and its normalized
  pullback data. The full direct-image theorem and mate definition were read.
* `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixPullback`, with the published
  `ScalarSixDefinitions.scalarSixChange`. Its body specializes the upstream
  scalar adjunction without changing it; the open comparison uses the upstream
  `derivedOpenImmersionShriekIso` directly.
* `Sheaf.Paper.ProEtaleProperOpenInterchange`: `properOpenInterchange`,
  `compositionInterchangePullback`, `compositionInterchangeRestriction`, and
  `compositionInterchangeIsNormalized`; the entire module was read.
* `Sheaf.Compactification.BoundaryRefinement`: `BoundaryCompactification` and
  `DenseBoundaryCompactification`; the item uses the former plus its exact density
  predicate. The latter would bundle the same condition.
* `Sheaf.Paper.FiniteConstantRingedLocalModel` publicly preserves the recorded
  `CondensedConstantConstructibility.constantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor` definitions. The recent ringed-site extension
  of this dependency is not needed for these internal-module coefficients.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the ambient setting's `compactificationOverField`; the standing hypotheses are
  rendered explicitly rather than introducing a second setting predicate or choice.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`;
  exact body read, and the recorded adjunction interfaces remain public.

Every stated proof dependency is imported as a plain proof import, unless already
one of the public statement imports. ScalarSixDefinitions is publicly re-exported by
the recorded ScalarSixPullback interface; its redundant direct proof import was removed
after the first server compile diagnosed a stale published ScalarSixPullback artifact
from before the recent definition-module refactor. No dependency repair or new node is required.

Edge cases checked before drafting:

* A zero derived object and empty schemes are allowed; no Nonempty or nonzero binder.
* The finite zero coefficient ring is admitted by ListedCoefficientMap.finite.
* Identity coefficient maps, identity opens, p an identity, and c the trivial dense
  compactification use the same units and normalization and reduce to the expected
  mate/naturality identities; none is excluded.
* Nonflat finite-ring maps are allowed. Only derived tensor is used, and no flatness
  or t-exactness of scalar extension is assumed.
* Integral-to-finite, localization and Qbar maps keep the same canonical comparison;
  there is no completion or replacement by all continuous Qbar-valued functions.
* A is bounded constructible of finite Tor amplitude, but the arrows and adjunctions
  are taken in the ordinary unbounded categories, as required. No fixed Tor interval
  or cohomological lower bound is imposed.
* The single universe u is the existing small-site convention: schemes in Type u,
  pro-etale site object size u+1, and internal abelian sheaves in Ab.{u+1}. No site
  object/morphism universe equality or extra coefficient-size constraint is imposed.

Searches actually made for an existing statement:

* msearch leanfinder: `Derived extension of coefficients commutes with the normalized
  proper open interchange square` returned eight normalization/localization results,
  including Scheme.Hom.ι_fromNormalization; none concerns this derived coefficient square.
* msearch loogle: `CategoryTheory.Adjunction, "mate"` returned twelve general mate
  declarations, including mateEquiv and its composition identities; none is the node.
* msearch grep: `interchange.*coefficient|coefficient.*interchange`, CategoryTheory:
  zero hits.
* msearch leansearch: `Change of coefficient ring commutes with the proper open
  interchange morphism in derived categories of sheaves` returned eight scheme
  structure-sheaf/restriction results; none matches.
* rg on `lean/WeilConjectures` and `lean/Sheaf` for
  `scalar.*(Interchange|interchange)|properOpen.*[Ss]calar|compositionInterchange`
  found the existing proper/open geometry and unrelated finite-etale/adic comparison
  modules, but no theorem of this condensed pro-etale square. grep for the exact
  assigned node id in WeilConjectures had no hit. rg for scalarProperOpen,
  properOpenScalar and scalar/interchange in dag/lean_names_upstream.json had no hit.

No statement correction, statement dispute, hollow definition or dependency fault found.

## Second reading by NV

A separate pass by this worker re-read the node, all three composite-map definitions,
and the theorem; no other agent was started, per the dispatcher instruction. The
maintainer's independent review remains separate. The pass checked the direction of
both delta maps: both routes use delta.hom, while restriction uses i* delta.inv to
identify its source. It checked that rho is followed implicitly by the inverse of
Rp_* u_j' when interpreting the forward-unit equation. The RHS therefore really is
gamma_p rather than an unspecified isomorphic arrow. It checked the normalization
predicates at A and T A, the four finite-type separated schemes and k-linearity, all
coefficient cases, and both endpoint predicates. The existential properOpenInterchange
interface means iota must be quantified with its defining normalization; treating an
unconstrained map as iota would have been incorrect. No node text changed.

Validation: the module compiles through scompile.py in sandbox and library mode.
The intermediate line-width warnings were repaired; final clean verification and
the prescribed delivery dry run are run before the push.
