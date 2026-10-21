## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence` states all clauses of
`lem-pur-etale-sum-right-adjoint-coherence`. Its six theorems have `sorry` proofs. Its six
helper definitions contain actual constructions; none chooses a mere existing isomorphism
or an unspecified normalization. The natural-language proof in each theorem docstring
identifies the relevant steps of the node's nine-step proof.

Hypotheses and objects:

- A finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The existing coefficient-size convention is retained, including the zero ring. No
  nontriviality or invertible-prime assumption is added.
- Ordinary unbounded constant-A module categories are the recorded
  `DerivedCategoryModule A X`, namely `DerivedCategory (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} A))`. There is no Plus, bounded, constructible or perfect restriction.
- Schemes are `Scheme.{u}` with `[IsNoetherian X]` for each scheme occurring in a theorem.
  Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`, precisely the
  finite-affine-cover condition of the node. Compactification middle schemes are finite
  type over Noetherian targets, hence Noetherian; no assumption on them is lost.
- The relevant arrows have `[Etale e] [IsSeparated e] [QuasiCompact e]`.
  Etale already implies locally finite presentation and locally finite type, so
  quasi-compactness expresses finite type without an extra independent hypothesis.
  The same conditions hold for v and for the base-changed e' and e'' where used.
- Chosen compactifications are the existing `[HasCompactification e]`, etc., including
  `[HasCompactification (e ≫ v)]` in the composition assertion. The arbitrary
  compactifications `c d : Compactification e` in the refinement assertion show that
  this chosen model imposes no restriction on compactification choice.
- `G`, `G_e`, `G_v`, `G_ve`, `G'`, `G''` and their `adj` arguments quantify over the
  specified right adjoints and adjunctions of the actual compact-support functors.
  Existence is the recorded exceptional-adjoint theorem. Supplying the adjunctions is
  the node's instruction to write F_a adjoint to G_a with its counit, not an additional
  mathematical condition on the arrows.
- A Cartesian square is `(sq : IsPullback w' e' e w)`, the established equivalent
  representation of the dependency's chosen Cartesian-square data. Every Cartesian
  square is allowed, not just one presentation of the chosen fiber product. No
  separatedness, finite type, flatness or etaleness is imposed on the arbitrary base
  map w. This follows the explicit 'along any w' clause and proof steps 7–8.

Clause-by-clause translation:

1. `etaleSumSupportIso A e` is d_e. It transports from the actual chosen compact-support
   functor by `(rightDerivedLowerShriekIso A c).symm`, then uses
   `canonicalEtaleCompactSupportComparison A e c` for the chosen c. The latter is the
   inverse of the graph-extension sheaf map descended through homotopy localization
   and the total-right-derived unit. This is the proper-support/sum identification,
   not an independently selected natural isomorphism. Its graph and derived-unit
   characterization is the same one used in `quasifiniteCompactSupportExact` and
   `etaleSupportMapCompatibility`.
2. `derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat A) e inferInstance` is
   S_e adjoint to e^*, including the degreewise derived sum/evaluation counit.
   `etaleSumRightAdjointIso A e G adj` is exactly
   `conjugateIsoEquiv adj sumAdj (etaleSumSupportIso A e).symm`, i.e. rho=(d^-1)^c.
   `etaleSumPullbackUnitIso` transports the existing left-derived unit identification
   to the exact derived inverse image; it introduces no new unit convention.
   `etaleSumRightAdjointUnitIso` is rho at `constantComplex A X` followed by this
   pullback-unit identification, precisely eta.
3. `etaleSumRightAdjointCompIso` is c_{v,e}, defined by conjugating
   `unboundedEtaleLowerShriekCompIso A e v` against `adj_ve` and `adj_e.comp adj_v`.
   In `etaleSumRightAdjoint_comp`, the left side is rho_ve followed by the specified
   `unboundedEtaleUpperStarCompIso A e v`. The right side is c_{v,e}, then
   rho_e at G_v(K), then the exact e^* applied to rho_v at K. Lean's composition
   order is the reverse of the TeX functional notation. K is arbitrary in D(T_et,A).
4. `etaleSumRightAdjoint_id` compares rho_id followed by the canonical pullback
   identity with the conjugate of the specified compact-support identity. Thus the
   identity clause uses the actual canonical identity comparison, even for an
   arbitrary chosen right adjoint and its counit.
5. `etaleSumRightAdjointBaseChange` is b_{e,w}. Its body installs the invertibility
   theorem for the actual `unboundedEtaleCompactSupportBaseChange A sq`, applies
   the inverse component at G(A_X), then w^* of `adj.counit.app A_X`, then the
   canonical w^*A_X -> A_X' map, and finally `adj'.homEquiv`. Applying the hom
   bijection after the unit identification is exactly the same as following the
   adjunct by G' of that identification, by naturality of the adjunction bijection.
6. `etaleSumRightAdjoint_baseChange` states b followed by eta_e' equals w'^*(eta_e)
   followed by w'^*A_U -> A_U'. This last factor explicitly inserts the constant
   identification suppressed in the node's displayed formula.
7. `etaleSumRightAdjoint_evaluation` states the displayed derived evaluation
   equation for the inverse of the *specified* `exactEtaleSumExchange A e w`.
   That helper is the degreewise inverse of `etaleLowerShriekBaseChangeMap A w e`,
   whose invertibility is `isIso_etaleLowerShriekBaseChangeMap`, with the standard
   derived-composition identifications. The left side is its inverse followed by
   w^*(ev_e,A_X), then w^*A_X -> A_X'. The right side is S_e' of the explicit
   identifications w'^*e^*A_X -> A_U' -> e'^*A_X', followed by ev_e',A_X'.
   Thus both sides have exactly the same domain before the suppressed pullback
   identifications; no arbitrary replacement for the specified sum comparison is used.
8. `etaleSumRightAdjoint_refinement` states equality of the normalization at c
   with the conjugate of the canonical c-to-d comparison followed by the normalization
   at d. It holds for arbitrary c,d, so in particular for every proper refinement.
   This is the common-refinement form of the same assertion, since the existing
   `rightDerivedLowerShriekOfCompactificationIso` is constructed through the actual
   common refinement. Combined with the specified compositor/exchange coherence of
   the dependency, it makes the preceding equations independent of compactification.
9. `etaleSumRightAdjoint_openRestriction` gives the explicit pasting equation for b
   for a Cartesian square followed by a Cartesian open restriction (`[IsOpenImmersion k]`).
   The first two squares and their pasted square are arbitrary IsPullback witnesses;
   the pasted witness exists by pullback pasting. Its left side is k'^*(b_1) followed
   by b_2. Its right side is the inverse canonical pullback-composition identification
   followed by b for the pasted square. This compares the actual maps defined by
   the exchange and counit. The other displayed identities also apply on all these
   restricted schemes; no new right-adjoint normalization is selected on restriction.

Dependency declarations used (module and name):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `constantComplex`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
  `def-weil-scheme-morphism-properties` is a convention node, so it has no module.
- `WeilConjectures.Compactification.Refinement` and its imported definitions:
  `Compactification`, `Compactification.Refinement`; the chosen compactifications are
  from `HasCompactification.compactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`;
  `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` and its upstream import
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`:
  `derivedEtaleLowerShriekUpperStarAdjunction` (the fully derived sum/evaluation adjunction).
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`:
  `quasifiniteCompactSupportExact`, which supplies the proper-support/sum interpretation
  and its actual-compositor compatibility. Its old existential statement is not used
  to choose data: the already constructed uniquely graph-normalized comparison is used.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, `conjugateEquiv`,
  `mateEquiv` and the mate-pasting calculus;
  `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `Adjunction.id`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekId`,
  `unboundedEtaleUpperStarCompIso`, `unboundedEtaleUpperStarIdIso`,
  `unboundedEtaleCompactSupportBaseChange`, `unboundedEtaleCompactSupport_baseChange`,
  and its composition/refinement equations. These are the actual specified maps.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`;
  the theorems use the equivalent `IsPullback` witness, as permitted by STATE.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `etaleLowerShriekBaseChangeMap`;
  `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`:
  `isIso_etaleLowerShriekBaseChangeMap`.
- Added existing statement dependencies: `def-asd-compact-support-graph-comparison`
  (`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData`,
  `exactEtaleSumExchange`), and
  `lem-asd-compact-support-graph-derived-isomorphism`
  (`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso`,
  `canonicalEtaleCompactSupportComparison`). These already landed notions give the
  canonical maps named in the item's prose. No new node or dependency repair is needed.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarUnitIso`, with the existing
  `leftDerivedUpperStarIsoMapDerivedCategory` for exact inverse image.
- Proof-only modules are imported without public, including
  `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`:
  `etaleSupportMapCompatibility`; the sheafification, homotopy adjunction,
  localization, inverse-image exactness, and module-linear exchange dependencies
  are also imported as the stage-3 proof plan requires.

Edge cases checked before writing: empty schemes and empty sets of etale lifts give empty
sums and the same zero counit on both sides; the zero coefficient ring is allowed; arbitrary
unbounded K is retained; identity and composite arrows have explicit equations; w need not
be etale, flat or finite type; c.g need not be finite; arbitrary compactifications and proper
refinements are retained; further open restrictions include empty and identity opens. The
formulas are categorical, so they also cover zero complexes and vanishing summands. The
coefficient/site universes match the recorded six-functor convention without any extra
universe equality.

Searches (2026-10-21):

- `msearch.py ... leanfinder "Right adjoint normalization of etale sum extension preserves
  composition and arbitrary base change via evaluation counits"`: 8 hits, concerning
  etale algebra composition and scheme normalization, none the requested theorem.
- `msearch.py ... loogle "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp"`:
  12 hits, including conjugateEquiv unitors, whiskering, associators and iterated mates.
  These provide the generic calculus, not this normalized etale theorem.
- `msearch.py ... grep "etaleLowerShriek|rightDerivedUpperShriek" CategoryTheory`:
  0 Mathlib hits. Mathlib does not contain the requested etale functor package.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `normalizedEtaleSum`, `etaleSumRightAdjoint`, and normalization/coherence vocabulary:
  no existing theorem for this node. Reading the nearby normalization, support-map,
  horizontal-tower, sum-adjunction and compact-support-comparison sources identified the
  existing canonical maps reused here. No second definition of sum extension or any
  compact-support compositor/exchange is introduced.

Sources read: the item's full nine-step proof; each statement dependency's node and recorded
source signature/docstring; blueprint main-20261015
`sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`, Step 1;
local Stacks `etale-cohomology.tex` lemma-shriek-base-change (03S6), and `more-etale.tex`
lemma-shriek-composition (0F7J), lemma-pseudo-functor (0F7K).

No statement correction, disputed statement, hollow definition or new node is present.
Only the item's lean record and the two permitted additions of landed statement dependencies
change. Compilation uses only the prescribed scompile/deliver2 server wrappers.

## Second reading by Q84

The dispatcher explicitly assigned one worker and prohibited starting other agents. This is
therefore an in-thread second reading, not a claim of an independent second worker; the
maintainer's independent delivery review remains applicable as stated in the brief.

Reopened the node and final module together. Checked the direction of d^-1 and of the
conjugate, the order `adj_e.comp adj_v` (right adjoint G_v followed by G_e), and the
placement of the pullback compositor on the left side of the composition formula. Checked
that b uses the inverse actual C at G(A_X) before the pulled-back counit. Checked the
explicit constant-unit maps at the ends of both base-change and evaluation equations,
including the inverse e'^* unit map inside S_e' on the evaluation right side. Checked that
the refinement conjugate uses the inverse left comparison, hence goes from G to H, and
that the open-pasting equation compares maps with the same source after the inverse
pullback compositor. The initial version lacked an explicit further-open-restriction
formula; this was repaired by adding `etaleSumRightAdjoint_openRestriction` before delivery.
No restriction to bounded-below objects, an etale base map w, a finite proper factor, or
nonzero coefficients was introduced. All postponed proofs are named and documented.
