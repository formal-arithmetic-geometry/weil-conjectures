## Worker report

The module `Sheaf.Paper.ProjectionFormulaCoherence` states the projection-formula
coherence clauses for the datum in the node.  It introduces no replacement operation
or arbitrary comparison.  The helper `sixFunctorProjectionExchange` is the endpoint
transport of the recorded `SixFunctorExchangeData`; the three `sixFunctorProjection*Mu`
definitions are the recorded canonical pullback/tensor comparisons conjugated by the
operation-datum equalities.  All data in these definitions are real constructions.

The hypotheses and clauses are rendered as follows.

* The datum hypothesis is the explicit `S : SixFunctorDatum D C E n hn`, with the
  field, algebra, finite-dimensionality, positive-level, and four site categories
  inherited from that structure.
* Naturality in `K,L,f` and the four coefficient stages is stated by
  `sixFunctorProjection_naturality`, with the finite, integral, rational, and
  common-stage component equations and the recorded finite-Tor hypotheses.
* Compactification independence is `sixFunctorProjection_compactification`, using
  `S.comparison` and the supplied comparison cocycle.  Composition and the A4
  compositor are `sixFunctorProjection_composition`; the threefold associativity
  equation is `sixFunctorProjection_pentagon`.
* The proper direct-image identification is `sixFunctorProjection_proper`, using
  `S.*.properIdentification` and the recorded proper counit mate.
* The integral, rational, and common-stage Cartesian base-change equations are
  `sixFunctorProjection_baseChange_integral`,
  `sixFunctorProjection_baseChange_rational`, and
  `sixFunctorProjection_baseChange_common`.  Their terms explicitly contain the
  exchange, the `Mu` monoidality isomorphism, both pullback compositors, and the
  square equality `Q.squareComm`.
* The identity clause is `sixFunctorProjection_identity`.  For each stage it
  quantifies the identity pullback unitor by its compositor normalization and uses
  `sixFunctorProjectionIdentitySupport`; the finite clause additionally uses the
  recorded Tor-domain inclusion and `sixFunctorProjectionTorIdentity`.
* The finite square is `sixFunctorProjection_baseChange_finite`. Its upper map is
  `S.finite.pull Q.g` applied to `CompactSupportFiniteProjection.component`.
  Its exchange helper uses `(S.finiteExchangeProjection Q).2.1` explicitly;
  `finitePullback`, `finiteSupport`, the coefficient units and counits, and the
  fixed pullback comparison supply exactly its endpoint identifications. Its target
  compactification is the Cartesian base change; the compactification clause supplies
  every other target choice. `sixFunctorProjectionFiniteMu` uses the actual K-flat
  tensor comparison, and `torPullComposition` plus `Q.squareComm` identifies the last
  pullback. The first input remains arbitrary bounded constructible.
* The current source's all-ideal finite-reduction clause is
  `sixFunctorProjection_reduction_finite`. The predicate
  `sixFunctorProjectionFiniteReductionSquare` exposes both composites. Its upper map
  is the actual S component conjugated by `sourceComparison`, `targetComparison` and
  the coefficient equivalence, then tensored with the degree-zero constant quotient
  by `J`. The right comparison is projection at that quotient. The lower-right
  comparison is the K-flat monoidality map followed by the inverse tensor associator.
  This keeps reduction in the original coefficient category, exactly as the source
  of `prop-sf-pf-reduction` explains. The lower ambient component deliberately admits
  nonperfect quotients whose reduced second input has infinite Tor dimension.
* `sixFunctorProjection_reduction_integral`, `_rational`, and `_common` state the
  corresponding right-tensor/reduction equation on S's actual completed or field
  projection components. Their associators are the prescribed coherent-system,
  localized, and common-stage associators transported through the datum's tensor
  normalizations. They retain the tensor coefficient object N explicitly, so the
  constant-quotient specializations include identity and zero reduction.
* `sixFunctorProjection_realization` retains the actual finite realization equation.
  It is additional useful normalization; scalar-extension and coefficient-ring
  naturality are no longer claimed as clauses after the source correction below.

The dependency declarations used are:

* `Sheaf.Paper.SixFunctorDatum`, `WeilConjectures.SixFunctorDatum`;
* `Sheaf.Paper.SixFunctorDualNotation`,
  `WeilConjectures.SixFunctorDatum.finiteCoefficientDual`;
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`,
  `AlgebraicGeometry.ProEtale.originComposition`;
* `Sheaf.Paper.ConstructibleProjectionMates`,
  `WeilConjectures.CompactSupportFiniteProjection.component`;
* `Sheaf.Paper.CompactSupportProjectionFormula`,
  `WeilConjectures.compactSupportProjectionFormula` and
  `WeilConjectures.compactSupportProjectionFormula_coefficients`;
* `Sheaf.Paper.CompactificationProjectionPasting`,
  `CategoryTheory.SuppliedExchangeProjection.CompactificationPastingData.compactification_pasting`;
* `Sheaf.SixFunctors.OpenBaseChangeSquare`,
  `WeilConjectures.OpenProjectionBaseChange.openBaseChangeSquare`;
* `Sheaf.Paper.CoefficientRealizationTransport`,
  `CategoryTheory.coefficientRealizationTransport`;
* `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate`,
  `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`;
* `Sheaf.Paper.ExchangeFunctoriality`,
  `WeilConjectures.exchangeFunctoriality`;
* `Sheaf.Paper.ProjectionFiniteReduction`,
  `WeilConjectures.projectionFiniteReduction`;
* `Sheaf.Paper.SfProEtaleProjectionFormula`,
  `WeilConjectures.sf_proetale_projection_formula`.

I checked the identity morphism, empty schemes and zero inputs, positive level
`n = 1`, and arbitrary compactifications. The repaired reduction square includes
`J = 0` (identity reduction), `J = ⊤` (zero reduction), and nonperfect quotients
of finite coefficient rings; no flatness or finite-Tor condition is placed on J.
The generic higher tensor equation retains N equal to the unit and zero object.  The finite-Tor predicates occur only where the
recorded operation interfaces require them.  The residue-field invertibility
instances used in the `Mu` definitions are inlined from the canonical inverse of
`PurCompactSupport.coefficientPrimeUnit`, mapped by the scheme residue-field algebra
map. No declaration from the open base-change theorem is used in a definition, and
no site-universe equality is imposed.

Searches for an existing statement or definition were made before writing:

* `msearch.py ... leanfinder "Compact support projection formula coherence, identity, composition, compactification independence, base change and coefficient reduction"`: eight unrelated `Profinite.NobelingProof` hits; no match.
* `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Functor"`: only generic
  Mathlib adjunction declarations; no compact-support projection coherence.
* `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointProjectionMap, CategoryTheory.Adjunction.ProjectionCompCompatible"`: unknown identifier/no match.
* `msearch.py ... grep "(Projection.*Coherence|projection.*baseChange)" CategoryTheory`: no match.
* `rg` over `WeilConjectures` and `Sheaf` found only the finite etale/pro-etale
  exchange theorem, the operation-datum records, and the imported projection-law
  modules listed above; no declaration states this node's all-stage conjunction.

The repaired file is checked with the prescribed `scompile.py`; compiler results
and delivery preflight are recorded below.  No definition contains `sorry`; every theorem proof is `by sorry`.

## Second reading by Q51

This is Q51's own rereading after the independent maintainer return, not a claim of
another worker's independent review. The independent return accepted the structural,
identity, proper, and higher-stage base-change clauses. Those clauses are retained.
I read the new finite square against A2: its exchange comes from S, its projection
is S's full-domain component, and its endpoint maps are the prescribed comparisons.
I checked the all-ideal square against the current theorem and reduction source:
reduction remains in the original coefficient category, so it does not assert that
an arbitrary quotient preserves the bounded finite-Tor domain. No first-input Tor
hypothesis or quotient flatness is introduced. The six residue-field unit instances
in the original Mu definitions are now written with their actual data.

## Returned-head repair

H3: Removed the foreign declarations `compactSupportProjectionFormula`,
`compactSupportProjectionFormula_coefficients`, and
`AlgebraicGeometry.ProEtale.compactification_projection_exchange_coherence` from
`lean.declarations`; the foreign finite theorem is not imported. Added the actual
finite square for S and the all-ideal finite-reduction square for S's component.
The current blueprint_update is recorded below with the complete citer audit,
as explicitly permitted in the return. Existing coefficient theorems are proof
imports only and are not presented as this item's statements.

H2: Inlined the inverse-residue-field construction from the canonical coefficient
prime unit in every Mu definition. `OpenBaseChangeSquare` is only a proof import.

## Statement corrected

The old statement is retained verbatim in `statement_change.old_statement`.
The current theorem source, order 3344 at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.md`,
removes coefficient-ring naturality, scalar extension and realization from its last
clause and instead requires the all-ideal finite-reduction square. This is the
node's `blueprint_update` (commit 7284bb09daf97437d544c51882b325f9c52cd345),
and the independent return explicitly permits recording it by §1(C). The sandbox
node now uses that source statement verbatim. The unit file is not changed.
The statement dependencies add `prop-sf-pf-reduction`, which the corrected text cites.
The inherited proof and its dependencies are retained: its structural and reduction
arguments apply, while the extra coefficient discussion is not claimed as a conclusion.

Citer audit (all direct statement/proof citers, selected from the required rg scan):

* `lem-sf-kunneth-coherence` — holds true: Uses the Cartesian square and identity normalization, both retained.
* `lem-sf-kunneth-first-open-substitution` — holds true: Uses composition and input naturality, both retained.
* `lem-sf-kunneth-second-open-substitution` — holds true: Uses base change, proper coincidence, composition and naturality, all retained.
* `lem-sf-middle-exchange-projection-base-change` — holds true: Uses only the displayed Cartesian square and naturality in the first input.
* `lem-sf-product-compactification-identity` — holds true: Uses refinement and compactification independence, both retained.
* `lem-sf-relative-product-base-change-factor-squares` — holds true: Uses the Cartesian projection square and naturality, which are unchanged.
* `lem-sf-relative-product-coefficient-factor-squares` — holds false: Its projection-factor argument invokes coefficient naturality, no longer a clause of the updated source.
* `lem-sf-triple-compactification-normal-form` — holds true: Uses naturality and compactification/refinement compatibility, all retained.
* `prop-base-linear` — holds true: Uses only naturality in the two projection inputs.
* `prop-sf-mixed-cup-coefficient-change` — holds false: Uses scalar-extension and rationalization intertwining, removed by the blueprint update; must cite A5 or a coefficient theorem.
* `prop-zl-smooth-proper-relative-purity` — holds false: Its proof invokes scalar-extension coherence from this item; that use must cite a coefficient comparison theorem.
* `sk-thm-sf-compatibility` — holds true: Its use of this item is structural tensor coherence; clause (7) independently cites fix-prop-coherence.
* `sk-thm-sf-package` — holds false: Its proof also invokes coefficient comparisons from this item; those must now be supplied by A5 or the coefficient theorem.

The four breaking citers are named for maintainer follow-up and are not edited.
No new definition node or dependency repair is needed: the new definitions are
endpoint/comparison helpers for the owning node, built from existing notions.

## Verification

The repaired module compiled through `scompile.py` with no errors or warnings
(sandbox 59.1 s including wrapper scheduling, owning module 45.8 s). Static checks
found 15 named theorem statements and exactly their 15 postponed proofs, no `sorry`
in definitions, no overlong lines, and an exact node signature match.
The delivery dry run passed: `OK (dry run): commit aaa88287fe2 passes the
preflight and compiles; nothing pushed`. The final delivery runs the same checks.

Repair-specific source searches: `rg` in `SixFunctorOperationDatumStages.lean`,
`SixFunctorOperationDatum.lean`, and `ConstructibleProjectionMates.lean` located
`finiteExchangeProjection`, `pullRealization`, `fixedPullRealization`,
`fixedSupportRealization`, `sourceComparison`, `targetComparison`, and the partial
finite tensor domain. `rg` over the upstream projection/reduction modules located
the all-ideal reduction convention: right tensor by the constant quotient, kept
in the original coefficient category. `DerivedPullbackTensorIso.lean` supplies the
normalized integral, rational and common-stage associators. No replacement for
those notions was introduced. The required text scan for the item followed by
JSON dependency filtering yielded exactly the 13 citers recorded above.
