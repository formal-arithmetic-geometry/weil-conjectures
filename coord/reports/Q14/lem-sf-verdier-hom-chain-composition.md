## Worker report

The delivery states `lem-sf-verdier-hom-chain-composition` in
`Sheaf.Paper.VerdierHomChainComposition`. The main declaration is
`WeilConjectures.VerdierHomChainComposition.verdier_hom_chain_composition`.
The node's clauses are distributed over the declarations recorded in
`lean.declarations`: representation, naturality, composition, Verdier specialization,
identity, coefficient transposes, and composition after coefficient change.
Every theorem has exactly `by sorry`. Definitions give actual functors, equivalences,
arrows, isomorphisms, or predicates, without postponed data. The only proof fields
in the new isomorphism `exchange` are references to the separately named
`representing_chain` theorem, whose inverse equations determine those fields.

### Hypotheses and clauses

- The fixed finite field, algebraic closure, unequal primes, and coefficient algebraic
  closure are `D : FiniteFieldDatum.{u}` and `B : D.CoefficientDatum`. The finite
  coefficient extension is `E : Type u` with its `Field`, `Algebra (Padic B.l) E`,
  and `FiniteDimensional (Padic B.l) E` instances. Positive exponents are `n : ℕ`
  and `hn : 1 ≤ n`; no zero quotient is introduced.
- `S : SixFunctorOperationDatum D B E n hn` is the specified operation datum.
  `s : PodCoefficientStage` selects its finite, integral, rational, and common-stage
  categories and operations. These selectors retain finite etale-origin witnesses,
  derived completeness and finite reductions, raw localization, and common finite-field
  representatives through the published datum; no new coefficient construction is used.
- `X Y Z : SixFunctorSpace D` are finite-type schemes over D.k. Their structure maps
  are required separated. The f and g binders have `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` instances on their underlying maps. The same three composite
  instances are explicit binders as authorized by H2; they follow from composition
  of the corresponding instances for f and g and introduce no geometric restriction.
- The six admissibility assumptions are `_hf`, `_hg`, `_hx`, `_haX`, `_haY`, `_haZ`.
  They use `TensorHomCoefficientTransposes.Admissible` and `structureAdmissible`.
  The latter only installs the finite-type proofs already in `X.property`; it then
  uses that same published stagewise admissibility predicate for the structure map.
  Ambient admissibility is neither silently discharged nor asserted for all varieties.
- Compactifications `cf`, `cg`, `cx`, `cX`, `cY`, `cZ` present the specified operations
  and their admissibility predicates. They range over all compactifications.
- `Rf`, `Rg`, `Rx` are universally quantified restricted-domain presentations of S's
  actual operations. `_closedX`, `_closedY`, `_closedZ` identify the entire closed
  presentations on the common spaces; `_tensorX`, `_tensorY`, `_tensorZ` identify
  the corresponding tensor comparisons by `HEq`, allowing their dependent types.
  `_naturalX`, `_naturalY`, `_naturalZ` assert naturality in the tensor factor;
  naturality in the test variable is already built into each natural isomorphism.
  `TensorPresentationNatural` spells out that same comparison's remaining naturality
  equation using Mathlib's `MonoidalCategory.whiskerRight` and the recorded partial
  tensor's `map`. This is a predicate about the owning presentation, not a new tensor.
  `Domain` is the published `PodCtfAdjunctionData` interface: four actual restricted
  functors, their restricted adjunctions, and closed tensor presentations normalized
  to the recorded tensor and internal Hom. No new six-functor data are assumed.
- M, N, and T are objects of `(PodCoefficientStage.domain S s W).FullSubcategory`.
  This is the actual common constructible finite-Tor domain. The two representing
  objects are `PodHomChain.targetFunctor` and `PodHomChain.sourceFunctor`; their types
  place them in the same domain, so T may be either representing object itself.
- The displayed five bijections are `chain`, literally the inverse of the dependency's
  `PodHomChain.homEquiv`. That dependency runs ordinary adjunction, tensor-Hom,
  exceptional adjunction, projection precomposition, tensor-Hom in reverse order.
  Its projection is forward PF. Hence our forward chain uses precomposition with
  PF inverse, as required. `stageChain` writes the same five bijections directly in
  the dependency's right-factor tensor convention, with the canonical signed symmetry
  understood. In that convention `StageData.projection.hom` is inverse PF.
- `forward` applies that fixed chain to the identity test. `representing_chain`
  asserts both inverse equations against `homEquiv ... (𝟙 _)` and
  the formula on every test arrow. `exchange` packages exactly these two arrows.
  `chain_naturality` states test naturality and second-input naturality.
- `supportComposition` and `pullComposition` restrict the datum's recorded compositors
  through the fully faithful inclusions. `directComposition` and
  `exceptionalComposition` are their adjoint mates via `rightAdjointUniq`, so the
  pasted ordinary and exceptional counits fix the comparison maps.
- `sourceCoordinate` acts by exceptional conjugation in Hom's second variable, then
  ordinary direct-image composition. `targetCoordinate` acts contravariantly by the
  inverse compact-support compositor. `ChainComposition` asserts equality of the
  single and successive forward chains on EVERY input arrow in these coordinates.
  The main theorem asserts this proposition and `VerdierComposition` for EVERY
  presentation with shared closed/tensor data. It assumes neither equation nor
  projection pentagon, and no existential choice can absorb an erroneous scalar.
- `epsilon` specializes the representing arrow to omega_Y and postcomposes by
  direct-image Hom applied to the dualizing comparison. `dualizingComposition` is
  the exceptional compositor followed by f!c_g and c_f. `VerdierComposition` is
  epsilon_gf followed by the ordinary compositor equal to epsilon_g followed by
  Rg_* epsilon_f, with the contravariant support coordinate on the source.
  It is stated uniformly for supplied dualizing objects and comparisons, in
  particular for omega_W = Ra_W! Lambda and their structure-mate cocycles.
- `stageModel` reuses every field of `VerdierExchange.StageData` except its dualizing
  comparison. `stage_specialization` identifies its explicit chain with
  `TensorAdjunctionExchange.Model.inverseComponent`, identifies any normalized
  dependency conclusion's inverse exchange component, and gives the literal
  `StageData.epsilon` formula after specialization. Thus the statement is about
  the canonical exchange of the dependencies, not an unrelated isomorphism.
- `identity_exchange` quantifies over every R with `_closed : R.closedX = R.closedY`
  and `_tensor : HEq R.tensorX R.tensorY`, together with factor naturality `_natural`.
  It supplies only the canonical identity
  pullback unit, normalized by the recorded
  identity/self compositor. `identityDirect` is its ordinary adjoint mate;
  `identitySupport` uses proper coincidence; `identityExceptional` is the latter's
  exceptional mate. Its displayed equation is epsilon_id = identity in these unit
  coordinates, with contravariant support identification exposed on the right.
- `coefficient_transposes` lists the ordinary adjunction, tensor-Hom on X,
  exceptional adjunction, projection, and tensor-Hom on Y squares separately.
  Its final clause is the forward-chain square on every input arrow. The supplied
  `Comparison` is precisely the published evaluation- and unit/counit-normalized
  coefficient interface, not an arbitrary endpoint arrow. It covers the stated
  finite/integral changes and the field stages when their normalized restrictions
  are presented in these coordinates. It requires no extra perfectness hypothesis.
- `composition_after_change` states the coefficient image of the original successive
  chain equals the recalculated changed single chain in its composition coordinates,
  on every test arrow. Applying changed `ChainComposition` also identifies it with
  the successive changed chains. Together with the dualizing specialization this
  preserves the displayed Verdier composition equation. The published rational and
  common-stage coefficient theorems supply precisely these normalized maps on
  fractions and common representatives; no reduction of a field object is used.
- No arbitrary-pullback Verdier exchange, biduality, or new preservation assertion
  is included.

### Dependency declarations used

All six original statement dependency declarations and their docstrings were read:

- `Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`
  and its finite/integral/rational/common-stage tensor, Hom, and finite-Tor selectors.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`,
  `WeilConjectures.IsExceptionalAdjointAdmissibleAtFiniteStage`, and its integral,
  rational, and algebraically closed variants, via the published Admissible selector.
- `Sheaf.Paper.TensorAdjunctionExchange`,
  `WeilConjectures.TensorAdjunctionExchange.tensor_adjunction`, `Model`,
  `Model.inverseComponent`, and `Conclusion`. The definition interface is in
  `Sheaf.SixFunctors.TensorHomTranspositionData`, publicly imported there.
- `Sheaf.Paper.CompactSupportProjectionFormula`,
  `WeilConjectures.compactSupportProjectionFormula`, with its actual proper/open
  projection, composition, and pentagon laws.
- `Sheaf.Paper.AdmissibleVerdierExchange`,
  `WeilConjectures.AdmissibleVerdierExchange.verdier_exchange`, `Package`, and
  stagewise admissibility. Its canonical components are those of StageData below.
- `Sheaf.SixFunctors.VerdierExchangeData`,
  `WeilConjectures.VerdierExchange.StageData`, `StageData.epsilon`, and its
  tensor/Hom and adjunction fields.

The following already stated nodes are additionally cited in `stmt_deps`, because
public signatures or definitions now use their interfaces directly. They were
already proof dependencies of the item, or the owning definition of such an interface:

- `def-sf-tensor-hom-chain-data`: `Sheaf.Paper.PodHomChainCounitFormula`,
  `PodHomChain.homEquiv`, `sourceFunctor`, `targetFunctor`, together with the
  restricted functors/adjunctions of `PodCtfAdjunctionData`. The owning node now
  separates these definitions from the counit theorem. The reverse representative
  is the specified `homEquiv` evaluated on identity; no `curriedPairing` is used.
- `def-pod-ctf-pairing-maps`: `Sheaf.Paper.PodCtfPairingMaps`,
  `PodCtfPairing.homX` and `projection`, replacing the duplicates under PodHomChain.
- `def-sf-coefficient-gamma-representatives`: `Sheaf.Paper.CoefficientGammaRepresentatives`,
  `TensorHomCoefficientTransposes.Domain`, `Admissible`, `Comparison`, its
  evaluation-normalized maps, and the actual rational/common Gamma representatives.

The theorem nodes `lem-pod-hom-chain-counit-formula`,
`lem-sf-tensor-hom-coefficient-transposes` and
`lem-sf-constructible-exceptional-compositor` are not statement dependencies.
The latter two modules are no longer imported; their theorem interfaces are not
used by any signature. Composite geometric instances are bound explicitly.

Recorded, available proof modules are imported privately, including the ordinary
adjunctions, integral Hom reduction, integral finite extension, rational operations,
basic-operation reduction, finite Hom change and Hom-chain domain theorem.
The recorded proof module `Sheaf.Paper.ConstructibleExceptionalMateCocycles` is absent
both locally and from `scompile.py --source`; therefore it is not imported. Its
structure-mate cocycle is needed in the future proof, not to define the explicit
composite dualizing comparison or state this item. No duplicate of that theorem
is introduced here.

### Edge cases

The identity map is explicitly included, with proper identity compactification.
The coefficient interfaces include equal quotient levels, identity field embeddings,
and common-stage enlargement by equality. Empty schemes and zero objects impose
no nonemptiness hypotheses; identity tests exist for their zero representing objects.
Positive exponent one is included. Every integer shift remains governed by the
existing signed evaluations; no parity restriction or characteristic restriction
beyond the fixed unequal primes is added. Universes are explicitly bound, and
`autoImplicit` and `relaxedAutoImplicit` are false. Only the recorded small pro-etale
categories, with their original object/morphism universe convention, are used.

### Searches

- `msearch.py leansearch`: "The canonical tensor Hom exchange for compact support is
  compatible with composition and Verdier duality". Eight generic tensor/Hom hits,
  including rigid-category tensorLeftHomEquiv naturality; no exact six-functor result.
- `msearch.py leanfinder`: "The tensor Hom adjunction exchange for compact support
  direct image is compatible with composition and gives the Verdier duality
  composition law". Eight generic rigid/locally cartesian closed results; no match.
- Repair search: `rg` for tensorX/Y naturality in SixFunctorDatum, PodCtfAdjunctions,
  PodCtfPairingMaps, CoefficientGammaRepresentatives and WeilConjectures found no
  full-presentation factor naturality predicate. Generic tensor comparison
  naturality lemmas concern different categories/maps. `msearch.py loogle` query
  "CategoryTheory.NatIso, CategoryTheory.MonoidalCategory.whiskerRight" returned
  zero hits (NatIso unknown). The helper merely records the missing naturality
  clause of the same shared comparison using Mathlib's existing whiskerRight;
  it defines no new tensor, Hom, adjunction, or canonical arrow.
- `msearch.py loogle`: "CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.conjugateIso". No hits; conjugateIso is not the Mathlib name.
  Source reading identifies `conjugateIsoEquiv` and `Adjunction.rightAdjointUniq`,
  which are reused rather than restated.
- `msearch.py grep`: `verdier.*compos|homChain.*compos|HomChain.*compos`.
  No Mathlib match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the same patterns and
  `VerdierHom` found only unrelated dual-evaluation/trace-formula constructions.
  `grep -rn` for this item id in `lean/WeilConjectures` found none.
- The old CompactObject example module is withdrawn; its node now points to
  `WeilConjectures.CategoryTheory.CompactObject`. That current declaration and
  docstring were read to check namespace, signatures, and existing-interface practice.

No statement correction, new definition node, or dependency module is needed.
The node's statement and proof remain unchanged. The additional statement
dependencies are exactly the three landed definition owners listed above.

### Validation

All compiler probes and the delivered module were compiled only with `scompile.py`.
The final repaired module, including factor naturality, passes the sandbox (57.0 s)
and library module-name (34.7 s) compiles without warnings on 2026-10-25.
The delivery dry run passed preflight and per-file compilation (a076a219919).
The final delivery dry run checks this same module and all records on the server.

## Repair of returned delivery c6c1bd517ddd

H3: removed the existential Domain conclusions of both the main and identity
laws. The main law now quantifies over Rf, Rg and Rx; three equalities identify
closedX/closedY on X,Y,Z and three HEq hypotheses identify their dependent
natural tensor isomorphisms. These identify monoidal structure, evaluation and
symmetry as well as tensor comparison. Twisting Rx.tensorY alone by a unit
fails the shared-Z tensor hypothesis, so an existential scalar repair is impossible.
The independent reader found that mere sharing of the pointwise family still leaves
an object-dependent twist, since Domain stores naturality only in the test variable.
The final repair adds TensorPresentationNatural for the three shared families and
for the identity presentation. Its equation is the naturality square in the other
tensor variable. This is the natural comparison on one space required by the source;
it allows transport from Rx.support(M) to Rg.support(Rf.support(M)) through the
support compositor, and prevents an object-dependent unit twist from defeating it.
The identity law quantifies over R and requires its two closed and tensor fields
to agree. Its remaining existential is the normalized pullback unit p, whose
normalization and adjoint mates were accepted in the return.

H2: changed the statement edges and imports to the definition owners; replaced
curriedPairing by homEquiv on identity and PodHomChain.homX/projection by
PodCtfPairing.homX/projection. Composite IsSeparated/LFT/QC instances are explicit
binders instead of being obtained by importing the compositor theorem module.
The compile first detected duplicated composite binders in the main declaration;
these were removed before the final compile.

The sandbox was compared with the current main node: only stmt_deps and lean
are changed, and the natural-language statement and proof remain the current
main's verbatim values. deliver2 performs its normal current-main rebase.

Advisory: composition_after_change is a direct consequence of the last clause
of coefficient_transposes after substituting h. Its statement is retained to
spell out the preserved composition equation on every arrow.

## Independent second reading

Independent reader: `/root/independent_repair_reading`, a separate agent started
only to satisfy the returned H11 request. It read the full node, current blueprint
coherence proof, repaired module and the relevant closed/pairing/chain/coefficient
and StageData dependency interfaces. It found no remaining clause fault after the
following substantive correction from its reading.

The reader matched D, B, the finite-dimensional Padic extension and positive n to
the coefficient assumptions; S and its four selectors retain witnessed finite
origins, integral completeness/reductions, raw rational localization and common
coefficient stages. SixFunctorSpace and the separated/LFT/QC map binders give the
geometry; _hf/_hg/_hx/_haX/_haY/_haZ match all six admissibility hypotheses.
All compactifications present the specified operations.

It checked the H3 universal Rf/Rg/Rx binders and the three closed-data equalities
and tensor HEqs. These identify monoidal structure, evaluation and symmetry as
well as tensor comparisons on every repeated space. It then identified the
additional first-factor naturality defect of the pointwise tensor families.
TensorPresentationNatural and _naturalX/Y/Z, plus identity _natural, were added
and reread: inclusion(a ▷ T) followed by tensor_L equals tensor_K followed by
recordedTensor(inclusion(a)). This is needed for supportComposition.app M and
identitySupport. Hence independent and object-dependent unit twists cannot be
absorbed by the theorem. The identity R is likewise universal; only its normalized
pullback unit is existential, and all other unit coordinates are prescribed mates.

The reader matched the displayed five bijections to homEquiv.symm (therefore PF
inverse), forward to its identity test, representing_chain to both inverse laws
and every-arrow representation, and chain_naturality to the test/input squares.
All objects are in the full finite-Tor categories, so identity tests are valid.
It checked that support/pull composition are restrictions and direct/exceptional
composition their adjoint mates; ChainComposition consequently compares actual
chains on every arrow in pinned coordinates. epsilon, dualizingComposition and
VerdierComposition give the structure-map dualizing specialization and composite
formula; stage_specialization identifies the literal StageData.epsilon and the
normalized tensor-Hom exchange. The identity equation includes the contravariant
support and covariant direct-image unit coordinates.

For H2 it verified the new definition-owner edges, homEquiv/source/targetFunctor,
PodCtfPairing.homX/projection, identity-based inverse representative, the changed
CoefficientGammaRepresentatives import, removal of the compositor module and
explicit composite instance binders. For the final clause it matched all five
separate normalized coefficient squares and the resulting forward-chain square.
composition_after_change is the last coefficient square after substituting its
composition hypothesis, as the advisory says. The finite/integral/rational/common
interpretations retain the dependency's evaluation and unit/counit normalizations.
No arbitrary-pullback duality or hollow definition was found.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
