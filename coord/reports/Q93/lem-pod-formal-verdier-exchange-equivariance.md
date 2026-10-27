## Worker report

The module `Sheaf.Paper.FormalVerdierExchangeEquivariance` states
`WeilConjectures.FormalVerdierExchange.formal_verdier_exchange_equivariance`, with one
postponed proof. Every definition has real data. The node's statement is unchanged.

The source read is the current `literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md`, the sentence on formal duality exchange.
I also read the current `fix-lem-tensor-adjunction.md` and `fix-cor-verdier-exchange.md`.
The old path in the node has moved in the latest blueprint; its evaluation/adjunction
construction is retained by the current source. The resolved stage-1 repair note was read;
the accepted split and proof are preserved.

Hypothesis and clause correspondence:

- The finite-field data, prime p, positive exponent a, q, base field and algebraic closure
  are the recorded `FiniteFieldDatum`; l and `[Fact l.Prime]`, with `hl : l ≠ D.p`, give
  precisely the distinct coefficient prime. `Ω` has the recorded algebraic-closure structure.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` and their locally-finite-type, quasi-compact, separated
  instances give the separated finite-type models. The same three instances on `f₀.left`
  give the separated finite-type morphism. Its actual geometric pullback is retained in
  `_pullback` via `VerdierPairing.geometricPullback`.
- `E : Option (FieldStage l)` and `_embedding` represent an arbitrary finite extension
  inside Ω, or Ω itself (`none`). `SX` and `SY` are the existing full Frobenius-stable
  domains inside the actual rational/common-stage categories. Their `phi` is restriction
  of actual geometric Frobenius pullback, and `IsoAlgebra` is the existing Weil-pair category.
- The first two conjuncts `CoefVerdierWeil.Conclusion ... X₀` and `... Y₀` supply the
  contravariant dual lifts, actual evaluation and biduality, omega and dual scalar
  isomorphisms for all finite extensions (including identity extensions), their diagrams,
  and stage-inclusion compatibility. This reuses the complete published assertion rather
  than a private copy of coefficient duality. Its `Coefficients.finite/common/scalar/stage`
  fields were read, including `Duality`, `DualityComparison` and exceptional comparisons.
- The formal part is universally quantified over supplied lifted operations and their
  domain data. `Data.exceptional`, `.ordinary`, `.structureY`, `.structureX` are exactly
  F ⊣ G, P ⊣ Q, H ⊣ J, U ⊣ R, with the original units and counits pinned by the recorded
  `LiftedAdjunction`. In a geometric application H,J belong to a_Y and U,R to a_X.
  `Data.Z` is the supplied coefficient-unit Weil pair. The formal assertion is uniform
  in the supplied base category and this object, as allowed by the node's last paragraph.
- `Data.omegaY` is J(Z) and `Data.omegaX` is R(Z). `Data.compositionMate` is precisely
  `VerdierExchange.composition ... compositor` evaluated at Z: conjugation of the inverse
  compact-support compositor under the pasted adjunctions. It is never an arbitrary c.
  `Assertion` includes its full unit-map-counit formula at every base object, as well as
  its Weil square. `compositor_equivariant` is the assumed equivariance of composition.
- `x` and `y`, with the recorded `Realizes` predicates, restrict the actual tensor and
  partial internal Hom. `_tensorX` and `_tensorY` identify these with the published
  projection data. `source` uses the recorded `imageDual` to set A = D_Y(FM).
  `tensorSource` uses the recorded V = M tensor P(A). Evaluation is in the specified
  FM tensor A order; reversing a convention is handled in supplied tensor identification.
- `Projection.iso` is the displayed invertible projection component, pinned by
  `Projection.component` to `ExchangeProjectionStage.projection`. Projection has no
  equivariance field. `ProjectionLifts` supplies the primitive proper adjunction, tensor
  pullback, open projection and support-identification Weil lifts; the first projection
  clause of `Assertion` derives the assembled PF square. `pairing` is exactly inverse
  projection followed by evaluation.
- `exceptionalTranspose` is eta! followed by G(b). `threeTransposes` then applies the
  tensor--Hom unit and H_M to t, and the ordinary unit and Q to the result. The supplied
  tensor adjunction has its underlying unit and counit fixed explicitly.
- `formalMap` postcomposes that exact s with Q Hom(M,c). `target` is Q(D_X M).
  `Assertion` gives the Weil equation for this map and its equality with the same
  construction where c is substituted before the final two transposes. Thus it does
  not assert equivariance of an unrelated exchange isomorphism.
- `Normalizes` spells out the entire natural Hom chain defining the canonical internal
  adjunction comparison I of fix-lem-tensor-adjunction: inverse ordinary, inverse tensor,
  inverse exceptional transposition, precomposition with the actual projection, then
  tensor transposition on Y. Explicit `eqToHom` transports use the two supplied tensor
  equalities; there is no hidden changed projection map.
- When this canonical I is available (under the named admissibility and finite-Tor
  hypotheses of the dependencies), `Assertion` gives s = I.inv, formalMap = Q Hom(M,c)
  after I.inv, invertibility, and the explicit inverse Weil equation. Availability of I
  is not required for the preceding formal equivariance. This is precisely the distinction
  between the unconditional formal construction and its conditional isomorphism clause;
  the module does not add exceptional admissibility to operation lifting.
- No invariant lattice, integral inverse, or ambient exceptional right adjoint is used.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`,
  through the recorded Frobenius of the pairing dependency.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the rational/common tensor, Hom, pullback and
  permitted-pair declarations, through `VerdierPairing.Realizes` and `geometricPullback`.
- `Sheaf.Paper.SfWeilSheafComplex`: actual rational/common Frobenius and Weil complexes.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `FieldStage` and actual
  coefficient categories. The morphism-properties dependency is a convention node:
  the Mathlib `Over`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` are used directly.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage`, `.projection`.
- Mathlib `CategoryTheory.mateEquiv` and `conjugateIsoEquiv`, used by the existing
  `VerdierExchange.composition`, with the recorded unit/counit orientation.
- `Sheaf.Paper.VerdierPairingThreeTransposes`: `Domain`, `Domain.phi`, `TensorHomData`,
  `ClosedData`, `LiftedAdjunction`, `Realizes`, `geometricPullback`, `imageDual`,
  `tensorSource`; `verdier_pairing_three_transposes` is the planned proof tool.
- `Sheaf.Paper.VerdierExchange`: `VerdierExchange.composition`. Its definition owner
  `def-sf-verdier-exchange-data` is added to the statement dependencies.
- `Sheaf.SixFunctors.CoefVerdierWeilEquivariance`: `CoefVerdierWeil.Conclusion`,
  `coef_verdier_weil_equivariance`. The plain predicate is owned by the new definition
  node `def-pod-verdier-weil-conclusion`; the corollary remains only a proof dependency.
  The used pairing definitions are owned by `def-pod-verdier-pairing-domain-data`;
  the three-transpose theorem remains only a proof dependency.
- Proof imports are `Sheaf.Paper.ConstructibleMateCoherence`,
  `Sheaf.Paper.TensorAdjunctionExchange`, and `Sheaf.Paper.AdmissibleVerdierExchange`.
  I read `PodConstructibleMate.adjunction_coherent`, `TensorAdjunctionExchange.tensor_adjunction`
  and its Package, and `AdmissibleVerdierExchange.verdier_exchange` and Assertion.
  `lem-pod-verdier-composition-mate-normalization` has no recorded Lean declaration in
  the current read tree; it is a proof dependency only, so there is no nonexistent import.
  The map and its normalization needed for this statement are explicit here.

Edge cases checked before writing and during the second pass:
identity f and identity coefficient extensions; zero M; empty X or Y; a = 1;
finite E and the `none` common-stage choice; rational Frobenius equal to a uniformizer
at a point (the inverse remains a rational inverse); non-semisimple Frobenius.
The Hom chain has the correct variance and its order sends s to the identity.
No dimension, smoothness, properness, lattice, or global exceptional-adjoint hypothesis
is introduced. Isomorphism assertions occur only under the normalized I binder.
No statement dispute or statement correction.

Searches (all via the prescribed launcher search or read-only rg):

- leanfinder: `Verdier exchange equivariance via projection formula evaluation and three
  adjunction transposes`: 8 hits, including expComparison, coev_expComparison, mateEquiv
  and iterated_mateEquiv_conjugateEquiv; general categorical infrastructure, no exact match.
- loogle: `CategoryTheory.Adjunction, CategoryTheory.mateEquiv`: 12 mate correspondence
  and pasting hits; infrastructure, not the node's geometric/coefficient assertion.
- grep tool: `verdierExchange|verdier_exchange|IsoAlgebra` in CategoryTheory: 0 hits.
- leansearch: `Frobenius equivariance of Verdier duality exchange defined by transposing
  projection and evaluation`: 8 hits (isocrystal equivariance, linear transposes and
  frobeniusMorphism), no exact match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for Verdier exchange and the node id:
  upstream `PoincareDuality/Verdier.lean` has the opposite internal-adjunction map;
  `WeilSheaf/VerdierDual.lean` has an unnormalized Nonempty exchange on a native category.
  Neither supplies this node's actual rational/common-stage formal-map Weil equation.
  Project `VerdierExchange` owns the construction and `VerdierPairingThreeTransposes`
  owns the preliminary calculation; both are reused. No exact theorem was found.
- rg of Mathlib and both project roots found no declaration or namespace collision with
  `WeilConjectures.FormalVerdierExchange` or `formal_verdier_exchange_equivariance`.

Validation: prescribed scompile.py compiled both sandbox and actual library-module forms
cleanly (no errors or non-sorry warnings). One initial elaboration mismatch in the Hom
chain was repaired by explicit tensor endpoint transports, then the same wrapper passed.

## Second reading by Q93

This is an in-session second reading, not an independent agent review: the dispatcher
explicitly prohibits starting other agents and assigns independent review to the maintainer.
I reopened the node and delivered source after compilation and checked the correspondence
above. The formula for c is conjugation of the inverse compositor; its counit is H(epsilon_F)
then epsilon_H, matching the pasted adjunction. The three transposes have domains V, PA,
and A respectively. Hom is covariant in c and Q is applied after Hom. The final square uses
source.str followed by the map, and Frobenius(map) followed by target.str; the inverse square
reverses those endpoints. The supplied projection is pinned by HEq, with explicit tensor
transports in the normalized Hom chain. The duality/scalar clauses reuse the full existing
Conclusion instead of dropping diagrams. The natural-language item is unchanged.
Two new definition ownership nodes (existing declarations, no copied modules) are supplied
in this repair; no dependency module is changed.


## Returned-delivery repair

The returned immutable head is `7ca50a7fa9f8`. Its sandbox node had the same original
statement and proof as current main, plus its Lean record and three added dependencies.
I compared those fields with current main and rebuilt the sandbox node from current main,
retaining only the corrected Lean record and authorized statement-dependency additions.
The prescribed delivery wrapper performs the repository rebase and delivery bookkeeping;
no direct Git commands or edits in the read-only clone were used.

H2: The two theorem nodes added to stmt_deps in that head were wrong ownership. I removed
`lem-pod-verdier-pairing-three-transposes` and `cor-coef-verdier-weil-equivariance` from the
item's statement dependencies; both remain in proof_deps unchanged. The two new definition
nodes below own exactly the published plain definitions used by the item. Their Lean
records are existing:true on unchanged modules, as the return explicitly permits. Nothing
is copied or restated in Lean, and no theorem conclusion is used to state either definition.
`def-sf-verdier-exchange-data` remains the already-landed owner of composition.

H3: I removed `Projection.equivariant` entirely, retaining only the inverse-isomorphism
data and HEq with the published PF component. The theorem now takes `ProjectionLifts`:

- `proper` is a lifted adjunction for exactly d.properPull and d.properPush, with
  `properAdjunction` identifying its adjunction with d.properAdjunction, hence the
  underlying unit and counit are fixed, not independently chosen.
- `bar` gives the tensor lift on the intermediate compactification domain, with
  `tensorBar` identifying its tensor with d.tensorBar.
- `tensorPullback` is an actual isomorphism of Weil pairs whose underlying arrow is pinned
  by `tensorPullback_hom` to d.tensorPullback. Thus the primitive tensor comparison, not
  its assembled projection mate, is supplied as equivariant.
- `openProjection` is an isomorphism of Weil pairs pinned by `openProjection_hom` to
  d.openProjection; its pullback structure is exactly k.ordinary.leftComparison.
- `supportIdentification` identifies the exceptional left lift with open extension followed
  by the proper right lift, and its forward and inverse underlying arrows are pinned to
  d.compactSupportIdentification.

These are exactly the primitive lifted operations, units/counits and canonical comparisons
assumed by the node's supplied-data clause. Arbitrary incompatible lifts no longer satisfy
the hypotheses: the normalization fields constrain each primitive comparison at every pair
of Weil inputs. No field asks for a Weil lift of PF or assumes its equivariance. Assertion
now concludes the full PF square before the formal-map square. To obtain it, tensor the
proper counit with identity after the supplied tensorPullback, transpose through the proper
lifted adjunction, then apply the open extension and the proper image of openProjection,
and conjugate by supportIdentification. After forgetting, the unit/counit and underlying
comparison normalizations identify the composite with the existing
compactificationProjectionFromData and hence ExchangeProjectionStage.projection. This is
exactly the mate-coherence proof Step 2 called for; it also covers arbitrary supplied
closed domains, since every primitive operation used is part of the supplied data.

The formal-map formulas and conditional normalization are unchanged. No theorem is proved:
the single sorry now states both derived PF equivariance and the ensuing formal exchange
conclusions. Edge cases were rechecked: zero input and empty domains require no extra
nonemptiness assumption; identity morphism and identity coefficient extension keep all
normalizations; the none-stage uses the same primitive map equations. In particular this
repair adds no ambient exceptional-adjoint assumption and no integral lattice.

## New nodes

`def-pod-verdier-pairing-domain-data` owns the existing `Domain`, `Domain.C`, `Domain.phi`,
`TensorHomData`, `TensorHomData.weilTensor`, `TensorHomData.weilHom`, `ClosedData`,
`LiftedAdjunction`, `Realizes`, `geometricPullback`, `imageDual`, `tensorSource` of
Sheaf.Paper.VerdierPairingThreeTransposes. These are precisely the plain interfaces used
by the consumer. Its source is the latest prop-weil-operations formal-exchange sentence
with the existing rational/common coefficient and Weil-pair conventions. The node defines
full stable domains, normalized tensor/Hom and lifted adjunction data, and the two source
objects. It asserts no three-transpose theorem. DAG exact-name searches found only the
statement node, no definition owner; blueprint_refs.py search 'Verdier pairing' found no
blueprint node. The LeanSearch query 'Frobenius stable domain with tensor Hom and lifted
adjunctions for Verdier duality' returned 8 generic Frobenius/Hom adjunction hits; Loogle
'CategoryTheory.Endofunctor.IsoAlgebra, CategoryTheory.Adjunction' had 0 hits (unknown
project identifier); msearch grep 'VerdierPairing|CoefVerdierWeil|ProjectionLifts' in
CategoryTheory had 0 hits. Direct rg found the project declarations and no upstream or
Mathlib alternative. The node reuses these exact declarations rather than defining copies.

`def-pod-verdier-weil-conclusion` owns exactly `CoefVerdierWeil.Conclusion` of
Sheaf.SixFunctors.CoefVerdierWeilEquivariance. Its proposition packages the actual
finite/common duality and internal-Hom/dualizing identifications, Weil structures with
evaluation/biduality/scalar/inclusion diagrams and exceptional adjunction diagrams. It
does not assert existence: it defines the predicate that the theorem proves. Its source
is the same formal duality exchange sentence and the cited common-stage duality data.
DAG exact-name searches found only cor-coef-verdier-weil-equivariance, and blueprint_refs.py
search 'Weil duality' returned 0 nodes. The same three Mathlib searches listed above did
not supply this predicate; direct rg found the exact project definition which is reused.

Both nodes have existing:true records and no new Lean module. Each has the required
search metadata, source, import_flags, creation and ancestor metadata. The item's
statement dependencies cite them directly; the theorem nodes remain proof dependencies.


Repair second reading: I rechecked the returned H2 list against the two new
lean.declarations lists: all twelve listed VerdierPairing interfaces and the one
CoefVerdierWeil.Conclusion predicate are owned; neither theorem is included. The new
nodes' dependency lists equal their bracket citations. The existing modules are unchanged.
For H3 I reopened ExchangeProjectionSuppliedDomains and the upstream Adjunction/ProjectionMap
implementation: proper projection is exactly the adjunction homEquiv of tensorPullback
followed by tensor of the counit. This is the composite modeled by ProjectionLifts;
its supportIdentification endpoints use open then proper image in that order. Each
primitive has a Weil arrow and an underlying-map normalization. Projection has only iso
and component fields. Assertion's new first per-object conjunct concludes the missing
PF equivariance square. I checked that no new premise depends on the assembled projection
or on the formal map, so the repair does not merely rename the rejected assumption.
The remaining comparison-mate, three-transpose, and inverse equations are unchanged.

Repair validation: scompile.py compiled the repaired sandbox and library module successfully,
with no errors or warnings (the postponed named theorem remains the single sorry).
