## Worker report

Delivered module: `Sheaf.Paper.VerdierCompositionMateNormalization`.
Namespace: `WeilConjectures.VerdierCompositionMate`.
The main declaration is `verdier_composition_mate_normalization`; the node's
`lean.declarations` lists its construction helpers and the four other named
statement clauses. Every theorem proof is `sorry`; every definition has real data.
No source statement correction, new node, or dependency-record repair is needed.

Read the full item, its statement/proof dependencies and their records, the
stage-2 brief, stage document and delivery-errors H. The nominal CompactObject
example is now a withdrawn module; its node record and the current module-mode
conventions were read. There is no repair note for this item.

Sources actually read are the current blueprint under `literature/blueprint/latest`:
`sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.proof.md`, the formal
exchange sentence; `sec-six-functors/sk-thm-sf-package/fix-cor-verdier-exchange.proof.md`,
Steps 1--2; and `fix-lem-tensor-adjunction.proof.md`, Step 1. The item's historical
source path says sk-lem-finite, but the current source is sk-thm-frobenius. Its
mathematical construction and orientation agree with the item.

Hypotheses and clauses, including the separate named clauses of the same DAG node:

| Node text | Lean rendering |
| --- | --- |
| p prime, a positive, q=p^a, finite base and fixed algebraic closure | `D : FiniteFieldDatum`; its fields retain these conditions. |
| l prime, l different from p, chosen algebraic closure of Q_l | `l`, `[Fact l.Prime]`, `hl`, `Ω`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]`. |
| Rational finite E in Ω, or common-stage algebraically closed coefficients | `E : Option (FieldStage l)` and `_embedding`; `some` selects the rational category and `none` the common-stage category. `FieldStage` contains the finite-dimensional extension. |
| Separated finite-type k0-schemes and separated finite-type f0 | `X₀ Y₀ : Over (Spec (.of D.k₀))`, their `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` instances, and the analogous instances on `f₀.left`. |
| Actual geometric fibers and geometric Frobenius pullback | `SX`, `SY : VerdierPairing.Domain ...`; `.C` is a full subcategory of the recorded geometric-fiber category and `.phi` is the restriction of the actual recorded pullback. No new Frobenius is defined. |
| Supplied domains only, containing every displayed composite | `Domain.objects`, `Domain.stable`, the supplied functors and their displayed endpoints. No ambient exceptional right adjoint is postulated. |
| F,G,P,Q and tensor/Hom, with their canonical Weil lifts | `d.compactSupport`, `G`, `d.pull`, `Q`, `x`, `y`, `e`, `o`. `Realizes` retains the actual tensor/partial-Hom identifications; `_pullback` retains actual geometric pullback. `_tensorX`/`_tensorY` identify the projection's tensors. `LiftedAdjunction` retains underlying unit/counit equations. |
| H,J,U,W and compositor alpha | `h`, `j`, `alpha`, `alphaW`, `_alpha_eq`. `alphaW` is the supplied equivariant compositor with its underlying map fixed to `alpha`. |
| Pasted counit and specified c_Z formula | First two conjuncts of `composition_mate`; `VerdierExchange.composition` is reused, not a new dualizing identification. |
| c_Z is an isomorphism and a Weil arrow, for every Weil Z | `weilComposition` is a natural isomorphism on the existing `IsoAlgebra` categories; `composition_mate` identifies its underlying component with the existing composition isomorphism. Taking `Z` to be the coefficient unit gives exactly c:G omega_Y ≅ omega_X. No second c is chosen. |
| omega_Y=J Lambda_s, omega_X=W Lambda_s | In the main formula these are `J.obj Z.carrier` and `W.obj Z.carrier`. The statement is uniform in Z, as required by the node before its unit specialization. |
| M Weil, A=D_Y FM, V=M tensor PA | `M : IsoAlgebra SX.phi`; A is the repeated explicit term `(y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)`; V is `(x.tensor.obj M.carrier).obj (d.pull.obj A)`. No opaque let binder. |
| Invertible canonical projection at A | `pi` and `_pi_eq`, using the actual `(d.projection.app M.carrier).app A`. Invertibility of projection at other test objects is not imposed for the unconditional assertion. |
| b=eval after pi inverse and exceptional transpose t | `exceptionalTranspose` applies `e.adj.homEquiv` to `pi.inv ≫ ay.counit.app ...`. `ay` is precisely the tensor/Hom adjunction at FM, so its counit is evaluation. |
| Only the required tensor/Hom adjunction at M | `ax : x.tensor.obj M.carrier ⊣ x.hom.obj (op M.carrier)`. No closed structure at every object of X is imposed. |
| Tensor transpose then ordinary transpose | `lastTransposes` applies `ax.homEquiv` and then `o.adj.homEquiv`; `preExchange` applies these to t. |
| Substituting c commutes with those transposes | `substitution`, and the first main conjunct for the actual composition mate. Lean uses forward composition `s ≫ Q.map(H_M.map c)`, the same mathematical order as QH_M(c) composed after s. |
| Substitution map is Weil | `substitution_weil`: the exact fixed-pair arrow equation for `Q.map ((x.hom.obj (op M.carrier)).map c.hom.f)`, for any supplied Weil c, hence for `weilComposition.app Z`. |
| Right side is precisely canonical epsilon_M | `exchangeComponent` is the prescribed substitute-before-transposition recipe. `stage_epsilon` additionally states equality using the existing `StageData.epsilon`, `Model.inverseComponent` and the existing `StageConclusion.components` convention, with the stage interface's recorded right-tensor ordering. `stageTensorModel` only repackages those same fields. |
| Additional admissibility/finite-Tor hypotheses only for I and final inverse formulas | The final main conjunct quantifies the supplied isomorphism `I` with exactly the stipulated Hom-chain normalization. It asserts no existence of I on an unrestricted supplied domain. Its source is the isomorphism of `fix-lem-tensor-adjunction`, applicable under the additional admissibility/finite-Tor hypotheses in the item. At field coefficients the recorded finite-Tor domain equals the whole bounded constructible domain. |
| Normalization for every B and every u | The final conjunct's `piAll`, `_piAll_eq`, and `∀ A u'` equality `u' ≫ I.hom = internalHomChain ...` retain all five steps: inverse ordinary transpose, inverse tensor transpose, inverse exceptional transpose, precomposition with canonical projection, tensor transpose on Y. piAll maps are constrained by HEq to the recorded projection; they are not arbitrary maps. |
| s is invertible, s=I inverse, epsilon=QH_M(c) I inverse | The final three conjuncts are `IsIso (preExchange ...)`, `preExchange ... = I.inv`, and `exchangeComponent ... = I.inv ≫ Q.map (...)`. |
| Stage conclusion has that component | Last clause of `stage_epsilon`, quantified over the recorded `VerdierExchange.StageConclusion`. |

The normalized-I clause is intentionally conditional: the mathematical node says
“let I be ... in the following normalization,” not that an ambient exceptional
right adjoint or an internal-adjunction isomorphism exists on every supplied domain.
The imported `TensorAdjunctionExchange.tensor_adjunction` and
`AdmissibleVerdierExchange.verdier_exchange` are the already stated existence
results on the additional admissible domains. The present result fixes their
component, rather than restating or assuming their all-coefficient packages.

Dependency interfaces read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum` and geometric fiber.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: rational/common-stage pullback, tensor and permitted-pair internal Hom, through the recorded realization interface.
- `Sheaf.Paper.SfWeilSheafComplex`: the actual rational and common-stage Frobenius functors and the `IsoAlgebra` fixed-pair convention.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `C`, `Stage`, `FieldStage`, `Operation`, and `System`; no ambient adjoint assumption.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage`, `.projection`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateEquiv`, `conjugateIsoEquiv`; `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `comp_counit_app`, `homEquiv_naturality_right`.
- `Sheaf.SixFunctors.VerdierExchangeData`: `composition`, `StageData`, `.epsilon`, `StageConclusion`.
- `Sheaf.SixFunctors.TensorHomTranspositionData`: `Model`, `.inverseComponent`, `Conclusion`, owned by the directly cited `def-sf-tensor-hom-transposition-data`. `Sheaf.Paper.TensorAdjunctionExchange.tensor_adjunction` is a proof dependency, imported without public visibility.
- `Sheaf.Paper.AdmissibleVerdierExchange`: `atStage`, `admissible`, `Package`, `verdier_exchange`; proof import for the admissible existence conclusion.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and its `FiniteTorAmplitude` import: field finite-Tor convention, notably `finiteTorFieldCoefficientCategory`.
- Landed `Sheaf.Paper.VerdierPairingThreeTransposes`: `CategoryAt`, `Domain`, `.C`, `.phi`, `TensorHomData`, `LiftedAdjunction`, `Realizes`, `geometricPullback`. Its landed definition owner `def-pod-verdier-pairing-domain-data` is cited in stmt_deps for these shared definitions; the three-transposes theorem is not used or cited as a statement dependency. No definition is copied.

Edge cases checked before writing: the zero object and empty scheme require no
nonemptiness or dimension assumption; identity functors/compositors give the identity
mate; arbitrary Z remains allowed before taking the coefficient unit; `none` and
`some E` cover both coefficient cases; no pi invertibility is assumed at other B
before the conditional I clause; no admissibility or finite-Tor hypothesis is
silently imposed on the mate/substitution clauses. Object and morphism universes
for the generic mate lemmas are independent. Every universe/binder is explicit.

Searches actually run with msearch.py (2026-10-25):

- LeanFinder: “The mate of compact support composition identifies dualizing objects and substitution commutes with tensor Hom adjunction transposes to identify canonical Verdier exchange”. Eight results, including `tensorLeftHomEquiv`, `tensorRightHomEquiv`, and rigid-category mate composition/evaluation lemmas. Generic infrastructure, no exact sheaf-domain normalization statement.
- Loogle: `"conjugateIsoEquiv"`. Ten results; the generic `CategoryTheory.conjugateIsoEquiv` and its hom/inverse component lemmas supply the mate construction, already reused by `VerdierExchange.composition`; none states this entire node.
- LeanSearch: “Verdier exchange is the inverse internal adjunction followed by substitution of the dualizing composition mate”. Eight results, including `Adjunction.op`, `frobeniusMorphism_mate`, and `mateEquiv`. No exact match.
- msearch grep: `homEquiv_naturality_right|conjugateEquiv_apply_app` in `CategoryTheory/Adjunction`. Seventeen hits, including Basic.lean:238 and Mates.lean's conjugation infrastructure. Read the full relevant signatures and docstrings.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id, `composition_mate_normalization`, `CompositionMateNormalization`, `transpose.*substitut`, and conjugation names. No existing theorem for the full statement. The searches located `VerdierExchange.composition`, `VerdierPairingThreeTransposes`, and `WeilChosenDualityExchange`; the latter fixes a different chosen-adjoint exchange and supplies no inverse-I normalization. These existing notions are reused where applicable.

The final module compiled cleanly through scompile.py in both sandbox and library
module modes (23.2 s and 11.1 s). Earlier probes found one unused binder and one
overlong line; both were corrected before the clean compile.

## Second reading by N5

Author's separate second pass, not an independent-agent review (the dispatcher
explicitly forbids starting other agents; the maintainer supplies independent review).
I reopened the file and node and checked the table above against the actual binders.
The first draft required a closed structure at every X object and projection
isomorphisms at all test objects before the unconditional conclusion. I removed
both restrictions: only ax at M and ay at FM remain, and piAll occurs inside the
conditional normalized-I clause and consists of maps, not isomorphisms.
The mate orientation is alpha inverse, with source GJ and target W. The tensor
and ordinary transpose order agrees with the source. The I-normalization uses
u followed by I.hom and the chain is read from QH_M(G omega) to D_YFM, so the
conclusion is I.inv, not I.hom. The existing stage epsilon clause uses the
published right-tensor convention and projection normalization, rather than
silently swapping the tensor factors. No mathematical change to the node was made.


## Repair of returned head 9cdf0ea7967a

H2 repaired: replaced the statement dependency
`lem-pod-verdier-pairing-three-transposes` with its landed definition owner
`def-pod-verdier-pairing-domain-data` (Q93, 919a934). Read that node's statement,
existing:true Lean record and the shared module: Domain/.C/.phi/.objects,
TensorHomData/.weilHom, LiftedAdjunction, Realizes and geometricPullback are exactly
the definitions used here. The three-transposes theorem's conclusion is not used.
Updated lean.note and the ownership explanations above. Also cited the landed
`def-sf-tensor-hom-transposition-data` directly for TensorAdjunctionExchange.Model
and inverseComponent, as identified in the return's advisory.

Compared the retained packet to current main: the item has no landed Lean record,
and the module is absent both locally and from scompile.py --source. Thus Q63 has
not superseded this delivery at the time of repair. All fields outside lean and
stmt_deps match main. Rebased the node copy on that current main record. The Lean
file is retained byte-identically to the returned sandbox version, SHA256
ed538ba15ca8f5d3ffa56a942d14d3e738139896336e170608af4cdc9d66b32e. No mathematical statement, proof, definition, or import changed.
The maintainer's return independently accepted the mathematics; this repair changes
only definition ownership in the DAG and its documentation. Compilation, dry run,
and delivery are rerun through the prescribed wrappers.
