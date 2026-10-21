## Worker report

The module `lean/Sheaf/Paper/WeilInternalHom.lean` defines the ambient completed
rational internal-Hom bifunctor and its Frobenius
`WeilConjectures.wfInternalHomFrobenius`. The source is the current
main-20261015 blueprint, definition 2914 in
sec-algebraic-groups-lie-algebras/sk-p-cyclotomic, together with the full current
DAG statement. No mathematical statement correction is needed. All eight
new theorem obligations have `sorry` proofs; every definition has real data.

### Hypotheses and clauses

- `D : FiniteFieldDatum`, `c : D.CoefficientDatum` supply the finite base field,
  algebraic closure, coefficient prime and prime inequality.
  `X₀ : Over (Spec (CommRingCat.of D.k₀))` binds the base scheme;
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` express separated finite
  type. `D.geometricFiber X₀` is the specified X, including its projection.
- `E : Padic.FiniteCoefficientFields c.l c.Qbar` is the finite intermediate
  coefficient field. `pbcStageDatum` and `pbcStageUniformizer` reuse its actual
  valuation-ring datum and uniformizer, transported to the recorded small model.
  The datum supplies Noetherianity, torsion of the residue ring, and finiteness
  and perfectness of all positive quotients. `pbcAdicCompletion` is the actual
  completed coefficient sheaf B on the small pro-etale site.
- `WfIsComplete` is the recorded invertibility predicate for the intrinsic
  completion unit; `WfCompleteCategory` is its full subcategory.
  `WfAmbientRationalCategory` is its raw scalar localization, specialized by
  `WfAmbient` to the field E. This does not insert Karoubi completion.
- `wfOrdinaryDerivedHom` is exactly `derivedInternalHomOfUniverses`, computed
  by the fixed functorial K-injective replacement in the second argument
  among all module sheaves. `wfDerivedHom_complete` has arbitrary first
  argument and complete second argument. `wfIntegralHom` restricts that
  existing object and action; it does not complete the Hom object again.
- `wfRationalHomObj` retains the integral Hom object. The unique bilinear map
  of `wfRationalHomMap_exists` sends `(s tensor f,t tensor g)` to
  `(s*t) tensor H(f.op,g)`. Thus denominators varpi^r and varpi^s produce
  varpi^(r+s), in exactly the direction M,N to M',N' of the node.
  `wfRationalHom_laws` supplies the identity and composition obligations,
  and `wfRationalHom` is the resulting functor.
- The ordinary module transport is `pbcIsoModulePullback`; its derived
  transport is `pbcIsoAmbientPullback`. Preservation of complete objects
  is the existing `wfCompletePullback`, and rational transport is
  `wfAmbientRationalPullback`. They use the coefficient-limit identification
  that fixes the uniformizer, as stipulated in the node.
- `wfModuleTransportUnit` is the section function of the existing normalized
  adjunction unit. `wfModuleHomEvaluation` evaluates a Hom section at the
  identity object of its slice. Both are explicit definitions.
  `wfModuleHomTransport_exists` uniquely specifies the ordinary comparison
  by evaluation on these transported unit sections, for every M,N,U,phi,x.
  The ring in every sheaf Hom is explicitly `pbcAdicCompletion X d`.
- `wfHomComplexTransport_exists` specifies the transport comparison on every
  homogeneous degree and every Hom-product projection, using the published
  `coefficientHomComponent`. These projections characterize the chain map
  with the original signed Hom differential.
- `wfHomResolutionUnit` uses the same fixed functorial replacement as the
  recorded derived Hom. `wfHomResolutionMap_isIso` postpones the invertibility
  obligation for an already K-injective target. `wfHomKInjectiveModel` is the
  fixed localization comparison followed by the inverse of that actual
  localized augmentation; it is not an arbitrary model isomorphism.
- `wfDerivedHomTransport_exists` uniquely specifies alpha by its displayed
  square on every complex C and K-injective I, using that model comparison
  and the fixed Hom-complex transport. `wfIntegralHomTransport` restricts
  it, and `wfRationalHomTransport_exists` uniquely specifies its localized
  component on every pair of integral objects.
- `wfInternalHom` specializes the ambient functor to E. Its Frobenius is
  alpha followed by its action on the product isomorphism
  `(wfWeilStructure ... K).symm.op.prod (wfWeilStructure ... L)`.
  The first hom is phi_K inverse, contravariantly; the second is phi_L,
  covariantly. The result is an ambient isomorphism, with precisely the
  source and target of the node. No constructible-output conclusion is added.

### Recorded dependencies

The statements and recorded declarations of all nine original statement
prerequisites were read. The modules and interfaces used are:

- `Sheaf.Paper.PbcWeilCategory`: `WeilConjectures.WeilD`, its coefficient data
  and the specified completed Frobenius pullback.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum` and its actual
  finite quotient and completed coefficient sheaves, through the PBC API.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: intrinsic completion, through
  the published `WfIsComplete` interface.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization` and
  `ScalarLocalization.localization`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `WfIsComplete`,
  `WfCompleteCategory`, `wfCompletionReflector`.
- `Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete`:
  `isLocallyDerivedRingedIdealComplete_derivedInternalHom`.
- `Sheaf.Paper.PbcAutomorphismTransport`: `pbcIsoModulePullback`,
  `pbcIsoAmbientPullback`, and the canonical completed coefficient map.
- `Sheaf.CategoryTheory.RingedPresentationTransport`:
  `ringed_presentation_transport`, including K-injective preservation,
  local Hom transport and equivalence of local completeness tests.

The item additionally cites the already-landed `def-wf-tensor-product` and
`def-coef-hom-representative-evaluation`. Their interfaces supply the shared
ambient category/transport and the normalized fixed-resolution comparison,
respectively. The imported `QuasiIsoHomComplexMapOfUniverses` is a proof-only
import for `wfHomResolutionMap_isIso`, so its node is not a statement dependency.
No new definition node or dependency module is delivered.

### Searches and edge cases

Actual msearch.py searches, rerun on 2026-10-21:

- leanfinder: "Derived internal Hom of completed pro-etale Weil complexes with
  Frobenius by contravariant inverse and covariant action"; eight unrelated
  perfectoid, Witt-vector and etale-ring hits, no match.
- loogle: "CategoryTheory.MonoidalClosed"; twelve abstract closed-category
  hits, no construction in the completed rational coefficient category.
- grep, CategoryTheory: "internalHomFrobenius|WeilD|rational.*[Hh]om";
  zero hits.

The preserved earlier search log also records LeanSearch with "Derived
internal Hom Weil complexes Frobenius completed coefficient scalar
localization": eight localization, Ext and Frobenius hits, no exact match.
Source rg in Sheaf, WeilConjectures and dag/lean_names_upstream.json found no
new-name duplicate. The required node-id grep found the finite-etale
WeilComplexInternalHom/WeilComplexTensorHom modules. Their signatures were
read: they use finite-Tor etale coefficients, so they do not state this node's
completed pro-etale raw rationalization. No second notion is defined.
The example CompactObject module is currently withdrawn in the read clone.

Checks include zero objects, identity Frobenius, shifts, the empty scheme,
unbounded complexes, and an empty generator list in the general integral
construction. On rank-one scalar Frobenii lambda and mu the displayed action
is mu/lambda. Site objects have universe u+1, site arrows u, coefficients
u+1 and derived Hom arrows u+2; no extra equality of universes is imposed.
There is no STATEMENT-DISPUTED claim.

## Repair of returned delivery

Return: independent stage-2 review of immutable head `7d88d09401f7`,
2026-10-21, points F1 (H2) and F2 (H13).

- F1: removed `lem-weil-integral-scalar-extension-well-defined` and
  `lem-pur-rhom-well-defined-universes` from the item's `stmt_deps`.
  No declaration from either is used in the item's signatures or definitions.
  The latter supports only the postponed resolution-map proof. Retained
  `def-wf-tensor-product` and `def-coef-hom-representative-evaluation`.
- F2: removed the sandbox `IntegralScalarExtensionWellDefined.lean` and
  its dependency node copy from the packet. The published module and NC's
  record remain the dependencies used by compilation. The earlier report's
  claim that the live scalar-action proof required replacement was incorrect;
  it does not justify replacing seven landed proofs with `sorry`.

The item module is unchanged from the returned packet. SHA-256:
`cf9189aad965d66d1256d58259bf69e3805df2f6997e98f3a87e2562da07cbd5`.
Comparison with the current shared node shows only the item's `lean` field
and the two retained additions to `stmt_deps` differ. The mathematical
statement, all other node fields, and every dependency node are unchanged.

## Validation

All compiles use the prescribed scompile.py/deliver2.py wrappers and the
unchanged 60-second per-file limit. The saved packet's initial dry run was
started before repairs, as requested. Its preliminary item check timed out;
the run then failed when it reread the dependency module I had removed before
it finished. A fresh item-only scompile run compiled the sandbox form in
48.8 seconds; its library form and server confirmation timed out at 60 seconds
without reporting a Lean elaboration error. The corrected packet contains
only the item module, item node and this report. Subsequent validation uses
that complete corrected packet, without edits while a wrapper is running.
The required self-check passed: unchanged module hash, exact recorded
signature, the two retained statement-dependency additions only, one module
and one node, no #check commands, explicit binders and lines at most 100 columns.
No direct Git command, live-source edit, launcher-script edit or global
build was performed.

## Second reading by Q43

I reread the order-2914 blueprint formula, the full current node and both
modules. Each hypothesis and clause is matched above. The comparison alpha
is determined by actual local evaluation, all Hom-product projections,
every K-injective representative and the localized integral components.
The inverse is on the first variable, and `Iso.op` reverses its direction
as required. The ambient categories and Weil carriers are exactly the
published shared ones. The finite-etale alternative does not match them.
The edge cases and the independent site universes remain included.
On this repair I reread the complete item and current blueprint and checked
both return points against the packet. The resolution theorem remains a
proof obligation, while the derived Hom definition reuses the published
construction. There are no dependency modules in the corrected packet and
no published proof bodies or dependency records are changed. The item Lean
remains byte-for-byte unchanged. The dry run and push use deliver2.py.
