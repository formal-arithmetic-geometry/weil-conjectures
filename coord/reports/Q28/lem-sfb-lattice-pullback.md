## Worker report

The module `Sheaf.Paper.LatticePullback` states
`AlgebraicGeometry.ProEtale.lattice_pullback`. Its only theorem proof is `sorry`.
The two helper definitions contain actual data: the existing module-sheafification unit
applied to `1 ⊗ m`, and inverse image of a section followed by that insertion.
No canonical object is chosen from a bare existence statement.

Source checked: the current main-20261015 blueprint proof of
`sk-lem-stratified-lattice`, especially “Pushing down by the trace”, where the universal
lattice is restricted to each stratum. The node's five-step proof plan is included in
the theorem docstring. The definition of coefficient pullback agrees with Stacks 03D2;
the tensor comparison is the one in Stacks 03EL. The module's extra explicit unit
normalizations express the induced maps already named in the node.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Prime ℓ | `(l : ℕ) [Fact l.Prime]` |
| Finite extension E/ℚ_ℓ | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Canonical ℓ-adic topology on E | `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`; this is the field with the recorded spectral absolute-value topology |
| A = O_E, subspace topology | `latticeCoefficientIntegers l E`, the existing valuation subring transported along `WithAbs.equiv`, with its subtype topology |
| Every scheme's small pro-etale site | `Scheme.ProEt.topology X` and `Scheme.ProEt.topology Y` through `latticeModuleRing` |
| A_T(U) = C(|U|,A), E_T(U) = C(|U|,E) | `latticeCoefficientSheaf` and its underlying `latticeModuleRing`; sections are `ULift C(U.left,T)` with precomposition restrictions, without discretizing T |
| Sheaves of modules | The recorded `CategoryTheory.ringedSiteModules.{u + 1}` over those ring sheaves |
| Any g:Y→X | `{X Y : Scheme.{u}} (g : Y ⟶ X)`, with no morphism-property binder |
| L locally finite free over E_X | `L` over the field coefficient ring and `[L.IsFiniteLocallyFree]` |
| M locally finite free over A_X | `M` over the integer coefficient ring and `[M.IsFiniteLocallyFree]` |
| Varying finite ranks, including zero | Existing `SheafOfModules.IsFiniteLocallyFree`, whose local generators may have different finite cardinalities, including the empty type |
| A_X-linear i:M→L | `i : M ⟶ (SheafOfModules.restrictScalars ...).obj L`, along `integralLatticeCoefficientMap X l E` |
| i monic | `[Mono i]` |
| Its induced E_X⊗M→L is invertible | `hi` gives `phi` from the existing `changeOfRings` object, `IsIso phi`, and `phi(1 ⊗ m) = i(m)` for every object and section |
| Canonical coefficient pullback | Existing `continuousModulePullback`, exactly `changeOfRings (continuousCoefficientInverseImageMap g T) ((proEtaleModuleInverseImage g ...).obj M)` |
| The actual induced inclusion | The unique `j` with the displayed formula `j(unit_M(m)) = unit_L(i(m))` on every base-change test object |
| Pulled inclusion monic | `Mono j` |
| Both pulled modules locally finite free | The two `.IsFiniteLocallyFree` conjuncts on the actual `continuousModulePullback` objects |
| E_Y⊗g_A^*M→g_E^*L is an isomorphism | `beta` with domain the existing `changeOfRings (integralLatticeCoefficientMap Y l E)` and codomain the actual field-coefficient pullback, together with `IsIso beta` |
| This is the adjoint of the pulled inclusion itself | For every Y-site object and section, `beta(1 ⊗ m) = j(m)`, using the actual sheafification insertion |

`hi` adds no choice of rationalization: scalar extension's universal property says that
there is exactly one map with the displayed unit formula. Thus its existential form is
equivalent to the node's hypothesis that the induced map is invertible. Similarly,
inverse-image adjunction-unit sections locally generate inverse image; after scalar
extension their scalar multiples locally generate pullback. Consequently the displayed
unit formula uniquely determines `j`. Its `∃!` binder packages the canonical induced map
and the node's conclusions, rather than assuming an arbitrary map or a comparison
isomorphism. Finally the unit formula for `beta` uniquely determines its scalar-extension
adjoint on all local pure tensors by linearity. These formulas include the identity map
and arbitrary lifts/restrictions of sections, via the existing adjunction constructions.

Dependencies reused (the signatures and docstrings were read in their source modules):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing
  `Padic.coefficientExtensionAbsoluteValue`, `Padic.coefficientExtensionIntegers`, and
  the finite-extension setup of `def-weil-l-adic-coefficient-extension`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.ContinuousIntegralCoefficients`: the recorded continuous coefficient
  interface `CondensedRing.continuousIntegers`. The already landed general-universe
  lattice coefficient presentation supplies the same valuation ring with canonical
  topology through `WithAbs`, rather than imposing an additional normed-field hypothesis.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, publicly importing
  the recorded scalar-extension construction
  `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`;
  Mathlib's `PresheafOfModules.sheafificationAdjunction` gives its unit.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`,
  `proEtaleSheafAdjunction`, `proEtaleModuleInverseImage`, `proEtaleModelRingUnit`.
- `Sheaf.Paper.ContinuousConstructibleModule`: `continuousCoefficientDirectImageMap`,
  `continuousCoefficientInverseImageMap`, `continuousModulePullback`; these do not assume
  a Noetherian scheme (the later constructibility predicate in that file does).
- `Sheaf.Paper.LatticeSheafBasic`, publicly reached through that module:
  `latticeCoefficientSheaf`, `latticeModuleRing`, `latticeCoefficientIntegers`,
  `integralLatticeCoefficientMap`; the new existing-definition record
  `def-sfb-continuous-lattice-coefficients` now records this presentation directly.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` and its local-generators definition.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `ProEtaleTensorComparison.inverseSection`, using the actual transported module
  adjunction unit; its new existing-definition record is
  `def-sfb-proetale-inverse-image-unit-section`. The comparison theorem remains a proof
  dependency, rather than a statement dependency.
- The other proof dependencies are imported as ordinary proof-only imports:
  `ProEtale.toposFunctorialityInverseImage`, `ProEtale.isIso_condensedPullbackHom`,
  `CategoryTheory.NatTrans.naturality` for the coefficient square,
  `Scheme.proEtaleObjectInverseImageRestriction`, and
  `ProEtale.chartComparison_naturality` with its continuous-realization API.

The statement uses the already landed definition dependency
`def-weil-pbc-continuous-constructible-module` for canonical coefficient pullback, and
the two new definition records listed below for continuous lattice coefficients and the
inverse-image unit section. Neither theorem node from the return is in `stmt_deps`.
`lem-pur-proetale-inverse-image-tensor-comparison` remains in the unchanged `proof_deps`.
The image-classification theorem itself is unnecessary for this statement or its proof
plan; only its module's existing plain definitions are reused. The advisory about
`def-weil-pbc-continuous-integral-coefficients` concerns the inherited condensed encoding:
its original statement dependency and public import are retained; the new coefficient
record explicitly captures the continuous-function presentation actually used here.
No dependency declaration, Lean code, statement, or proof plan is changed.

Edge cases checked mathematically against the formula and existing definitions:

- `g = 𝟙 X`: the unit normalizations identify the induced inclusion with the original one;
  the final adjoint remains exactly the original rationalization.
- Rank zero and the zero module: empty finite bases are permitted, and both unit formulas
  are zero; no positive-rank or nonzero-section requirement occurs.
- Empty schemes: site covers and local freeness remain valid, and all maps have the
  unique required values on empty sections. No nonemptiness binder is present.
- Varying ranks and disconnected schemes: finite local generators impose no fixed rank.
- Arbitrary nonflat or non-quasi-compact `g`: no flatness, immersion, qcqs, Noetherianity,
  base field, or characteristic condition is imposed on the schemes or their morphism.
- No special choice of uniformizer, residue level, or characteristic is required.
- Site object universe remains `u + 1`, Hom universe `u`, and module universe `u + 1`;
  `WithAbs` and the integral subtype stay in `Type u`. Every universe and variable is bound.

Searches made before writing:

- `msearch.py ... leanfinder` with “An inclusion of a locally finite free integral lattice
  stays monic and rationalizes to an isomorphism after scheme pullback on the pro-etale
  site”: eight results about etale morphisms and their base changes; no matching lattice
  statement.
- `msearch.py ... leansearch` with “Pullback of an integral lattice inclusion with scalar
  extension isomorphism along arbitrary morphisms of schemes”: eight results, including
  scheme pullbacks, `PresheafOfModules.pullback`, and pullback of open immersions;
  none asserts the continuous-coefficient lattice statement.
- `msearch.py ... loogle` with
  `SheafOfModules.pullback, SheafOfModules.IsFiniteLocallyFree`: unknown identifier for
  the project-local finite-freeness declaration, zero hits.
- `msearch.py ... grep` with
  `lattice.*pullback|pullback.*lattice|IsFiniteLocallyFree` in the module-sheaf directory:
  zero hits. The same query without a subdirectory returns ten Z-lattice/order-lattice
  results, none about lattices over continuous coefficient sheaves.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for lattice/pullback/local-freeness
  found the existing constructions reused above. The condensed local-freeness theorem
  omits lattice monicity and its scalar adjoint; the immersion coefficient theorem
  concerns rings and assumes an immersion. Neither matches this node.
- Searches for the item id and the three proposed full declaration names in project
  source and `dag/lean_names_upstream.json` found no existing theorem/name collision.

Historical validation of the returned packet (not reproduced during this repair): `scompile.py Q28 lem-sfb-lattice-pullback .../LatticePullback.lean` passes
both sandbox and library-module compilation with no diagnostics (6.2 s and 5.9 s).
An initial unresolved sheafification universe was repaired by explicitly specifying
the module universe `u + 1`; no site universes or mathematical hypotheses were changed.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q28

Author's separate second pass with the node and module open; the maintainer supplies
the independent review required by this dispatch workflow. Rechecked every row above
against the unchanged node statement, the two actual helper definitions, and the
`continuousModulePullback` construction. In particular, `i` is linear only after restricting
the specified rational coefficient module along the actual integral inclusion; its
rationalization is constrained on `1 ⊗ m`. The output `j` is constrained on the canonical
unit sections for that same `i`, and `beta` is constrained on `1 ⊗ p` for that same `j`.
Thus the two existential map presentations cannot hide unrelated isomorphisms. Verified
the four output properties, varying and zero ranks, arbitrary scheme maps, canonical
coefficient topologies, explicit universes, and the five proof-plan steps. No mismatch
or source-based correction was needed. All helper data are defined in full; only the
main theorem is postponed.


## New nodes

`def-sfb-continuous-lattice-coefficients` records, with `existing: true`,
`latticeCoefficientSheaf`, `latticeModuleRing`, `latticeCoefficientIntegers`, and
`integralLatticeCoefficientMap` from `Sheaf.Paper.LatticeSheafBasic`. For any scheme and
commutative topological coefficient ring, the first two give continuous-function ring
sheaves with precomposition restrictions and the unchanged universe lift. For the finite
extension in the item, the latter two give the canonical valuation subring with its
subspace topology and the actual postcomposition inclusion into rational coefficients.
This is precisely the continuous coefficient presentation used in the blueprint's
stratified-lattice proof, "Pushing down by the trace", and in Bhatt--Scholze Definition
6.8.1 and Proposition 6.8.4(6). No definition is duplicated. The complete signatures,
bodies, and docstrings were read at lines 156, 178, 201, and 209 of that module.

`def-sfb-proetale-inverse-image-unit-section` records, with `existing: true`,
`AlgebraicGeometry.ProEtaleTensorComparison.inverseSection` from
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`. It evaluates the
existing transported module-adjunction unit on the original section at the original
base-changed site object. Source: Stacks Tag 03D2 (`lemma-pullback-module`) and the adjacent
`lemma-adjoint-push-pull-modules`, which explicitly uses the map to direct image of inverse
image. Its full signature and real-data body were read at lines 75-83. This is a plain
definition, independent of the tensor-comparison theorem's proof.

Searches for both records were run before adding them. `msearch.py leansearch` queried
"Continuous coefficient ring sheaves on the small pro-etale site and the adjunction-unit
inverse image of a module section" and returned eight generic adjunction/module results,
including `SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app` and
`SheafOfModules.pullbackPushforwardAdjunction`, but no exact small-site specialization.
`msearch.py loogle` queried `latticeCoefficientSheaf, inverseSection`: zero hits, with
"unknown identifier 'latticeCoefficientSheaf'" (an indexing limitation, not evidence that
the published definition is absent). `msearch.py grep` queried the five declaration names:
zero Mathlib hits. `rg` over `lean/WeilConjectures` and `lean/Sheaf` found exactly the
published definitions above and their consumers. `rg -l` over `dag/nodes` followed by
parsing declaration records found that only the two theorem nodes in the return recorded
the five names; no definition node carried them. `blueprint_refs.py search` found zero
nodes for each of `latticeCoefficient` and `inverseSection`; `ancestor` returned
`sk-lem-stratified-lattice`. The actual search counts, names, and diagnostic are stored
in each new node's `mathlib_searches`.

Both records retain all relevant cases: arbitrary morphisms and site objects, rank zero,
empty schemes, and site object universe u+1 / morphism universe u. The coefficient record
uses subspace topology, not a discrete coefficient replacement. The section record uses
the actual adjunction unit, not a section chosen from existence.

## Repair of immutable head 8d1c775d8a63

H2: replaced the two theorem ids added solely for plain definitions by the two new
`existing: true` definition nodes above. The tensor-comparison theorem is still a proof
dependency. The Lean file is byte-for-byte the saved returned version (SHA256
`ab849b917a0893037126a2c344ca7f4742df1ca5cdab1f1c9f5e600e9980645e`). Its theorem, both
real-data helper definitions, imports, universe binders, and all normalizing equations
are unchanged. The saved item's stale `lean_audit` was refreshed from current main;
relative to main, only `lean` and the authorized added `stmt_deps` now differ. No dependency
node is modified. The first dry run was run on the saved packet before this repair.

The original independent immutable-head review approved the Lean clause by clause;
this metadata repair retains that approved Lean. Author's second reading additionally
checked both new definition statements against the complete existing declarations:
continuous sections and restrictions, underlying ring sheaf, valuation-subring transport,
postcomposition inclusion, and the unit section all match. The item's original clauses
remain matched by the table above. No new mathematical hypothesis or conclusion appears.

Current verification attempt: the initial `deliver2.py --no-push` failed before preflight
because local compilation could not find Mathlib/CategoryTheory/Functor/Category.olean,
and server confirmation reported "Live published library is unavailable". Historical
clean compile evidence above is not represented as a new successful compile. The repaired
packet is retained for a prescribed compile and dry-run retry.


Final verification outcome of this repair attempt: the prescribed standalone
`scompile.py Q28 lem-sfb-lattice-pullback .../LatticePullback.lean` again failed locally
on a missing Mathlib `Preadditive/Injective/Basic.olean`, with server confirmation
"Live published library is unavailable". The repaired packet's final
`deliver2.py Q28 lem-sfb-lattice-pullback --no-push` progressed through many dependency
compiles, including the existing coefficient construction, but failed before preflight:
local overlay `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` timed out
at the unchanged 60-second limit. Server confirmation then failed while compiling
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` because the published object file
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
does not exist. No push was attempted. These are published build/dependency failures;
the sandbox's item Lean remains byte-identical to the reviewed packet. Live sources,
compiled artifacts, and launcher tools are read-only under this brief and were not
edited, and no global build or timeout override was run.

Self-check completed: both new definition signatures match the existing source verbatim;
new-node fields and explicit citations match the required shape; the item changes only
`lean` and the authorized `stmt_deps` relative to current main; its saved theorem signature
matches its module; all 121 nodes in its statement-dependency closure are acyclic.
The H2 repair is saved and awaits restored published build artifacts for compilation,
maintainer preflight and delivery.


## Retained-packet verification retry, 2026-10-21

Read the retained report first and ran the prescribed `deliver2.py Q28
lem-sfb-lattice-pullback --no-push` before changing the packet. It failed before
preflight while compiling the unchanged published dependency
`Sheaf.Paper.LatticeSheafBasic` at its import on line 6. The local wrapper and
its current-server confirmation both reported that this published object file
is absent:
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.olean`.
Then ran the prescribed standalone `scompile.py Q28 lem-sfb-lattice-pullback
.../lean/Sheaf/Paper/LatticePullback.lean`; it independently failed at the same
unchanged dependency, with the identical missing-object diagnostic locally and
in server confirmation (0.1 seconds, not a timeout).

The H2 repair remains intact. Reopened the item, both new definition records,
the Lean module, and the existing coefficient and inverse-section definitions.
The item differs from current main only in `lean` and the authorized additions
to `stmt_deps`: the already-landed continuous-pullback definition and the two
new existing-definition records. No original dependency is removed. The two
theorem nodes named in H2 are absent from `stmt_deps`; tensor comparison remains
in `proof_deps`. Both new record signatures still match their existing source.
The item Lean SHA256 remains
`ab849b917a0893037126a2c344ca7f4742df1ca5cdab1f1c9f5e600e9980645e`.
No mathematical statement, helper, import, or dependency source was changed.

Compilation and preflight cannot complete until the published dependency
artifact is restored by the library/build tooling. The worker cannot write
published build artifacts or alter launcher tools. No push was attempted;
the repaired packet is preserved in the authorized sandbox.


## Retained-packet retry, 2026-10-21 04:25 UTC

Inspected the saved report and ran `deliver2.py Q28 lem-sfb-lattice-pullback
--no-push` before editing the packet. It again failed compiling the unchanged
published dependency `Sheaf.Paper.LatticeSheafBasic` at line 6 because
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.olean`
is absent. The wrapper's current-server confirmation reproduced the same error
in 0.1 seconds. Standalone `scompile.py Q28 lem-sfb-lattice-pullback
.../lean/Sheaf/Paper/LatticePullback.lean` independently reproduced this same
missing published object locally and in current-server confirmation. Neither
command timed out. Preflight and item compilation could not be reached; nothing
was pushed.

Retained-packet self-check: compared parsed item JSON with the current shared
main source without running Git. Only `lean` and `stmt_deps` differ; no original
statement dependency is removed. Both new existing-definition records are still
absent from main and cite the exact existing declarations, whose signatures and
real-data bodies were re-read. Neither returned theorem is in `stmt_deps`;
`lem-pur-proetale-inverse-image-tensor-comparison` remains in `proof_deps`.
The Lean SHA256 is still
`ab849b917a0893037126a2c344ca7f4742df1ca5cdab1f1c9f5e600e9980645e`,
identical to the independently reviewed delivery. No repair note is present
for this item. No Lean, node, source-library, compiled-artifact, or launcher-tool
changes were made during this retry. The H2 repair remains saved; delivery is
blocked by the prescribed wrappers' missing published build dependency.

## Retained-packet retry, 2026-10-21 04:27 UTC

Read the saved report and ran the prescribed `deliver2.py Q28
lem-sfb-lattice-pullback --no-push` first. It failed on the unchanged published
dependency `Sheaf.Paper.ContinuousConstructibleModule`, line 6, with:
`object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.olean' of module WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs does not exist`.
The wrapper's current-server confirmation reproduced the diagnostic in 0.1 s.
Then standalone `scompile.py Q28 lem-sfb-lattice-pullback` on the saved
`lean/Sheaf/Paper/LatticePullback.lean` independently failed on the same
published dependency, both locally and in current-server confirmation (0.1 s).
Neither failure was a timeout. Preflight and item compilation were not reached.

Rechecked the retained H2 repair against current shared main by parsing the JSON,
without Git: only `lean` and the authorized `stmt_deps` additions differ; no
original dependency is removed. The two new existing-definition records remain
absent from main. Re-read the existing coefficient definitions and
`ProEtaleTensorComparison.inverseSection`, including their docstrings and actual
bodies; their recorded signatures still match. The returned theorem ids are
absent from `stmt_deps`, and tensor comparison remains in `proof_deps`.
No repair note exists for this item. The Lean SHA256 remains
`ab849b917a0893037126a2c344ca7f4742df1ca5cdab1f1c9f5e600e9980645e`,
unchanged from the independently reviewed head. No Lean or node changes were
needed or made. The required repair is preserved; the published dependency
artifact still prevents the prescribed tools from completing. Nothing was pushed.
