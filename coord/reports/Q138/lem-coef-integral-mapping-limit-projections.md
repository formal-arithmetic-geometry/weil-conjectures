## Worker report

The module `Sheaf.Paper.IntegralMappingLimitProjections` states
`WeilConjectures.integralMappingLimitProjections`. Its single theorem is postponed by
`sorry`; every helper definition has actual data. The original node's statement,
proof, and proof dependencies are unchanged. Its statement dependencies gain the definition ownership node
`def-coef-reduction-limit-shift-data` and the already-landed internal-Hom shift
interface named below, under brief-stage2 §5 and the returned H2 repair.

Source read: current blueprint main-20261015,
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2. The first and last mapping-complex comparisons reconstruct the second
input and give the actual finite-level adjunction maps. I also read the complete item
and every statement dependency's node, declaration signature and docstring, including
the reconstruction proof dependency. The example CompactObject module is withdrawn
in this checkout; the new file follows the active module/public-section convention
of the recorded coefficient calculus instead.

Hypotheses and clauses:

| Node | Lean rendering |
| --- | --- |
| Global algebraic closure of a finite field, characteristic p | `D : FiniteFieldDatum`, with its prime, finite base field, algebraic closure and chosen inclusion |
| Prime l distinct from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p` |
| Finite coefficient extension E/Q_l | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| R, chosen uniformizer, A_n and completed coefficient ring sheaf | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing`, `completedIntegralCommRingSheafUnrestricted`; the scalar-reduction category uses this completion, not the discrete constant integral sheaf |
| W separated and finite type over k | `X : Scheme`, `[X.Over (Spec (CommRingCat.of D.k))]`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of the structure morphism |
| P,Q in D^b_c(W,R) | Each assertion quantifies `P Q : sfIntegralConstructibleCategory l E X`; `.obj` is the ambient ordinary derived object, `.hom` its actual derived morphism |
| Roos completeness, all constructible reductions, common bounded interval | These are exactly the conjuncts in the recorded `sfIntegralConstructible` predicate, not assumptions of bounded Tor-amplitude or integral boundedness |
| Strict system category, R, L, actual u and e | `CoefficientDerivedSystemCalculus`, its `reduction`, `adjunction`, `coefficientSequenceLimit` and `coefficientSequenceDerivedEvaluation`; `C : CoefficientDerivedSystemCoherence` retains the specified enriched/global normalizations |
| Canonical cochain shift conventions | `sh : PurReductionLimitShiftData`, owned by `def-coef-reduction-limit-shift-data`; the theorem quantifies the normalized shift data and does not invoke its existence theorem |
| Global derived mapping complex | Recorded `coefficientIntegralGlobalHom`, definitionally derived internal Hom followed by `coefficientIntegralSections`; analogous `coefficientFiniteGlobalHom` at finite levels |
| lambda = gamma after RHom(P,u_Q) | `integralMappingLimitMap`, literally that composite; gamma is evaluated at `S.reduction.obj Q`, using `S.reduction_normalized Q` |
| Isomorphism in D(Ab) | `IntegralMappingLimitAssertions.isIso` is `IsIso` of the defined composite in the ordinary derived category of abelian groups, not an isomorphism only on cohomology |
| Natural isomorphism | `naturality` states the full two-variable derived-complex square, including noninvertible a,b |
| Actual mapping-limit projection | `integralMappingLimitProjection` is `coefficientMappingProjection`, `S.globalEvaluation` and the canonical `S.reductionEvaluation` identifications, in that order |
| Projection equals second-input reduction followed by scalar adjunction | `projection`: first `coefficientIntegralGlobalHom.map` of the actual finite adjunction unit at Q; then global sections of the finite `coefficientEnrichedAdjunctionMap`; finally `C.scalarSections` |
| Degree-zero h maps to h_n | `integralMappingLimitHom` applies H-zero to the actual lambda/projection composite, using `coefficientIntegralHomEquiv` and `coefficientFiniteHomEquiv`; `hom` equates it with derived extension applied to h |
| e_n (u_Q)_n h_n = h_n | `triangle` writes the evaluated actual reduction of the unit and actual counit, with precisely the finite evaluation identifications at its endpoints |
| Every integer shifted Hom | `shifted_hom` quantifies `r : ℤ`, `h : P.obj ⟶ Q.obj⟦r⟧`, and postcomposes with the normalized finite shift comparison to land in `Q_n[r]` |
| Compatibility with shifts of mapping complexes | `shift` is an equation before homology and before finite projection, using `integralMappingLimitSourceShift` and `integralMappingLimitTargetShift`; the source uses the uniquely normalized Hom target shift followed by the canonical derived-global-sections shift; the target uses the normalized reduction shift, sequence Hom target shift, and total derived-limit shift |
| Composition of mapping complexes | `composition` is the enriched tensor-Hom composition square before global sections. `integralMappingLimitInternal` is the internal unit/enriched-adjunction composite; `integralMappingLimitTensor` is the lax tensor map of L, defined as the adjunction mate of the tensor of its two actual counits. Applying derived sections and S.globalLimit yields the global mapping-complex composition square, without reducing it to Hom-set composition or finite-projection detection |
| Only the first input is extended in scalar adjunction | The finite enriched adjunction extends P and uses Q's restriction via the actual unit. No helper tensors an integral internal Hom or assumes such a base-change comparison invertible |

Recorded declarations reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the coefficient-extension
  rings, uniformizer, quotient maps, and `Padic.finite_coefficientExtensionRing`
  reexported by the calculus.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: recorded completed integral
  coefficients and canonical constant-to-completed coefficient map, reexporting the
  independent-coefficient completion and projections.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`; its global
  branch is the existing augmented-Roos completeness predicate. The theorem's
  hypothesis uses the recorded constructible predicate, whose completeness
  presentation is canonically transported to this branch by the already-published
  coefficient presentation comparison, as in `IntegralSystemReductionFullyFaithful`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` (through the calculus):
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`,
  `derivedScalarExtensionRestrictionAdjunction`; `coefficientFiniteAdjunction` is
  precisely this adjunction with finite category endpoints displayed.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: the actual strict derived system
  category, reduction/evaluation/limit and projections, `CoefficientDerivedSystemCalculus`,
  `CoefficientDerivedSystemCoherence`, `gamma`, the global Hom functors and both
  `coefficientIntegralHomEquiv` and `coefficientFiniteHomEquiv`. Their signature and
  docstrings were read; these are not replaced by arbitrary natural isomorphisms.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`: the generic
  `derivedInternalHomOfUniverses` reexported by the recorded dependency module;
  the ordinary-module specialization itself is not used on module sheaves.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`:
  `rhom_global_sectionsOfUniverses`, through the recorded H-zero identifications.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`:
  `purNormalizedReconstruction` (proof import), exactly invertibility of the actual
  unit on complete objects; no alternative reconstruction map is assumed.
- Added definition dependency `def-coef-reduction-limit-shift-data`:
  `Sheaf.Paper.PurReductionLimitShiftAdjunction`, `PurReductionLimitShiftData`,
  `purCoefficientLimitModel`, `purCoefficientShiftedResolution`,
  `purCoefficientRoosProductShift`, and `PurCoefficientRoosTriangle`. The data fixes
  the finite K-flat shift and simultaneous K-injective total-limit shift and their
  unit/counit compatibility. The existence theorem `purReductionLimitShiftAdjunction`
  is not used to state this item and is no longer a statement dependency.
- Added landed dependency `lem-weil-pbc-ringed-internal-hom-exact-restriction`:
  `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`,
  `CategoryTheory.RingedHomUniverses.hom`, `homCommShift`,
  `rightShift_existsUnique`; the shift is fixed by Hom-complex reindexing.
- The scheme-morphism dependency is a convention node. Its own record directs use
  of Mathlib's `Scheme.Over`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.

Edge cases checked mathematically before writing: n=0 in Lean means exponent one,
so no unintended zero quotient level occurs; every positive exponent occurs. The
zero objects and empty scheme satisfy the same composite and projection equations.
Negative shifts, r=0 and r=1 are included; the target Hom shift is unsigned while
all relevant cochain signs are retained in the recorded derived shift structures.
No perfectness, common Tor interval, local model, or cohomological bound on an
ambient source is added. The constructible predicate retains its actual common
cohomological support interval. The site is still object universe u+1 and morphism
universe u, with module universe u+1; helper maps allow independent t and u and
never identify the site's two universes. Finite fields, schemes and E use the
recorded category's common containing universe in the main theorem.

Searches made (in addition to reading the recorded dependency implementations):

- msearch leanfinder, query: "Global derived Hom of complete sheaf complexes is the
  derived inverse limit of finite coefficient mapping complexes with actual reduction
  projections". Eight hits: Sheaf.H, localCohomology.diagram, Ext, cohomologyPresheafFunctor,
  cohomologyPresheaf, ProjectiveResolution.extMk_hom, InjectiveResolution.extMk_hom,
  instAddCommGroupH. None states the varying-coefficient derived-system comparison.
- msearch loogle, query: `"derivedHom", "limit"`: zero hits.
- msearch grep Mathlib, query: `derivedHom.*[Ll]imit|[Ll]imit.*derivedHom|mappingLimit`:
  zero hits.
- msearch leansearch, query: "Derived Hom into a derived complete sheaf is the derived
  inverse limit of finite reduction mapping complexes": eight hits about
  HasDerivedCategory, complex limits, sheaf-module limits and mapDerivedCategory;
  none has the mapping-limit comparison or actual quotient projections.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `integralMappingLimit|integral_mapping_limit|lem-coef-integral-mapping-limit-projections|mappingLimit.*[Ii]so|[Ii]so.*mappingLimit`:
  no matching declaration. The prescribed node-id grep in WeilConjectures returned
  no hit. rg of proposed declaration names in Mathlib, upstream source and
  `dag/lean_names_upstream.json` also found none. Existing generic calculus supplies
  the components, but no prior declaration assembles this constructible comparison.

No statement dispute, statement correction or dependency module is needed.
The returned H2 repair adds definition ownership as described below.
The docstring reproduces the four proof steps and names the reconstruction,
enriched-calculus and RHom/Hom dependencies. All compilation uses scompile.py.

## Author clause audit

Author's separate checking pass, with the node and module open. The maintainer's
independent mathematical reading remains part of the prescribed delivery review.

This pass found that section variables for the finite-field datum and geometry
would otherwise be omitted by Lean because no result type referenced them. They
were moved into explicit theorem binders: the delivered theorem really retains D,
l ≠ D.p and all four scheme/base hypotheses. It also checked the inverse orientation
of `reductionEvaluation` on the contravariant finite Hom input, the actual H-zero
projection rather than an unrelated additive equivalence, and both actual u/e
maps in the triangle formula. Shifted Hom quantifies all integers and compares
actual maps to Q_n[r]; a separate square retains compatibility of whole mapping
complexes. Composition is stated through the actual enriched comparison and the
counit-defined lax tensor map before taking global sections, so it is not merely
an equality on finite projections or Hom sets. The canonical derived sections
shift is supplied explicitly through the recorded ordinary-sections right derived
functor, with the same Grothendieck instance as that construction.

Validation: scompile.py compiled the sandbox and final library module cleanly; no errors
or warnings. The delivery dry run will also compile the final packet and run server
preflight before push.

## New nodes

`def-coef-reduction-limit-shift-data` owns the unchanged existing
`WeilConjectures.PurReductionLimitShiftData` and the four helpers
`purCoefficientLimitModel`, `purCoefficientShiftedResolution`,
`purCoefficientRoosProductShift`, and `PurCoefficientRoosTriangle`, using
`existing: true` in `Sheaf.Paper.PurReductionLimitShiftAdjunction`. Its source is
the current blueprint's coefficient-comparison sentence and the already-published
resolution/Roos normalization. It introduces data, with no inhabitation claim.
The signature was checked against the existing source. No module is added.

Clause audit: the prime, extension, and arbitrary scheme are the existing explicit
section variables `l`, `E`, `W` with independent universes `u`, `t`. The canonical
limit model is exactly restriction/localization, the image of `j`, and the
right-derived comparison; shifted resolution is the termwise comparison followed
by `j[r]`; product shift uses localization shift and `PreservesProduct.iso`.
The Roos helper has `p`, `δ`, `triangle`, and the normalization `projection`.
The structure's clauses are `reduction_shift`, `finite_reduction_shift`,
`finite_shift_model`, `reduction_shift_evaluation`, `limit_shift`,
`limit_shift_resolution`, `products`, `roos`, `roos_triangle_shift`,
`unit_shift`, and `counit_shift`. The signed equation includes `r.negOnePow`
and `shiftFunctorComm _ 1 r`. No geometry or completeness premise is added.
The empty scheme, zero complexes, n=0 (exponent one), and all integer shifts
including r=0 and r=±1 are retained. The definition does not assert existence.

Searches: msearch LeanSearch for normalized reduction/limit shift data returned
8 generic cochain/triangulated/K-injective shift declarations; msearch LeanFinder
for a structure preserving units, counits and signed Roos triangles returned
8 generic derived shift and mapping-cone declarations; msearch grep of all five
helper names returned 0 Mathlib hits. The exact queries and unmodified JSON
search responses are in the new node's `mathlib_searches`. DAG name grep found
only the existing statement node `lem-pur-reduction-limit-shift-adjunction`,
which records the existence theorem and helpers but provides no definition-node
ownership. The blueprint search returned 0 matches for the structure name.
Project grep found only the exact existing module; upstream grep had no hits.
This reuses that definition and adds the missing DAG ownership, with no duplicate
Lean definition and no dependency on the theorem asserting `Nonempty` of the data.

## Returned H2 repair

The return on immutable head `48b560d7987f` asked for definition-node ownership
and replacement of `lem-pur-reduction-limit-shift-adjunction` in `stmt_deps`.
Both changes are made. The retained saved packet first passed the required dry
run at `dcbbc8d0d0b`; the repair changes the item's node and report, and adds only
the definition node. The item's Lean module, signature, mathematical statement,
proof, and proof dependencies are unchanged. The genuine internal-Hom shift
theorem dependency remains. Current main has no definition node for these data
and no Lean record on the item; the delivery wrapper rebases the packet on main.

Self-check: all five existing declarations were read with their full signatures
and docstrings. The new node has exactly the §5 fields, cites exactly its inline
dependencies, and its `lean` is `existing: true` with no file. The item cites the
new definition node in place of the unused existence theorem. The existing module
continues to supply the same import and names, and no Lean source was changed.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
