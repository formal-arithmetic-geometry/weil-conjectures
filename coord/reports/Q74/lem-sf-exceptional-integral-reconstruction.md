## Worker report

Q74 states `lem-sf-exceptional-integral-reconstruction` in
`lean/Sheaf/SixFunctors/ExceptionalIntegralReconstruction.lean`, declaration
`WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction`.
The only postponed proof is this named theorem. Every helper definition has real
functor, natural-isomorphism or categorical data; structures specify the theorem's
conclusions, and their nonemptiness is a conclusion, never an input assumption.
The node statement and proof are unchanged. Its statement dependencies gain existing
landed nodes for the strict-system, coordinate and shift interfaces used in its type.
The repair adds three definition owners for the existing interfaces; no replacement coefficient category is introduced.

### Hypothesis and clause correspondence

* The global finite field is `(D : FiniteFieldDatum.{u})`. Its characteristic and
  algebraic closure are the recorded `D.p` and `D.k` fields. The coefficient prime is
  `(l : ℕ) [Fact l.Prime]`, with `(hl : l ≠ D.p)`. The coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  These parameters are bound explicitly at the beginning of the public section.
  The ring and uniformizer are the recorded `Padic.integers` and quotient
  constructions. `integralExceptionalIntegers` and
  `integralExceptionalUniformizer` only apply the published universe lift to them.
  Level `n : ℕ` denotes the positive exponent `n+1` throughout.
* Finite-type k-schemes are the explicit `X.Over (Spec (.of D.k))` and `Y.Over ...`
  instances together with `LocallyOfFiniteType` and `QuasiCompact` on their structure
  maps. The theorem explicitly binds `(f : X ⟶ Y)`, `f.IsOver ...`, `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f`, and `(c : Compactification f)`.
  There is no absolute separatedness assumption. The fixed compactification uses
  the published `c.i`, `c.g`, `c.Z` and its factorization data.
* C and its inclusion I are exactly `finiteTorConstructibleIntegralCategory l E T`
  and `(finiteTorConstructibleIntegral l E T).ι`. This predicate uses
  `sfIntegralConstructible`, derived completeness, intrinsic constructibility of
  every positive reduction, a common cohomological interval and a common Tor interval.
  The locally registered `integralTriangulated` instance merely exposes the existing proved
  `ConstructibleExceptionalCoefficients.integralTriangulated` at the unbundled E.
  It introduces no new triangulation or axiom. That helper's proof is in the imported
  data module and uses only exact reduction and the common-interval triangle argument.
* N is defined by `normalized l E T := IsNormalizedCoefficientSequence l E T ∧
  IntegralSystemRealization.LevelBounds l E T`. `LevelBounds` contains the common
  constructibility, cohomological and Tor conditions at every level; normalization
  is invertibility of the transition adjuncts for all coefficient quotient maps.
  No compatible-origin witness or additional local model is imposed in N.
* R is `(calculus l E T).reduction`, and L is the recorded
  `coefficientSequenceLimit l E T`; neither is replaced by an arbitrary functor.
  `Reconstruction.equivalence`, `.reduction` and `.limit` give the restriction and
  identification with these actual functors. `.unit` and `.counit` equate the
  restricted maps to the fixed calculus adjunction's actual unit and counit.
  `.coherence` retains its simultaneous K-flat model and projection equations.
  `.resolutions` supplies `PurSequenceResolutionData`: actual quotient section maps,
  the whole Hom normalization, the flat-term K-flat presentation including all
  quotient transitions, and equations identifying its derived unit/counit with the
  calculus unit/counit. Thus the unit is the compatible quotient cone identified
  with completion, and the evaluated counit is precisely the scalar adjunct of the
  total-limit projection. `.resolutionShifts` and `.shifts` retain termwise,
  K-injective-limit and signed Roos normalization of these same maps.
* The first conjunct of the theorem gives this equivalence for every finite-type
  k-scheme T. The second supplies the two equivalences used for X and Y and the
  actual ordinary-etale transport package `Systems`. Its fields are the recorded
  ordinary proper/open construction, its right adjoint, all three comparison sites,
  the pro-etale proper/open word and its canonical comparison/transport coherence.
* `coordinates` is the derived equivalence of the existing explicit quotient-ring
  coordinate equivalence `integralExceptionalCoordinates`; it is not a new
  coefficient sheaf. `Systems.left` and `.exceptional` are literal compositions of
  this equivalence, `exceptionalProSupport`, and `exceptionalSystemRight`.
  `SystemAdjunction.leftStable` and `.rightStable` restrict them to exactly N.
  `.originX` and `.originY` are conclusions about N, used to access the transported
  adjunction. `.transpose` is an equation of whole-system arrows: after the coordinate
  counit and site counit, the Hom transpose is the ordinary-etale adjunction transpose
  following the fixed proper/open comparison and site unit. It fixes the adjunction,
  including its unit and counit, before finite evaluation.
* `integralLeft` and `integralRight` are the literal restrictions of L F R and L G R,
  conjugating `SystemAdjunction.F/G` by `Reconstruction.equivalence`.
  `leftComposite` and `rightComposite` identify their included functors with those
  literal ambient composites. `integralAdjunction` is defined by composing the two
  reconstruction adjunctions and the fixed restricted system adjunction; its unit
  and counit are therefore the transported maps, with both triangle identities.
* `Realization.leftAdditive`, `.rightAdditive`, `.leftExact`, `.rightExact` assert
  additive exactness on the integral finite-Tor categories. `.leftShift` and
  `.rightShift` give coherent integer shifts; `.unitShift`, `.counitShift` and
  `.rightShift_adjoint` fix their adjoint compatibility.
* `Systems.leftEvaluation/rightEvaluation` are defined from the published system
  evaluation comparisons and the actual coordinate counits. The integral
  `leftEvaluation/rightEvaluation` first use the actual reconstruction counit and
  then exactly these system comparisons. Their target functors are the fixed finite
  proper/open and exceptional operations from the same system package. All quotient
  transition, finite unit and finite counit equations are retained in
  `Systems.transport` and `SystemAdjunction.transpose`, so the integral comparisons
  are obtained from the actual adjunction, not chosen from levelwise existence.
* `UniformBounds` gives four integers independent of n. For every normalized input
  and every proposed input cohomological or Tor interval, the corresponding output
  interval is enlarged by these fixed endpoints. `Realization.leftBounds` and
  `.rightBounds` assert this for both actual system operations. Constructibility at
  every level is included in the two stability clauses. Via the defined integral
  evaluation comparisons these are the uniform bounds of the integral reductions.
* `prescribed` is literally the previously recorded reduction-tower compact-support
  functor, precomposed with the published finite-Tor inclusion. `.prescribedStable`
  asserts it lands in the same finite-Tor category; `.identification` is u.
  `Realization.prescribedAdjunction` is defined by transporting `integralAdjunction`
  through u, so the prescribed functor itself is a left adjoint to the same G.
* `prescribedRealization` is h: the inverse of the published
  `sfQcqsCompactSupportRealization`, restricted by the actual finite-Tor inclusion.
  `Realization.realization` is r. `.primitive` records the proper/open construction
  of r: `leftComposite`, limit of the system proper/open comparison, the canonical
  proper direct-image/limit comparison, and proper image of the inverse open
  reduction mate followed by inverse completion unit. `.openUnit` states precisely
  the invertibility used here, as a conclusion on the intermediate open object.
* `.normalization` is the componentwise equality of actual integral arrows
  `I.map(u.app K) = r.app K ≫ h.inv.app K`, exactly I(u)=h⁻¹∘r in the node's
  right-to-left notation. Its operands are the named whole functors and maps.
  `.systemLeftShift`, `.leftCompositeShift`, `.rightCompositeShift`,
  `.realizationShift`, `.prescribedRealizationShift`,
  `.prescribedLiftShift_inclusion` and `.identificationShift` give compatibility of
  these same maps with the proper/open, termwise and normalized Roos shift structures.
  No assertion identifies integral arrows merely because their finite evaluations agree.

### Dependency declarations used

The original statement dependencies are used directly: `FiniteFieldDatum`
(`Sheaf.Paper.FiniteFieldFiber`); `Padic.finite_coefficientExtensionRing` and the
coefficient constructions (`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`);
Mathlib's relative `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and scheme-over
instances; `Compactification`/refinements (`WeilConjectures.Compactification.RefinementCategory`);
`sfIntegralConstructible` (`Sheaf.Paper.SfIntegralConstructible`);
`finiteTorConstructibleIntegral`, its category and the finite predicate
(`Sheaf.Paper.FiniteTorAmplitudeSites`);
`CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`, actual
reduction, normalization, projection and evaluation declarations
(`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`); and
`sfQcqsCompactSupportRealization`, `sfCompactSupportFiniteIntegralFunctor`,
`PurCompactSupport.finiteTorIntegralInclusion`, and `coefficientPrimeUnit`
(`Sheaf.Paper.QcqsCompactSupportRealization`).

Additional existing statement dependencies provide `System`, `Integral`, `calculus`,
`Operations` (`def-sf-integral-system-operations`); `LevelBounds`
(`def-sf-integral-system-expression-domain`); `RealizationModel.push/openReduction`,
`ringedOpen` and `ringedPush` (`def-sf-integral-system-canonical-bridge`, module
`Sheaf.SixFunctors.IntegralSystemCanonicalBridge`); the actual ordinary/pro-etale
system packages, `exceptionalProSupportEvaluation`, `exceptionalSystemRightEvaluation`,
`exceptionalSystemOriginComparison` (`def-sf-exceptional-system-interfaces`);
the explicit lifted quotient-coordinate equivalence
(`def-pur-adic-exceptional-system-realization`); `PurReductionLimitShiftData`
(`def-coef-reduction-limit-shift-data`); `PurSequenceResolutionData`
(`def-pur-sequence-adjoint-resolution-data`); `PurSequenceAdjointShifts`
(`def-sf-sequence-adjoint-shift-interfaces`); and fixed `integralShifts`,
`systemOpenShift`, `systemPushShift` (`def-pur-integral-operation-shift-data`).
Their DAG dependency closures were checked for a path back to this item; none exists.
The inherited finite-Tor triangulation is an existing proved helper from
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`, not that module's
large exceptional-adjunction existence theorem. No downstream exceptional-adjunction
assertion is assumed in this file.

### Edge cases and source check

The empty scheme and zero object impose no nonemptiness hypothesis on geometry or
cohomological support; common ordered intervals can be chosen for zero. Empty input
intervals in UniformBounds cause no issue (the only possible supported input is
zero). The identity morphism and identity compactification use the same ordinary
unit/counit and quotient models, with no exclusion or arbitrary-lift case removed.
Both arbitrary finite type nonseparated source/target schemes and open embeddings
are allowed; only f is relatively separated. The intermediate compactification
scheme is finite type because its map to Y is proper. Its open immersion is
quasi-compact by Noetherianity, as in the node proof. No unproved finite-dimensional
or purity assertion is inserted as a hypothesis. All n refer to n+1, excluding the
zero coefficient quotient. CommShift ranges over every integer, including negative
shifts, and the retained Roos triangle includes its signed connecting-map equation.

Read the current blueprint under `literature/blueprint/latest/`, in particular its
exceptional inverse-image paragraph, and Zheng's recorded propositions, Lemma 5.22
and Proposition 5.24 using the local PDF. The current blueprint gives the ordinary
etale construction and integral exceptional adjunction; the node specifies the
additional actual reconstruction and normalization assembly. The accepted nine-step
proof is rendered in full in the theorem docstring. No statement fault was found;
there is no STATEMENT-DISPUTED claim or statement correction.

### Searches for reuse

Before writing, searched the DAG, project Sheaf and upstream WeilConjectures sources
for the item id, exceptional reconstruction, normalized-system equivalence and actual
integral realization. Existing pieces were found and reused; no declaration stated
this entire reconstruction plus prescribed compact-support normalization theorem.

`msearch.py Q74 lem-sf-exceptional-integral-reconstruction leanfinder` on the plain-word
reduction/normalized coefficient-system reconstruction and compact-support
adjunction description returned eight unrelated adic-completion/condensed results.
The Loogle query `CategoryTheory.Adjunction, CategoryTheory.Equivalence,
WeilConjectures.sfIntegralConstructible` found no hit (project identifier unknown to
the index). The Mathlib CategoryTheory grep query
`reduction.*[Aa]djunction|[Nn]ormalized.*[Ss]ystem` found no hit. LeanSearch on
`derived complete normalized coefficient systems inverse limit equivalence` returned
eight general inverse-system/adic results, no geometric statement. Direct rg searches
in `lean/WeilConjectures` and `lean/Sheaf` found generic reconstruction
`purNormalizedReconstruction`, strict-system transport, and the existing coordinate
and compact-support constructions used above, but no exact match. The direct search
for `lem-sf-exceptional-integral-reconstruction` found no existing Lean declaration.
Mathlib's `Equivalence.toAdjunction`, `Adjunction.comp`, `Adjunction.ofNatIsoLeft`,
functor whiskering and derived-category functoriality implement the categorical
composites instead of private copies.

### Validation

All compiler calls use the prescribed `scompile.py` wrapper against the published
live library. The final server compilation passed in both sandbox and library module modes,
with no errors or warnings. The final library invocation took 40.0 seconds; the wrapper
also reports shared-slot queue time separately in its sandbox elapsed time.
The first dry run found that its declaration parser omitted named `local instance`
commands. Recast the six computational instance helpers as named instance declarations,
then removed their global registration and registered them locally, preserving their
data and scope. This also preserves the standard instance reducibility annotations.
Recompiled the resulting module before repeating the dry run. No direct shared-repository writes, git mutation, global
build, or subagent was used.

The required `deliver2.py --no-push` completed successfully: its packet passed
preflight and compiled cleanly (dry-run commit `32e69063256`).

## Second reading by Q74

The dispatcher explicitly forbids starting other agents and specifies independent
review by the maintainer. This is a fresh self-check, not a claim of a second agent's
independent approval. Compared the complete node, every structure field and the final
signature. Corrected shift-instance elaboration to use the existing unbundled
finite-Tor triangulation and explicit derived quotient-coordinate shifts. Made the
main theorem's geometric assumptions explicit so section-variable omission cannot
drop relative separatedness or finite-type assumptions. Checked the orientation of
h, r and u and the natural-isomorphism whiskerings against each functor's full domain
and codomain. Added the actual transported adjunction for the prescribed functor.
Checked that compatible origins are conclusions and that N has exactly the stated
common-bound normalization property. The node's statement remains unchanged.

## Inherited returned construction steps 10–12 (verbatim)

Old step 10: Use the reduction/total-limit adjunction $\mathcal R_T\dashv\mathcal L_T$ of the derived-system evaluation calculus. Its unit is the actual compatible cone of quotient maps from one flat-term K-flat representative. The $L=E$ case of the finite-free completed-scalar comparison identifies that unit with the derived-completeness isomorphism for integral objects. On normalized systems its counit is invertible by normalized-DVR effectivity; the component is the scalar adjunct of the actual total-limit projection. Thus these functors restrict to mutually inverse equivalences between derived-complete objects and normalized systems, with the named unit and counit. Under the integral category definition, common constructible cohomological and Tor intervals on the levels are exactly the finiteness conditions needed for these equivalences to restrict to our integral finite-Tor subcategory.

Cited nodes: lem-coef-derived-system-evaluation-calculus, lem-weil-finite-free-completed-scalar-comparison, lem-coef-normalized-dvr-effectivity, def-weil-derived-complete-integral-detailed, def-weil-finite-tor-amplitude.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Reduction and total-limit reconstruction; Zheng Section 4 and the explicit pro-etale effectivity nodes."}

Old step 11: Restrict the transported system adjunction to normalized systems of bounded constructible finite-Tor levels. The left bounds of Step 1 are uniform in $n$; the finite exceptional preservation corollary gives common right bounds, and the system theorem gives normalized right outputs. Define $F_R=\mathcal L_Y\mathsf F^{pro}\mathcal R_X$ and $G_R=\mathcal L_X\mathsf G^{pro}\mathcal R_Y$. Transport the actual unit and counit through the equivalences of Step 10; their triangles follow from the system triangles and those equivalences. The integral compact-support theorem identifies $F_R$ with the published reduction-tower functor and its specified reductions. The integral finite-Tor subcategory is triangulated. Reduction and total limit are exact, and the system adjunction is exact, so these are exact operations; alternatively apply the right-adjoint exactness theorem with the adjoint shifts. The unique adjoint shift structures give unitShift and counitShift.

Cited nodes: lem-pur-etale-coefficient-system-adjoint, cor-pur-general-admissibility-datum, lem-coef-integral-compact-support, lem-weil-integral-ctf-triangulated, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Constructions 5.20 and 5.25, Proposition 5.24; normalized-system integral adjunction."}

Old step 12: Choose the integral left functor to be the prescribed reduction-tower compact-support functor, transporting the adjunction of Step 11 along its specified identification. The system-realization theorem applied to the single word $S_{p_c}J_j$ supplies its natural realization in the ambient completed-ring derived category, with the canonical proper/open maps. All intermediate objects satisfy its hypotheses by Step 1 and Step 11. Take $r_{c,R}$ to be the inverse of this ambient-to-tower realization after the integral-left identification. Then the included integralLeft map is, by this very choice, $r_{c,R}$ followed by the specified ambient-to-tower realization: this is integralLeft_normalized. This uses a realization of the actual system maps, rather than inferring equality of integral maps from finite evaluations. For the named integral realization and its maps, use the slotwise shift-realization theorem; it states compatibility with the canonical termwise and Roos-cone shifts for these same normalized expressions.

Cited nodes: lem-sf-integral-compactification-system-realization, def-weil-integral-rational-qbar-compact-support, lem-pur-integral-realization-shift-coherence.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Single-compactification word realization; the published reduction-tower compact support and its proper/open maps."}

### lem-sf-exceptional-integral-scalar-mates


## New nodes

* `def-sf-strict-etale-exceptional-adjoint-interfaces` owns the fixed-coefficient
  `StrictEtaleExceptionalAdjointData`, coherence subtype, and accessor definitions.
  These are moved unchanged from `EtaleCoefficientSystemAdjoint`; the theorem module
  publicly imports the owner. Its source is Zheng 4.1, 5.15, 5.22 and 2.29(2).
* `def-sf-exceptional-system-interfaces` owns the strict pro-etale proper/open,
  comparison, evaluation, origin, Hom-chain and transport records previously defined
  in `ExceptionalSystemTransport`. That theorem module publicly imports the owner.
  Sources are Zheng 4.1, 4.10, 5.22 and Stacks 0B65.
* `def-sf-sequence-adjoint-shift-interfaces` owns `PurSequenceAdjointShifts` and its
  left/right resolution models, shifted replacement and normalization predicates.
  These are moved unchanged from `PurSequenceAdjointResolutionShifts`, which publicly
  imports the owner. Sources are the blueprint coefficient-comparison sentence and
  Stacks 0941, 06YY and 0D6E. The original parameter universes are retained.

For all three, msearch LeanSearch returned eight general shift/adjunction results,
Loogle reported the strict-system identifiers unknown, and Mathlib grep returned no
matches. WeilConjectures rg returned no matches; Sheaf rg found precisely the existing
plain definitions being moved. Definition-node searches found no owners; the two
clopen nodes mentioning the etale adjoint specialize it and do not own its definition.
blueprint_refs searches for exceptional system and sequence adjoint shift found no
matching units. Each new node carries these search results in mathlib_searches.

## Dependency modules

`lem-pur-etale-coefficient-system-adjoint`, `lem-sf-exceptional-system-transport`,
and `lem-pur-sequence-adjoint-resolution-shifts` retain their theorem statements and
proof bodies. Their former interface records did not provide definition-node ownership
for the notions needed by this item. Each module now publicly imports the new owner,
and each lean record removes the moved definitions and documents the relocation.
This is the dependency-module repair explicitly required by the immutable-head return.
No theorem conclusion is used merely to obtain these definitions.

## Returned-head repair

The sandbox was compared against immutable returned head da5c20ee4c71 and the current
read-only main sources. The main import and stmt_deps lists drop
lem-sf-exceptional-system-transport, lem-pur-sequence-adjoint-resolution-shifts,
lem-sf-integral-basic-realization and lem-sf-exceptional-finite-operations. They gain the
three definition owners above and the existing def-per-strict-etale-system-interfaces
(StrictEtaleCompactSupport) and def-sf-integral-system-canonical-bridge
(RealizationModel, ringedOpen, ringedPush). All seven sandbox modules compile with the
prescribed scompile.py server wrapper; only existing named theorem sorry warnings occur.
The second reading is a self-check as requested in the return, with no other agent.


### Canonical realization advisory repaired

`Realization.systemLeft_normalization` fixes the new whole-system comparison on the
actual site inverse image of every etale derived system and every bounded-below finite
projection. Its left side is derived evaluation of `Systems.supportMap` followed by
`systemLeft`, then the recorded `IntegralSystemRealization.supportEvaluation`.
`supportMap` is literally `exceptionalSystemComparison` followed by the inverse
coordinate counit. On bounded-below inputs this is invertible by the existing
transport coherence. Its right side is `Systems.supportProjection`, a real composite
of the published scalar-unit-normalized `integralExceptionalCoordinatesInvFixed`,
exact site-localization `integralExceptionalSiteDerivedInverse`,
`integralExceptionalEtaleSupportComparison`, the canonical proper adjunction mate/open
`compactSupportSiteComparison`, the fixed intrinsic support realization and coordinate
counits. Thus it uses the canonical proper/open word, rather than an arbitrary
isomorphism between endpoint functors. The existing transport comparisonEvaluation
clause identifies this route with `Systems.leftEvaluation`, whose coordinate counit
and `exceptionalProSupportEvaluation` are unchanged. Multiplying systemLeft alone by
a nontrivial scalar violates this equation: all right-hand factors are fixed before
that choice. No equality of system morphisms is inferred from their finite images.

The additional used definition owners are def-pur-adic-proetale-realization,
def-pur-adic-derived-site-realization, def-pur-adic-support-realization,
def-sf-intrinsic-compact-support-realization and
 def-sf-compact-support-site-comparison-construction. The last supplies the specified
proper-mate-normalized comparison, rather than the older Nonempty-choice interface.
These owners and modules are read and cited directly in stmt_deps.

## Second reading by Q74 (repair self-check)

Self-check, as the maintainer requested: the main node statement, every geometric
hypothesis, the normalized category, n+1 indexing, unit/counit, exact shifts and uniform
bounds are unchanged. The newly owned interfaces are literal relocations, with their
original universes and equations. The three theorem modules reexport the new owners,
and their theorem signatures/proof bodies remain identical. The new normalization
clause repairs the previously unconstrained comparison using canonical published maps.
Identity compactification, residue exponent n=0, negative shifts, zero input and empty
schemes retain their actual canonical maps; no separatedness beyond that of f is added.
The additional bounded-below test in supportProjection is precisely the domain of the
published proper/open comparison; it is not an extra hypothesis of the main theorem.


Final validation: the canonical projection version and all six interface/reexport
modules compile with scompile.py. Every new declaration binds its variables and
universes explicitly; the main theorem alone is newly postponed. Definition data
remain fully written. The current blueprint fix-prop-coherence proof was read at
literature/blueprint/latest: its coefficient comparisons are explicitly the same
evaluation maps and adjunction units/counits, and the exceptional comparisons preserve
those maps. New pro-etale and etale records cite def-pur-coefficient-system-image-data
for the already normalized image packages instead of using an existence theorem.

## Reviewer fix (landing; independent second reader)

The delivery moved the plain definitions out of the three published theorem modules
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`, `Sheaf.Paper.ExceptionalSystemTransport` and
`Sheaf.Paper.PurSequenceAdjointResolutionShifts` into new modules of the three new definition
nodes. The landing index (`import_prune_check` check 3 through the parallel landing's source
index) still lists those names in the live theorem modules and refuses any such intra-delivery
move ("declares names that other modules already declare"), as it did for the N6 91e1 and
Q48 1638 extractions. The reviewer therefore applied the landed re-export shape (Q14 735d,
Q97 c6be, Q38 1257):

* the three theorem modules are restored byte-identically to their live text (base = live);
  their theorem signatures, published proofs and helper definitions are unchanged;
* `Sheaf.Paper.StrictEtaleExceptionalAdjointInterfaces`, `Sheaf.Paper.ExceptionalSystemInterfaces`
  and `Sheaf.Paper.SequenceAdjointShiftInterfaces` now publicly re-export the respective theorem
  module and add one transparent `abbrev` alias each (`StrictEtaleExceptionalAdjointInterface`,
  `ExceptionalSystemSiteComparisonInterface`, `PurSequenceAdjointShiftInterface`), which is the
  node's primary `lean.declaration`; every relocated name stays in `lean.declarations` of the
  owning definition node, so ownership is exactly as delivered;
* the item module, its record and its `stmt_deps` are unchanged: it imports the same three
  module names, which now expose the same declarations.

The delivered dependency records of the three theorem nodes keep only the theorem declarations;
that is consistent with the definition nodes owning the other names. Their `lean.note` still
describes the move; the maintainer may `--revert-nodes` them if the live records are preferred.

Compile (`nt_compile.py --json`, live build plus overlay): the three re-export modules 5.6 s,
6.1 s, 6.0 s and the unchanged item module 35.2 s, all clean (exit 0, no error or warning);
`ExceptionalSystemTransport` was taken as the cached live side override. `check_lean_text`
returns no finding for the three new records and the three dependency records.
