## Worker report

Q94 states `lem-sf-exceptional-reduction-transition-comparison` in
`lean/Sheaf/Paper/SfExceptionalReductionTransitions.lean`, namespace
`WeilConjectures.SfExceptionalReduction`. The main declaration is
`exceptionalReductionTransitionComparison`. The node's mathematical statement
has not changed. Every theorem proof in the item module is `sorry`; every definition has actual data.
Existing dependency proofs are retained unchanged.
The auxiliary quotient-law and scalar-mate theorems state the corresponding
clauses of this same node's seven-step proof, with source and proof docstrings.
This repair adds one existing-definition node and one public import to the
existing fixed-scalar dependency module; see the sections below.

The source read was the current blueprint,
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`,
Integral stage, especially the reduction of the open unit, the finite supported
triangles, Q_n = Ri_n^! K_n, and the concluding adjunction/counit paragraph. The
node's expanded seven-step proof specifies the additional transition equations.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Prime l invertible in k | Section parameter `(l : ℕ) [Fact l.Prime]`, main binder `hl : IsUnit (l : k)` |
| Finite E/Q_l, valuation ring, uniformizer, positive quotients | Section parameters `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the recorded `Padic.coefficientExtensionIdeal` and `Padic.coefficientExtensionRing`. Index n denotes exponent n+1, covering every positive exponent, including exponent 1. The uniformizer is the recorded coefficient datum's fixed uniformizer, not a new one. |
| X separated finite type over k | `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`, `[IsSeparated (X ↘ Spec (.of k))]`, `[LocallyOfFiniteType ...] [QuasiCompact ...]` |
| Closed i and complementary open j | `i : Z ⟶ X`, `j : U ⟶ X`, `[IsClosedImmersion i] [IsOpenImmersion j]`, `hij : IsCompl (Set.range i) (Set.range j)` |
| Original small pro-etale sites | All `scalarReductionSource.{u,u}`, `scalarReductionTarget.{u,u}` and `proEtaleDerivedCategory` endpoints use the recorded site: objects in u+1, morphisms in u, coefficient/module carriers in u+1. In particular the site universes are not equated. |
| Completed B_T and finite A_n sheaves | Existing `completedIntegralCommRingProjectionUnrestricted`, `integralCoefficientCommRingSheaf`; `quotient` is the sheafified quotient ring map, not an additional ring. |
| D^b_c(T,R) | Existing `sfIntegralConstructible` and its full subcategory `sfIntegralConstructibleCategory`; `inclusion` is only an abbreviation for its inclusion. |
| D^b_c(T,A_n) | Existing `intrinsicFiniteTorsionConstructible l E (n+1) (Nat.succ_pos n) T`, on the original ambient derived category. |
| Ordinary completed and finite kernel right adjoints | `Presentation.JR`, `Presentation.Jn`, with `aR : sfCompletedDerivedDirectImage l E i ⊣ JR` and `an n : finiteImage l E i n ⊣ Jn n`. This is an adjunction presentation of those actual right adjoints: a right adjoint of the fixed direct image, together with its counit, is unique up to its unique counit-compatible isomorphism. Thus specializing to the recorded kernel construction gives exactly the stated objects; no exceptional map or extra choice of transition is an input. |
| Open inverse image and its actual units | `Presentation.P`, `aOpen : P ⊣ sfCompletedDerivedDirectImage l E j`, and `aFiniteOpen n : finitePull l E j n ⊣ finiteImage l E j n`. `finitePull` abbreviates the recorded `finiteDerivedPullback`. The completed left adjoint is similarly specified by the fixed right adjoint and its adjunction. |
| Ambient supported triangles restrict | `preservesJR`, `preservesP`, `preservesIntegralClosed`, `preservesIntegralOpen`, `preservesFiniteClosed`, `preservesFiniteOpen`, `preservesFiniteExceptional`, `preservesFinitePull` assert the constructible restrictions. `boundaryR`, `triangleR`, `boundaryN`, `triangleN` give the supported triangles with precisely the actual adjunction counit and unit as the first two arrows. |
| Canonical ordinary/completed operation comparisons | `closedComparison`, `openComparison`, `pullComparison` assert invertibility on the stipulated domains of the *defined* canonical transformations `directReduction` and `pullMate`. Those transformations are constructed using the normalized recorded restriction comparison and scalar-extension adjunction; they are not supplied as arbitrary isomorphisms. |
| Reduction T and K_n | `reduce` abbreviates `scalarReductionDerivedExtension`; K_n is `(reduce l E X n).obj K.obj`. No alternative tensor operation is defined. |

`Presentation` packages exactly these operation and supported-triangle hypotheses
so they need not be repeated in every formula. In particular it does not assume
invertibility of alpha, transition commutation, or any finite-to-finite tensor
boundedness statement. Specifying adjunction presentations rather than committing
to resolution representatives is necessary because the kernel theorem's ringed
presentation uses pulled-back ring sheaves; the node assumes the canonical
ordinary/completed identifications. All formulas are invariant under the unique
adjunction-compatible identifications with that presentation.

### Conclusions and canonical arrows

| Node clause | Lean rendering |
| --- | --- |
| Direct/pull reduction carries integral open unit to finite unit | Second main conjunction: `(reduce ...).map (S.aOpen.unit.app K.obj) ≫ openComponent S n K = (S.aFiniteOpen n).unit.app ...`. `openComponent` is the direct comparison followed by direct image of the inverse pullback mate. |
| Natural alpha_n | `alphaOf S n` is an actual `NatTrans`, constructed by the whiskered adjunction Hom equivalence from the reduced integral counit and the inverse closed comparison. First conjunction asserts `IsIso (alphaOf S n)`, hence an isomorphism of functors, not just objectwise nonempty isomorphisms. |
| Exceptional counit preservation | `PreservesCounit S n K ((alphaOf S n).app K)` in the third conjunction. The predicate spells out the equation with `closedComponent` followed by the finite counit equal to reduction of the integral counit. |
| Unique characterization | For every candidate b of exactly the required type, `PreservesCounit ... b ↔ b = (alphaOf S n).app K`. The natural arrow is defined before asserting its invertibility. |
| Equivalent triangle characterization | Same conjunction: `PreservesCounit ... b ↔ ExtendsTriangles ... b`. `ExtendsTriangles` asks for an actual `TriangleMorphism` from `reducedTriangle` to `finiteTriangle`, with the prescribed closed component, identity middle component, and `openComponent` as its third component. `reducedTriangle` uses `mapTriangle` and the shift structure supplied by the universal derived extension. Thus all three squares, including the boundary square, are required. After the canonical comparisons, the open component is the identity too. |
| Canonical q_mn | `transition l E T h`, not an arbitrary map. This is the scalar-adjunction transpose of the smaller reduction unit, using the projection relation and the identity-on-sections restriction compositor. This is the universal scalar-extension description of the quotient of a K-flat representative. |
| Canonical restriction comparison d_mn | `restrictionMate` is the mate of `finiteImageRestriction`. Its inverse is d_mn. `restrictionMate_isIso` asserts the Hom-chain/Yoneda isomorphism of Step 4; its docstring gives the normalization argument. |
| Definition of t_mn | `t` is `exceptionalTransition`: apply J_m to q_mn, then the inverse restriction mate. By naturality of the closed counit, J_m(q_mn) is exactly the transpose of q_mn composed with the finite counit. Every map and functor in this formula is specified. |
| Alpha intertwines transitions | Fourth conjunction equates `(alphaOf S m).app K ≫ (t S hij h).app K.obj` with `(transition l E Z h).app (S.JR.obj K.obj) ≫ (restrict l E Z h).map ((alphaOf S n).app K)`. Both are A_m-linear morphisms with precisely the same endpoints. |
| Three-index cocycle | Fifth conjunction: the t_rm composite with restriction of t_mn and the canonical `restrictComp` equals t_rn. This takes place with A_r coefficients. |
| Equal-index identity | Sixth conjunction: t_nn followed by `restrictId` equals the identity. Both restriction and its identification with identity are explicit. |
| Natural derived equalities and coefficient actions retained | Alpha, q and t are defined as natural transformations. Their displayed component equalities quantify over every object of the full integral constructible category; by natural-transformation extensionality these are precisely equalities between the corresponding natural transformations. The targets are the finite derived categories with `restrict` explicitly present, never their forgotten underlying integral objects. |
| No arbitrary finite tensor boundedness | No functor from all bounded constructible A_m complexes to bounded constructible A_n complexes, and no such preservation hypothesis or conclusion, occurs. `restrict` is exact scalar restriction on the ambient categories. |

### Dependencies and searches

The dependency node records and signatures/docstrings were read. The construction
uses the following existing declarations, rather than private replacements:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, together with the existing valuation ring, uniformizer, ideals and quotient rings it imports.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its imported completion construction: the recorded constant-to-completion cone, `completedIntegralCommRingSheafUnrestricted`, its projections, and `integralCoefficientCommRingSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`: `ringedSupportKernel`, `ringedClosedKernelShriek`, `proEtale_ringed_closed_kernel_adjoint`. Its normalized derived adjunction identifies the right-adjoint presentations used here with the actual kernel functors.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`: `scalarReductionDerivedExtension`, `scalarReductionDerivedExistence`, `derivedScalarExtensionRestrictionAdjunction`. The last has an existential *normalized* adjunction, whose witness fixes the reduction units used in q and the direct comparison.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`, `sfDerivedRestrictionComparison`; `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`: `proEtaleConstantDerivedDirectImage`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`, used verbatim through the `finitePull` abbreviation. Its intrinsic ordinary inverse image is transported from the fixed-scalar presentation by the existing realization equivalence.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`; `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: `SheafOfModules.sheafRingDerivedCoefficientAdjunction`.
- `Sheaf.CategoryTheory.DerivedCoefficientSequenceRealization`: `derivedRestriction`, `comparison`, `derivedIdentity`. The module explicitly specifies their site, morphism, coefficient, and derived universes, namely `u+1,u,u+1,u+2`. The new existing-definition node `def-sf-derived-scalar-restriction-compositors` records precisely the six definitions used here. The sequence-realization theorem remains a proof dependency, not a statement dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`: `proEtaleDerivedDirectImage_restrictScalars`, the intrinsic constant-ring form of the normalized scalar square. The existing owning node `lem-weil-proetale-direct-image-restriction-of-scalars` was also added to `stmt_deps`. The dependency record preserves every live field and appends six intrinsic names to `lean.declarations`. The fixed-scalar module publicly imports the unchanged intrinsic module, as requested by R2′.
- `CategoryTheory.mateEquiv`, whiskered adjunctions, `Triangle.mk`, `Functor.mapTriangle`, `TriangleMorphism`, distinguished triangles, and Yoneda are Mathlib declarations.

The fixed-coefficient `AlgebraicGeometry.ProEtale.derivedTensor` in the recorded
upstream tensor module was read. It is not redefined: the actual reduction is the
recorded scalar extension, as required for the completed source ring. The scheme
morphism dependency is a convention node; its `lean` correctly has no declaration.
The Mathlib-status dependencies are read via their `mathlib_match` declarations,
including the triangle-morphism isomorphism lemmas and Yoneda full faithfulness.
The stated proof-dependency modules are imported. The proof dependency
`lem-sf-integral-ordinary-recollement-realization` currently has no Lean record;
this file does not call it or invent a substitute, since its result is explicitly
assumed in this node's own hypotheses. It remains the source of that hypothesis
when proving the parent theorem.

Searches actually run (the launcher log is `searches.jsonl`):

- `msearch.py ... leanfinder "Closed exceptional right adjoint derived reduction counit quotient transition natural comparison"`: eight general derived-adjunction normalization hits, including `derived_counit` and `derivedε_fac_app`; none states this comparison and coherent tower.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv"`: zero hits from that query; the declarations were then read directly in Mathlib.
- `msearch.py ... grep "exceptional.*reduction|reduction.*exceptional"`: zero hits.
- `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for exceptional/reduction/transition and counit comparisons: generic mates, the scalar tools, and `SfLocalizationAllStages` were found. That parent module packages existential localization data and conjugated tower maps, not the present canonical counit-mate and quotient-transition identities.
- Node-id search in `lean/WeilConjectures` and `lean/Sheaf` found no existing declaration for the item. Namespace/declaration searches found no collision for the new names.

Edge cases checked: n=0 indexes A_1 (no A_0 case is introduced); h : n≤m
includes equality, with actual coefficient identity and derived restriction identity;
r=m or m=n is included in the cocycle; K=0; Z empty and U=X; U empty and Z=X.
No nonempty hypothesis, strict inequality, flatness of A_n over A_m, or
faithfulness of scalar forgetting is used. The quotient ideals have the correct
inclusion direction. The mate of the closed restriction square is the inverse of
d_mn, so t uses its inverse, with the A_m-linear endpoints checked by Lean.
The triple restriction compositor has direction Res_mn followed by Res_rm to
Res_rn, as required by the displayed equation. No statement dispute or node
correction was found.

Validation: `scompile.py Q94 lem-sf-exceptional-reduction-transition-comparison`
compiled the module in sandbox and library mode against the live build, with no
errors or warnings. Only the prescribed wrapper was used; no live source was
edited and no direct Git command was run.

## Second reading by Q94

This is the dispatched author's second reading, not a claim of an independent
worker review. The dispatch explicitly forbids starting other agents and reserves
the independent review to the maintainer. I reopened the node and final Lean file
and checked the hypothesis and conclusion correspondence above.

The second reading found and repaired: the class-valued shift definition needed
`@[instance_reducible]` for a warning-free compile; the finite inverse-image alias
needed to point directly to the recorded `finiteDerivedPullback`; and the bundled
constructible-restriction hypothesis needed to spell out finite closed/open images,
finite exceptional/pullback restrictions and integral images as well as JR and P.
I checked the boundary square is required by an actual triangle morphism, and that
no transition is a freely supplied field. The final equations include both equal
indices and the canonical third-level restriction compositor. The semantic node
statement is unchanged. The report records the added statement dependencies and the use of universal
adjunction presentations for the maintainer's independent assessment.


## New nodes

`def-sf-derived-scalar-restriction-compositors` is an `existing: true` definition
record on `Sheaf.CategoryTheory.DerivedCoefficientSequenceRealization`: `Modules`,
`restriction`, `ordinaryComparison`, `derivedRestriction`, `comparison`, and
`derivedIdentity`. The site, module and derived universes remain independent.
`Modules` takes the existing ringed-site category; `restriction` is Mathlib's
unchanged-underlying-sheaf restriction; `ordinaryComparison` is selected by its
unique identity-on-sections characterization; `derivedRestriction` localizes
termwise restriction; `comparison` composes the derived-composition comparison
with the localization of `ordinaryComparison`; `derivedIdentity` localizes the
identity comparison. The node asserts no sequence-realization or coherence
lemma. Its source is the scalar identifications in the Integral stage of
`prop-sf-localization-all-stages`, with the existing construction's Stacks
03CW/015F/04VG citations.

Searches: `blueprint_refs.py search 'restriction scalars composition'` returned
zero blueprint matches; `ancestor` returned `prop-sf-localization-all-stages`.
DAG searches read the sequence-realization node and the varying-ring operations,
normalized coefficient diagram and ringed projection restriction definitions;
none records this standalone scalar compositor. Searches of `lean/WeilConjectures`
and `lean/Sheaf/CategoryTheory` found the exact six existing definitions above,
so no Lean definition is added. The logged LeanSearch query about derived
restriction along composable sheaf ring maps returned eight constituent module
restriction hits. The logged LeanFinder query about a derived scalar compositor
returned eight constituent sheaf/module restriction hits. The logged grep query
`restrictScalarsComp|mapDerivedCategoryCompIso|mapDerivedCategoryIdIso`
returned twenty constituent Mathlib hits. None is the complete sheaf-ring
ordinary and derived comparison package; the existing project module supplies it.
The new node records these actual queries and results.

## Dependency modules

`lem-weil-proetale-direct-image-restriction-of-scalars`: R2′ preserves the live
Q50/H3 record exactly, including `module`, `declaration`, `file`, `statement`,
`branch`, `by`, `date`, `existing`, and `note`. Its sole record change appends six
intrinsic names to `lean.declarations`, after the original nine names. All fields
outside `lean` remain unchanged, including the passing `reviewed_proof` record.
The fixed-scalar module gains exactly one line:
`public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`.
Deleting that line yields current live server source, obtained with
`scompile.py --source` (whose printed output adds a final blank line).
No definition, signature, proof, attribute or option was changed. The intrinsic
module is not delivered or modified; its current server source is identical to
the local live copy. This exposes the canonical intrinsic comparison needed by
the consumer through the existing owning module without rebinding Q50's proved
theorem to a postponed theorem.

### Returned-record repair and second reading

R1 remains fixed: the statement dependency is the existing-definition node
`def-sf-derived-scalar-restriction-compositors`, with six definitions and no
postponed theorem. The sequence-realization theorem remains a proof dependency.

R3 remains fixed: `lem-weil-derived-scalar-extension-restriction-adjunction` is
in `stmt_deps` and its module is publicly imported. Its normalized adjunction
pins the unit on K-flat representatives. The intrinsic direct-image comparison
likewise retains its K-injective normalization.

R2′ is fixed by preserving the live record and reversing the previous import
change as specified above. I verified all original record values and the original
nine-name prefix against current main. The main item module and its signature
remain unchanged from the returned packet. I reread its six conclusion groups:
alpha is a natural isomorphism; the actual open unit is preserved; the counit
uniquely characterizes alpha equivalently to the specified triangle map; alpha
commutes with quotient transitions; transitions satisfy the three-index cocycle;
and equal-index transitions are identities. The hypothesis and edge-case tables
above still apply without a mathematical statement change.

### R2′ validation and delivery-tool fault

`scompile.py Q94 lem-sf-exceptional-reduction-transition-comparison` compiled
both delivered modules and `scratch/IntrinsicWithFixedImporters.lean` separately,
in dependency order. The fixed-scalar module passed library mode in 58.3 seconds;
the item passed in 25.4 seconds; the module-mode scratch import compatibility
probe passed in 3.5 seconds. No error or non-sorry warning occurred. A source
scan identified exactly the 12 live direct importers of the fixed-scalar module;
the scratch file imports all 12 together with the intrinsic module.

The prescribed `deliver2.py --no-push` compiles the packet, then fails server
preflight: existing theorems in the fixed-scalar module are rejected because
"the proof is not `sorry` (stage 2 states; every theorem and lemma ends with
`:= by sorry` or `:= sorry`)". Examples include
`fixedScalarRestrictionDirectImage_kInjective`, `restriction_mate_eq`, and
`simple_derived_mate_normalization`. These are existing landed stage-3 proofs,
unchanged from current main. The stage-2 text gate checks the entire module
and has no import-only-change exemption. Replacing those proofs with `sorry`
would violate the return's explicit requirement to preserve Q50's proved record
and the live module apart from the one import. The source and node repair and
requested compatibility validation are complete; delivery is blocked by that
preflight refusal. No launcher/tool file was edited or bypassed.


### Retry self-check, 2026-10-23

The required first dry run on the retained packet again failed server preflight
with the unchanged-stage-3-proof diagnostic quoted above. Current-main comparison
confirms that the dependency node differs only in `lean.declarations`, whose
original nine-name prefix is preserved and whose six appended names are precisely
the requested intrinsic names. Every other field, including `reviewed_proof`, is
unchanged. The fixed-scalar module differs from current main by exactly the one
required public import; every declaration and proof remains byte-identical.
The intrinsic module remains absent from the delivery and its current server
source, read using `scompile.py --source`, matches the local live source.

The current source scan still finds 12 direct importers, but the set changed:
`Sheaf.Paper.SfIntegralOrdinaryRecollementRealization` now replaces the former
`Sheaf.Paper.LocalizationScalarUnit`. The scratch module-mode probe was updated
to import exactly those 12 current modules and the intrinsic module. Set comparison
confirmed no current importer was missing and no unrelated importer was present.
`scompile.py Q94 lem-sf-exceptional-reduction-transition-comparison` compiled both
delivered modules and the updated probe cleanly. Library-mode times were 58.3 s
for the fixed-scalar module, 25.4 s for the item and 2.8 s for the updated probe;
the newly needed live importer compiled in the private overlay in 24.8 s.
No live file or launcher tool was edited, and no direct Git command was run.

The requested source and record repair is retained. The blocking failure is the
stage-2 preflight's refusal of existing, unchanged stage-3 proofs in an import-only
repair; replacing these proofs with `sorry` would contradict R2′. Tool modification
or bypass is expressly forbidden by the launcher brief.


### Final repair retry, 2026-10-23

The initial dry run on the retained packet reported two current metadata failures:
`lean.by is 'Q50', not 'Q94'` for the preserved dependency record, and missing
`import_flags` on the new definition node. I added `import_flags: []` to
`def-sf-derived-scalar-restriction-compositors`; no other mathematical or
provenance field was changed. The Q50 authorship remains exactly as the return
requires. The subsequent prescribed dry run passed server preflight and all
per-file compilation, producing dry-run commit `0234531ce8a`. The earlier
proof and authorship gate refusals documented above no longer block this packet;
no tool was edited or bypassed.

Current-main comparison again verifies that the fixed-scalar module differs by
exactly the requested public import and that the dependency record differs only
by the six appended intrinsic names, preserving all original names and all other
fields, including `by: Q50` and `reviewed_proof`. The main mathematical statement
is unchanged and its recorded signature is verbatim from the final Lean file.
No statement dependency was removed.

The live importer set has grown to 13: `Sheaf.Paper.LocalizationScalarUnit` is
present in addition to the previous 12. I updated the scratch compatibility probe
to import exactly these 13 modules together with the unchanged intrinsic module.
`scompile.py` compiled the changed fixed-scalar module, the item module, and this
probe separately, cleanly, with library-mode times of 58.3 s, 25.4 s, and 3.7 s.
The fixed-scalar source read using `scompile.py --source` matches current local
live source before the one requested import is added. The intrinsic module is
still neither changed nor included in the delivery. The clause and edge-case
correspondence above remains valid; this retry changes only the required new-node
metadata and the scratch import coverage.
