## Worker report

This delivery states `AlgebraicGeometry.WeilComplex.native_compact_projection_formula` in
`Sheaf.Paper.NativeCompactProjectionFormula`. It concerns the actual ordinary derived categories
of native pro-etale Weil sheaves, restricted to their bounded constructible full subcategories.
The only postponed theorem is this named item. The compactification scheme instances are
named instances using the existing composition instances, without new proofs. All helper definitions have real data; the
comparison record is a specification of canonical maps, with its existence in the theorem's
conclusion, never an input assumption.

Clause correspondence:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime distinct from the characteristic: `(l : ℕ) [Fact l.Prime]`
  `[Fact (ringChar k₀ ≠ l)]`. The existing coefficient sheaf uses `PadicAlgCl l`.
- Both schemes over the finite field: `Scheme.{u}` and their `Over (Spec (CommRingCat.of k₀))`
  instances. The map's `IsOver` instance asserts that it is a k₀-morphism.
- Separated finite-type schemes: `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  on each structure morphism. The same three classes on `f` express its separated finite type.
- Actual bounded constructible Weil complexes: `WeilComplex k₀ l X` and
  `WeilComplex k₀ l Y`, the full subcategories of `DerivedCategory (ProEtaleWeilSheaf ...)`.
  No replacement by fixed pairs in a derived category occurs.
- Actual chosen compact-support operation: `WeilComplex.derivedLowerShriek k₀ l f`.
  `nativeProjectionCompactification` expands to its exact chosen Nagata compactification with
  the same `hasCompactification_of_over` witness. This is not a newly chosen factorization.
- Actual module pullback: `WeilComplex.upperStar f`; the compositor is the localization of
  `ProEtaleWeilSheaf.upperStarCompIso` followed by the equality of the factorization with f.
- Derived tensor over B: `ProEtaleWeilSheaf.nativeDerivedTensor` from the recorded operations.
  `nativeConstructibleTensor` merely lifts this bifunctor through the full inclusion using
  `nativeDerivedTensor_mem_weilComplex`; it creates no alternative tensor.
- Left and right sides: `nativeCompactProjectionLeft` and `nativeCompactProjectionRight` are
  respectively `(Rf! × id) ⋙ tensor` and `(id × f*) ⋙ tensor ⋙ Rf!`.
- Natural isomorphism for every M and arbitrary derived T: `pi` is an isomorphism of these
  bifunctors, so both directions are morphisms in the bounded constructible category and their
  naturality holds for every pair of derived arrows. There is no lisse or degree-zero binder.
- Compactification projection, rather than an unspecified isomorphism: the last equation
  identifies `(pi.hom.app (M,T)).hom` with the proper projection mate, then `Rp*(gamma)`,
  then `Rp*j!(id tensor the balanced pullback compositor)`. `nativeProjectionProperMate`
  is defined using the actual derived counit and `Adjunction.homEquiv`.
- Canonical balanced comparison: `NativeProjectionTensorComparison` fixes its presentation’s sheaf carrier
  to the existing `ProEtale.adicUpperStarTensorLeftIso`, its total chain map on each actual
  coproduct insertion, and its derived map on every pair of K-flat representatives via the
  recorded `nativeDerivedTensor_models`. Hence no arbitrary natural isomorphism is assumed.
- Normalized open comparison: `s`, `d`, and `c` satisfy the existing
  `NativeOpenPresentationCompatibility`, including the existing sheaf-unit and localization
  normalization. These are conclusions of the theorem, not extra hypotheses.

Dependencies read and used:

- `WeilConjectures.WeilSheaf.LowerShriek`: `WeilComplex.derivedLowerShriek`,
  `ProEtaleWeilSheaf.rightDerivedLowerShriek`, the native category and object property,
  `WeilComplex.objectProperty_rightDerivedLowerShriek`, and triangulated/shift instances.
- `Sheaf.Paper.DerivedWeilOperations`: `ProEtaleWeilSheaf.nativeDerivedTensor`,
  `NativeIsKFlat`, `nativeTensorTotal`, and `nativeDerivedTensor_models`.
- `Sheaf.WeilSheaf.NativePullbackStarPreservation`:
  `WeilComplex.native_pullback_star_preservation`, identifying the actual restrictions.
- `Sheaf.Paper.NativeDerivedWeilTensorConstructible`:
  `WeilComplex.nativeDerivedTensor_mem_weilComplex`, used to define the restricted tensor.
- `Sheaf.Paper.NativeOpenDerivedTensor`: the `NativeOpenTensorData`,
  `NativeOpenDerivedTensorData`, `NativeOpenPresentationCompatibility`,
  `nativeOpenTensorInsertion`, `nativeOpenTensorModel`, and `nativeOpenPullComp` interfaces.
  The new definition node `def-sf-native-open-tensor-presentation-data` attaches these
  already-landed data declarations with `existing: true`. The existence theorem remains in
  proof_deps and is not a statement dependency.
- `WeilConjectures.WeilSheaf.Localization`:
  `ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction` with its actual derived counit.
- `WeilConjectures.WeilSheaf.UpperStarId`: `ProEtaleWeilSheaf.upperStarCongrIso`.
- The available remaining proof dependencies are imported privately, including
  `Sheaf.WeilSheaf.NativeBasicComparisons` and the recorded Mathlib proper, closed-immersion,
  finite-type, quasi-compactness, and separatedness modules. The proper-realization node has
  no recorded Lean module yet, so no fictitious import is inserted. Its theorem is cited
  in the proof docstring; the statement specifies the counit mate directly and does not
  depend on its interface.

Edge cases checked before writing: zero or acyclic M or T, empty X, empty Y (then X is empty),
f the identity, f proper with identity open factor, and f an open immersion. The unrestricted
K-flat representative specification permits unbounded representatives of bounded derived
objects. The total tensor retains the recorded Koszul differential. No cohomology-only
isomorphism is substituted for an actual derived-category isomorphism. The rank-zero complement
in the extension-by-zero proof handles the empty-open case. There is no characteristic or
additional Tor-amplitude assumption beyond the recorded finite field coefficient framework.

Searches:

- msearch LeanFinder: "Projection formula for compactly supported derived pushforward of
  arbitrary bounded constructible Weil complexes". Eight generic sheaf pushforward-composition
  hits; none states this formula.
- msearch Loogle: `"projectionFormula"`. Zero hits.
- msearch LeanSearch: "Projection formula tensor arbitrary bounded constructible derived Weil
  complexes". Eight generic homological tensor, homology, or scheme tensor hits; no match.
- msearch grep: `projectionFormula|derivedLowerShriek.*[Tt]ensor` in Mathlib CategoryTheory.
  Zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id, native projection, and
  projection formula names. Upstream `ProjectionFormulaLisse/LowerShriek.lean` states only
  the lisse sheaf degree-zero parameter. The generic `CompactSupportProjectionFormula` uses
  the other coefficient realization and does not state this native formula. The normalized
  open derived tensor interface exists and is reused, not copied.

The original mathematical statement and proof are unchanged. H2 of the return is repaired by
replacing the added theorem statement dependency with the new definition node described below.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q25

The dispatcher explicitly prohibited starting other agents, so this is a second reading by
this worker, not a claim of independent review. The maintainer performs the independent review.
I reopened the node and checked the scheme and coefficient binders, the arbitrary two Weil
complex inputs, the bifunctor source/target order, and the final ambient composite against the
three proof steps. The chosen compactification uses the exact witness in derivedLowerShriek.
The tensor inputs are ordered (left,right), matching nativeDerivedTensor, despite the ordinary
curried sheaf tensor taking its right parameter first. The proper normalization therefore uses
`adicUpperStarTensorLeftIso ... N.carrier` at `M.carrier`. The open comparison's gamma has
orientation `j!M tensor N -> j!(M tensor j*N)`, as required. The final compositor uses the
inverse of the factorization equality, so iterated pullback ends at f*. Naturality is the
NatIso naturality in the product category; restriction and both inverse identities occur in
WC^der itself. No hypothesis was added to T. The explicit open data interface is now recorded by a definition node in stmt_deps; the
existence theorem stays in proof_deps. No mathematical mismatch or source defect found.

Implementation check: the generic `ProjectionTensorPresentation` carries the same total-summand
and K-flat localization equations; `NativeProjectionTensorComparison.compatibility` identifies
every functor, representative model, K-flat predicate, and insertion map with the existing
native one. Its `sheaf_forget` fixes the ordinary balanced carrier. This presentation avoids
unfolding geometric pullback choices while typechecking the equation.

## New nodes

`def-sf-native-open-tensor-presentation-data` records the existing definitions in
`Sheaf.Paper.NativeOpenDerivedTensor`, with `existing: true` as expressly allowed by
brief-stage2 sections 1(A) and 5. Its primary declaration is
`AlgebraicGeometry.ProEtaleWeilSheaf.NativeOpenPresentationCompatibility`; its declarations
list contains the 22 plain definitions and structures and excludes `native_open_derived_tensor`.
This gives the data a definition-node record without duplicating definitions, moving a reviewed
live module, or changing the existing theorem node. The existing theorem node states existence
of these data, which is a different notion from defining their types. The ordinary ringed-site
`def-sf-open-tensor-representative-data` does not define the native equivariant data or their
heterogeneous compatibility with the actual native operations.

Clause correspondence for the new definition:

- The finite field, prime, characteristic and separated finite-type open binders are exactly
  the variable context of `NativeOpenTensorData`, `NativeOpenDerivedTensorData` and
  `NativeOpenPresentationCompatibility` in the existing module.
- `NativeOpenTensorData.adj`, `unit_forget`, `counit_forget`, `unit_iso` record the actual
  open adjunction. `sheafRestriction`, `restriction_forget`, `sheafGamma`, `sheaf_inverse`
  record its balanced tensor and unit-transpose equations. `extension_kflat` and
  `restriction_kflat` record the two preservation properties.
- `NativeOpenDerivedTensorData.gamma`, `restriction`, `inverse_unit`, `ordinary` give the
  two natural derived comparisons, exact-derived unit normalization and ordinary forgetting
  square. `OpenTensorForgetData` includes the ordinary restriction compatibility, ordinary
  gamma and its inverse-unit equation, and equality after forgetting.
- `OpenTensorPresentation` carries E, R, exactness and additivity, SA/SB, TA/TB, DA/DB,
  flatA/flatB, hE/hR, modelA/modelB, iA/iB, the three levels of open and restriction
  comparisons, summands, restriction_summands, restriction_model and model. Its generic
  A,B binders explicitly include the category, abelian and derived-category structures.
- `OpenTensorUnitNormalization`, `OpenTensorRepresentativeNormalization`,
  `OpenTensorRestrictionNormalization`, `OpenTensorForgetNormalization` and
  `OpenTensorSummandNormalization` are exactly the componentwise predicates stated.
- `NativeOpenPresentationCompatibility` HEq-pins E/R, SA/SB, TA/TB, DA/DB, flatA/flatB,
  modelA/modelB, iA/iB, sheafGamma/gamma and sheafRestriction/restriction. It asserts no
  existence. The main theorem quantifies s,d,c anew as part of its conclusion.
- `nativeOpenPull`, `nativeOpenExtension`, `nativeOpenPullComp`, `nativeOpenSheafTensor`,
  the four source/target abbreviations, `nativeOpenTensorInsertion`, `nativeOpenTensorModel`,
  `nativeOpenForgetExtension` and `nativeOpenForgetPull` are the existing auxiliary operations.
  Their data is unchanged. The compositor localizes `upperStarCompIso.symm` and the
  chosen models reuse `nativeDerivedTensor_models`.

Source: current blueprint fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection,
and Stacks 0E8I/0GL1/03D8, as in the existing module's docstrings. Searches for the new
node used msearch LeanSearch (8 unrelated zero-tensor/module hits), LeanFinder (8 generic
module/condensed tensor hits), and Mathlib grep (0 hits). Exact query/result records are in
the node. rg on WeilConjectures found no native presentation; rg on Sheaf found precisely
the existing definitions reused here. DAG grep found only their existence theorem, and
blueprint_refs.py search open tensor found 99 related nodes, none defining the native data.
blueprint_refs.py ancestor reported None; the existing root breadcrumb is retained.

The new definition was checked at zero and acyclic inputs, the empty open, and the identity
open: it only defines data and equations, without asserting existence for arbitrary functors.
Its ambient comparisons have arbitrary unbounded inputs. The same declarations, with their
full signatures and docstrings, were read again; no mathematical change or additional
hypothesis is introduced by the definition-node attachment.

## Returned delivery repair

H2 (immutable head 558d9a399801): the theorem node
`lem-sf-native-open-derived-tensor` is absent from the repaired item's stmt_deps. Its
proof_deps occurrence is retained verbatim. The new definition node supplies exactly the
plain data declarations named by the accepted Lean statement. The main module and theorem
signature are unchanged. Compared with current main, the item differs only in lean and the
addition of this new definition dependency; no mathematical statement, proof, other metadata,
or already-landed dependency node is changed.

Validation: scompile.py completed cleanly for NativeCompactProjectionFormula. The first
repair dry run passed preflight and compiled the two checked files. In the new definition
prose, the pullback compositor is written in mathematical composition order j* p*; its
existing Lean definition and the accepted theorem are unchanged. A final dry run follows.
