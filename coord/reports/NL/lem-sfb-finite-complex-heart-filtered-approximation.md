## Worker report

This delivery states `AlgebraicGeometry.ProEtale.finite_complex_heart_filtered_approximation`
in `Sheaf.Paper.FiniteComplexHeartFilteredApproximation` with one whole-proof `sorry`.
It also defines the finite-complex stages and their filtered hull in
`Sheaf.Paper.FiniteConstructibleComplexHeartPresentations`. All definitions have explicit
formula bodies; no construction is selected from an unproved existence statement.
The item's accepted natural-language statement and proof are preserved.

The inherited BLOCKED ending concerned reopening a stage-1 split. The current node has
status `split`, an independent stage-1 review and no Lean record; `coord/queue.tsv` lists
it at stage 2. The stage-handoff paragraph of `coord/brief-stage2.md` explicitly permits
this statement delivery. No repair note for this item was present.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient object is a condensed abelian
  sheaf `Λ` on `coherentTopology Profinite.{u}`, with `[MonObj Λ] [IsCommMonObj Λ]`.
- `hΛ` has exactly six alternatives: a finite discrete commutative ring `A` annihilated
  by some `ℓ ^ n`; `continuousMapRingObj ℤ_[ℓ]`; `padicIntegersRingObj ℓ E`;
  `continuousMapRingObj ℚ_[ℓ]`; `continuousMapRingObj E` for a
  `PadicAlgCl.FiniteIntermediateField ℓ`; and `continuousMapRingObj (PadicAlgCl ℓ)`.
  The isomorphisms are in monoid objects of abelian sheaves, preserving the ring
  operations. Finite rings can be represented in `Type 0` without losing an isomorphism
  class. The topology on each nonfinite coefficient is the existing induced norm
  topology; the algebraic-closure alternative uses every continuous function.
  The fixed closure is `PadicAlgCl ℓ`; the existential finite intermediate field encodes
  exactly the permitted finite subextensions. The separate fixed A and E in the prose
  do not occur outside their respective alternatives.
- `X : Scheme.{u}` with `[IsAffine X] [IsLocallyNoetherian X] [CompactSpace X]` is exactly
  an affine Noetherian scheme in the node's expressly stated locally-Noetherian plus
  quasi-compact sense. No characteristic, field, dimension or invertibility binder occurs.
- `Scheme.ProEt.topology X` is the recorded small pro-etale site, and
  `condensedRingObj Λ X` is the recorded pullback coefficient ring. The ambient category
  throughout is `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  The etale-site dependency fixes the background site convention and imposes no further
  hypothesis on X. The theorem does not need a new etale construction.
- `IsFiniteConstantConstructibleComplex Λ X K` requires `K : CochainComplex ... ℤ`,
  a finite support `s : Finset ℤ` outside which `IsZero (K.X n)`, and
  `∀ n, IsConstantModelConstructible Λ X (K.X n)`. The cochain-complex structure
  contains the actual arbitrary module maps and the differential-square-zero identity;
  no common scalar matrix is required.
- `K.homology 0` is the actual abelian-category quotient ker(d^0)/im(d^-1).
  `finiteConstructibleComplexHearts` is its isomorphism closure. There is no hypothesis
  that this cohomology module is constructible.
- `(c : ℕ)` is the nonnegative integer bound. `hcd` quantifies over every such K, every
  `U : X.ProEt` with `[IsAffine U.left]`, and every integer `q` with `(c : ℤ) < q`.
  It pulls `K.homology 0` back by `(CondensedRing.upperStar Λ U.hom).obj`, inserts that
  module in degree zero with `DerivedCategory.singleFunctor`, applies
  `(condensedModuleSections Λ U.left).rightDerivedFunctor`, and asserts that its
  degree-q abelian-group cohomology is `IsZero`. This is actual module-derived sections,
  rather than the derived functor on abelian sheaves applied after forgetting modules.
- `indFiniteConstructibleComplexHearts` is literally Mathlib's `ObjectProperty.ind.{u + 1}`
  of the finite-stage property. `ind` supplies a small filtered category, a module
  diagram and a colimit presentation with the given module as vertex. Its maps are
  arbitrary ambient module maps and need not arise from chain maps. Both the finite
  stages and the hull are replete, by the explicit isomorphism condition and Mathlib's
  `ObjectProperty.ind` isomorphism-closure instance.
- The first conclusion is `.ContainsZero`; because the property is replete this includes
  every zero module. The second is `IsConstantModelConstructible Λ X ≤
  indFiniteConstructibleComplexHearts Λ X`, containing every member of C_X.
- `.IsClosedUnderKernels` and `.IsClosedUnderCokernels` quantify over all maps between
  members, with kernels and cokernels in the ambient module category.
- `.IsClosedUnderExtensions` means every ambient `ShortComplex.ShortExact` whose end
  objects satisfy the property has its middle object satisfying the property. It imposes
  no finite-stage extension data or prior lift.
- `∀ I : Type (u + 1), ...IsClosedUnderColimitsOfShape (Discrete I)` is all small ambient
  coproducts, including the empty family. Every resulting membership is in the same
  `ObjectProperty.ind.{u + 1}` with the same indexing universe. No closure under other
  colimits is added to the conclusion.
- All derived categories and functors are the ordinary uncompleted ones already supplied
  by the dependencies. No completeness or finite-subextension-valued condition appears.

Dependency declarations read and used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients` supplies the
  coefficient constructions. Its recorded predicate `IsLocalizingAdmissibleCoefficient`
  now also includes `Profinite.padicAlgClRingObj`. It cannot express exactly the six
  alternatives required here, so `hΛ` explicitly selects the six continuous cases, as
  the already-landed `FiniteConstructibleComplexHeartCd` statement does. This does not
  redefine any coefficient object or admissibility predicate, and needs no dependency
  repair: the recorded localizing closure notion itself is not used by this theorem.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-etale-site`: Mathlib `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `def-weil-pbc-proetale-site`: Mathlib `Scheme.ProEt`, its `.topology`, and `.mk`.
- `def-weil-size-convention`: universe convention; explicit `universe u`, sheaves in
  `Ab.{u + 1}`, and small filtered indexing categories in `Type (u + 1)`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`
  publicly exposes the canonical `CondensedRing.upperStar`, `Functor.rightDerivedFunctor`
  and ordinary derived-category machinery. The theorem uses those exact constructions.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`. Its full definition and
  finite scalar-model presentation were read, not replaced by the different upstream
  arbitrary-local-matrix constructibility notion.
- `def-pc-cochain-complex-modules`: Mathlib `CochainComplex` and `HomologicalComplex.homology`.
- `def-weil-pbc-category-colimit`: Mathlib `IsFiltered`, `ColimitPresentation`, colimits;
  used through `ObjectProperty.ind` in `Mathlib.CategoryTheory.ObjectProperty.Ind`.
- `pqf-def-locnoeth`: Mathlib `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: Mathlib `CompactSpace`.
- The existing definition node `def-sfb-condensed-module-sections` was added to stmt_deps:
  its recorded `AlgebraicGeometry.ProEtale.condensedModuleSections`, in
  `Sheaf.Paper.CondensedQcqsPushforwardContinuity`, is exactly the required sections
  functor. Its body is `Mod.forget ⋙ sheafToPresheaf ⋙ evaluation` at the identity object.
  No new definition or continuity hypothesis is introduced.

The available proof dependencies are imported without `public`:
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` and
`Mathlib.Algebra.Category.ModuleCat.AB` for small-site module-sheaf Grothendieckness;
`Sheaf.CategoryTheory.SheafTensor` for `sfbSheafTensor_properties`; and
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` for
`CategoryTheory.Mod.isGrothendieckAbelian`. The proof-only nodes
`lem-sfb-noetherian-scalar-constructible-heart`,
`lem-sfb-noetherian-scalar-constructible-fp2` and `lem-sfb-fp2-ind-realization` currently
have neither Lean records nor Mathlib matches, so no nonexistent module is imported.
They are proof prerequisites, not missing notions needed to state this theorem. The
four-step node proof is included in the theorem docstring, including its observation
that the local bound is unused after the Noetherian repair.

Edge cases checked before writing: finite support may be empty, so the zero complex is
allowed; no nonzero ring assumption excludes the zero coefficient ring; no Nonempty or
Nontrivial hypothesis excludes the empty scheme; `c = 0` is allowed and q ranges over
all integers above c; arbitrary maps and ambient extensions are allowed; small filtered
categories are nonempty by `IsFiltered`, whereas the asserted coproduct index may be
empty. There is no restriction on geometric characteristic or on the lengths of the
finite complexes. The bound quantifies over every affine pro-etale test object,
including the identity, and does not assume it Noetherian or of finite type over a field.

Searches (all made through the prescribed tools or read-only rg):

- `msearch.py leanfinder` with "Filtered colimits of zeroth cohomology of bounded
  constructible complexes of pro etale modules are closed under kernels cokernels
  extensions and coproducts": 8 ambient condensed category hits, no matching theorem.
- `msearch.py loogle` with `CategoryTheory.ObjectProperty, CategoryTheory.IsFiltered`:
  2 hits, including `ObjectProperty.of_essentiallySmall_index`; its source led to the
  existing `ObjectProperty.ind`, which is reused verbatim.
- `msearch.py grep` with `IsClosedUnderFilteredColimits|filteredColimitClosure`: 0 hits.
- `msearch.py leansearch` with "Small filtered colimits of zeroth cohomology of finite
  complexes of constructible sheaves": 8 general complex/sheaf/colimit hits, no match.
- `msearch.py grep` with
  `finiteConstructibleComplexHeart|finiteConstantConstructibleComplex|IndFiniteComplexHeart`:
  0 hits. The same rg on `lean/WeilConjectures` and `lean/Sheaf` had no hits.
- rg for the item id on `lean/WeilConjectures` found no declaration; in `lean/Sheaf` it
  found only the proof-plan reference in `TorsionCdTopologicalSerreTransfer`.
- DAG text search found the stronger unstated theorem
  `lem-sfb-qcqs-finite-complex-heart-filtered-closure`, but no definition node owning this
  finite-complex presentation property. Existing ind-constructible kernel/cokernel and
  extension modules concern different coefficient or geometric hypotheses and cannot
  supply the item's exact statement.
- `tools/blueprint_refs.py search 'finite constructible complex'`: 0 matching blueprint
  nodes. `ancestor` reports `det-sf-comp-coherence-cocycle`, used for the new node record.

No new statement dispute or correction is introduced. The current stage-1 split already
records the failure of the former arbitrary-affine assertion and its Noetherian repair;
this delivery retains that repaired statement. The item source's WANTED full-generality
reference remains WANTED; this is a statement-only delivery, not a proof of that claim.

Validation: prescribed `scompile.py` compiled both files separately, both in sandbox
module mode and as their actual library modules. No errors or warnings were printed;
reported library times were 8.8 seconds for the definition module and 6.4 seconds for
the theorem module, within the unchanged 60-second limit. Dry-run result recorded below.

## New nodes

`def-sfb-finite-constructible-complex-heart-presentations` owns
`IsFiniteConstantConstructibleComplex`, `finiteConstructibleComplexHearts` and
`indFiniteConstructibleComplexHearts`. It introduces exactly the finite-stage and
filtered-presentation classes defined in the item's prose, grounded in the current
blueprint's filtered-colimit heart construction. The three search kinds and the DAG,
blueprint and project searches above found no existing definition of these particular
classes. It reuses the dependency constructibility predicate, Mathlib complexes and
homology, and `ObjectProperty.ind`; no separate filtered-colimit definition is invented.
It makes no claim that the hearts themselves are constructible, and contains no theorem
or sorry. The item adds this new node and the existing module-sections definition to
stmt_deps; no dependency node is edited.

Dry-run repair: the current server schema additionally requires `import_flags` on new
node files (the 2026-10-23 tool update). Added `import_flags: []`; no mathematical
statement or Lean declaration changed.

Final dry run: `deliver2.py NL lem-sfb-finite-complex-heart-filtered-approximation --no-push`
printed `OK (dry run): commit 072274796ea passes the preflight and compiles; nothing pushed`.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
