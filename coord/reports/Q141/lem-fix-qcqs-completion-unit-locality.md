## Worker report

The item is stated as `WeilConjectures.IntegralOnSlice.qcqsCompletionUnitLocality` in
`Sheaf.Paper.QcqsCompletionUnitLocality`. Its proof is `sorry`; no proof work was done.
The source statement is unchanged. There are no new definition nodes and no statement
correction. The independent-universe ordinary-pullback helpers belong to the item module and
are all listed in its lean.declarations. The live existing:true record of
`def-sf-ordinary-integral-pullback-construction` is preserved unchanged; its module
`Sheaf.Paper.OrdinaryCompletedIntegralPullback` is imported.

Hypothesis and clause correspondence:

* The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded Padic coefficient
  constructions supply the valuation ring, its chosen uniformizer, and the actual
  quotients, with Lean index `n` meaning exponent `n+1`; no exponent-zero quotient occurs.
* `T : Scheme.{t}`, `[CompactSpace T]`, `[QuasiSeparatedSpace T]` and
  `_hl : IsUnit (l : Γ(T, ⊤))` render exactly the qcqs scheme and invertibility hypothesis.
  There is no Noetherian, separated, finite-dimensional, boundedness or completeness
  hypothesis. Site size is objects in `t+1`, morphisms in `t`; coefficients and modules
  have size `max u (t+1)`, with independent `t` and `u` throughout.
* `D l E T none` is the recorded unbounded derived category of all module sheaves over
  the actual completed coefficient ring. `none` selects the global small pro-etale site.
  Its `ring`, `rings` and `Mod` preserve the original completed limit and module category.
* `completion l E T none` is the recorded strict reduction tower followed by the
  functorial product mapping fiber and resolving-class descent. Each level is ordinary
  scalar extension along the actual quotient projection followed by restriction of
  scalars. `tower` uses the recorded quotient transitions. `completionUnit` is the unique
  natural transformation normalized by `roosUnit`, whose chain formula is the quotient
  augmentation and zero shifted-product coordinate. The first conjunct asserts for
  EVERY `H` that THIS map is invertible iff `IsComplete ... H`, the recorded Roos condition.
* The second conjunct quantifies every qcqs `S` and `r : S ⟶ T`. Its disjunction is
  `WeaklyEtale r` or `IsClosedImmersion r ∧ IsCompact ((Set.range r.base)ᶜ)`; under the
  closed-immersion hypothesis the complement is open, so this is exactly the required
  quasi-compact open complement. The weakly etale maps are precisely the site objects.
* `PreservesFiniteLimits (ordinaryPull l E r)` and `PreservesFiniteColimits ...`
  assert exactness of ordinary module inverse image (the underlying pullback uses
  inverse image and scalar extension along the specified coefficient map).
  `IsIso (ordinaryCoefficientMap l E r)` identifies inverse-image completed coefficients
  with completed coefficients on S. The following equation at EVERY `n` fixes the finite
  projections using the constant-section quotient maps; no arbitrary ring identification
  is substituted. The ring inverse image is defined by its adjunction with actual
  sheaf direct image, transported through the small model when sizes require it.
* The quantified natural isomorphism `τ` is between the entire strict tower functors.
  Its naturality in ℕᵒᵖ identifies every quotient transition, not only isolated levels.
  Its displayed augmentation equation identifies the quotient maps. Each component
  is the finite scalar-extension comparison, with both sides restricted to B_S modules.
  `χ` is the natural comparison of their strict Roos complexes. The displayed first
  and second mapping-cocone coordinate equations specify its product action on BOTH
  coordinates. `hgood` records preservation of flat-term K-flat representatives.
* `α : completion ... ⋙ ordinaryDerivedPull ... ≅ ordinaryDerivedPull ... ⋙ completion ...`
  is the desired natural derived comparison. Its normalization on every good
  representative ties it to the SAME `χ`, using the actual universal derived counit
  and `completionComparison` on both sides. The next equation is precisely
  `r*η_H ≫ α_H = η_(r*H)`. Thus no arbitrary triangulated lift is used.
  The last clause of this conjunct asserts preservation of derived completeness under
  ordinary, uncompleted pullback for every H.
* The third conjunct quantifies the entire finite rooted binary tree: `Fin d`, schemes
  `V`, maps `toT`, root, parent, left and right children, edge maps, and leaf predicate.
  Root identification is an isomorphism to T. Parents precede nonroot vertices, every
  nonroot vertex is a child of its parent, and leaves have no children. Internal vertices
  have two distinct later children and compatible maps to T. These conditions encode
  a finite connected rooted binary tree, permitting a numbering in parent-first order.
  Each vertex is qcqs and locally closed (`IsImmersion (toT v)`). The edge conditions
  are a quasi-compact open immersion and closed immersion, disjoint with union all of V.
* `I : ∀ v, Type w` and `W : ∀ v, I v → (V v).ProEt` encode the chosen covering families.
  `w` is independent, and no finiteness of the cover family is imposed. The presieve
  of the structure maps to the terminal object belongs to `ProEt.precoverage`, the
  actual weakly-etale/fpqc covering notion. Compactness and quasi-separatedness of each
  domain, as well as the covering condition, are required only at nonempty leaves.
* For every H, the final pair of equivalences detects the isomorphism of the root unit
  by its images under ordinary pullback through the composite chart-to-root map,
  and detects root completeness by completeness of those same ordinary restrictions.
  `leaf v → Nonempty (V v) → ...` explicitly removes all conditions on empty leaves.
  The preceding canonical restriction comparisons identify these maps with the local
  completion units along every branch.

Dependency declarations used (no private copies of notions):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, reexporting
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, `coefficientExtensionTransition`.
* `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `QuasiSeparated` and
  `QuasiSeparatedSpace`; `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`,
  `ProEt.topology` and `ProEt.precoverage`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `integralConstantToCompletionOfUniverses`, reexporting
  `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheafSystem`,
  `integralCoefficientSheaf`, `integralCoefficientCommRingSheaf`, and their projections.
* `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`
  (the exact Mathlib `SheafOfModules`); `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` and `Qh`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars` (the general ring-sheaf interface).
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients` (public statement
  dependency for total tower limits; no false exact-product assumption is added to it).
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, the recorded
  `WeilConjectures.IntegralOnSlice.Site`, `ring`, `rings`, `Mod`, `D`, `Cx`, `level`,
  `transition`, `tower`, `augmentation`, `Good`, `qGood`, `roos`, `completion`,
  `completionComparison`, `roosUnit` and `completionUnit`.
* `Sheaf.Paper.DerivedCompleteOnSlices`, `IntegralOnSlice.IsComplete`, reexporting
  `IsDerivedCompleteUnrestricted`, whose global branch is precisely the existing
  Roos-triangle definition. The definition is not replaced by unit invertibility.
* `Sheaf.Paper.OrdinaryCompletedIntegralPullback` is the unchanged recorded
  definition-node module. It retains all 14 ordinaryIntegral declarations used by
  landed consumers. The independent-universe helpers in the item module supply: `ordinaryCompletedRingMap`, its finite-projection
  uniqueness, `ordinaryCoefficientMap`, `ordinaryPush`, `ordinaryPull`,
  `ordinaryAdjunction`, `ordinaryComplexPull`, `ordinaryQuotientAugmentation`,
  `ordinaryProductAugmentation`, and `ordinaryCompletionChain`.
  `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`,
  `SheafOfModules.ringedTopoiDerivedPullbackIndependent`, supplies the derived
  existence theorem used by `ordinaryPull_hasLeftDerived`; `ordinaryDerivedPull`
  is its universal total-left-derived construction and `ordinaryComplexCounit`
  its representative comparison. The constructibility theorem
  `ordinaryCompletedIntegralPullback` is not used by any helper or item statement;
  its module is imported to retain the definition node's existing interface.
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`,
  `Scheme.coefficientProEtaleDirectRingMap` supplies the independent-size constant map;
  `Scheme.proEtaleBaseChange` supplies the actual site functor.
* All stated proof-dependency modules are imported plainly, including exact product
  functor strict limits, localized module exactness, Koszul completeness and
  reconstruction, open--closed unbounded calculus, immersion and restriction limit
  preservation, ringed open--closed calculus, reduction pullback towers, countable
  products, weakly etale localization and finite constant-ring maps. The four Mathlib
  matches are imported from LocalProperties, ShortComplex.PreservesHomology,
  ModuleCat.Sheaf.Limits and DerivedCategory.HomologySequence respectively.

Edge cases checked before and after writing: empty T, H=0, arbitrary unbounded H,
identity weakly etale or closed map, empty source S, empty closed complement, n=0
meaning exponent one, one-vertex tree, empty open or closed children, empty leaves,
and arbitrary (possibly infinite) cover index types. A nonempty leaf cannot have an
empty actual covering family, whereas empty leaves require none. The tree numbering
introduces no geometric assumption: every finite rooted tree admits such a numbering.
The first and second cone coordinates are specified separately, avoiding projection-only
characterization of a derived map. There are no auto-bound implicit variables.

Searches for existing statements (all msearch results are in searches.jsonl):

* leanfinder: "canonical derived completion unit commutes with proetale restriction and
  finite open closed stratification" returned BDeRhamPlus, formal smoothness and ordinary
  adic-completion results, StandardEtalePair and Proj results; none states this item.
* leansearch: "A canonical derived completion unit is an isomorphism locally on a finite
  open closed stratification of a scheme" returned affine-scheme unit, CompHausLike,
  localization-monoidal, gluing, and uniform-space completion statements; no match.
* loogle: `"Derived", "complete"` returned zero hits.
* msearch grep: `completionUnit|RoosComplete` globally and
  `derived.?complet|completion.?unit|Roos` in CategoryTheory returned zero Mathlib hits.
* rg over `lean/WeilConjectures` and `lean/Sheaf` for completion units, Roos completeness,
  locality and this blueprint id found the existing recorded completion constructions,
  finite-coefficient completion units in different categories, and the consumer's proof
  citation in ConstructibleProjectiveChartRefinement; no statement of this qcqs result.
  Exact new declaration-name checks found no collisions in either source tree.

The source was read locally in literature/stacks-project/proetale.tex:
lemma-naive-completion (099M), lemma-closed-immersion-affines-apply (09BL), and
lemma-closed-immersion-complement-retrocompact-exact (09BM). The latter requires the
retrocompact complement, retained in the statement. The accepted node proof already
explains the strict-unit refinement and finite-tree assembly. No STATEMENT-DISPUTED
fault was found. Dependency-closure checks for the added existing nodes found no cycle.

## Returned finding H13 repaired

The return at immutable head 247ec85590ce identified that replacing the live Q69
existing:true lean record of `def-sf-ordinary-integral-pullback-construction` would
discard its 14 ordinaryIntegral declarations while landed citers still use them.
The saved packet initially passed deliver2.py --no-push (7b5cc4e1a0a); that mechanical
pass did not resolve this semantic ownership defect, so the requested repair was made.

The final packet makes no change to that dependency node. Its sandbox copy was first
restored byte-identically from the live repository, checked for equality, and then
removed from the packet to ensure delivery cannot replace the record. The existing
module `Sheaf.Paper.OrdinaryCompletedIntegralPullback` is imported publicly. The 22
independent-universe helpers previously in IntegralOrdinaryPullbackOfUniverses are
now declarations of `Sheaf.Paper.QcqsCompletionUnitLocality`, each with the item
blueprint id, and all listed in the item's lean.declarations. The old helper module
has been removed from the packet. There are no new nodes or dependency modules.

The item retains both `def-sf-ordinary-integral-pullback-construction` and
`lem-weil-pbc-ringed-topoi-derived-pullback` in stmt_deps. The source statement,
proof, proof_deps and reviewed theorem signature are unchanged. All helpers were
moved without changing their signatures or bodies. In particular,
ordinaryDerivedPull and ordinaryComplexCounit still use the existence conclusion
ordinaryPull_hasLeftDerived and the universal total-left-derived counit.

Helper clause correspondence (part of the item module):

* ordinaryRingPush and ordinaryRingInverse give actual sheaf direct image and its
  left adjoint, with independent site and coefficient universes.
* ordinaryFiniteRingMap is the constant-section finite coefficient map.
  ordinaryCompletedRingMap_existsUnique fixes every finite projection, and uniquely
  determines ordinaryCompletedRingMap. ordinaryCoefficientMap is its adjoint.
* ordinaryPush is sectionwise module pushforward with this completed action;
  ordinaryPull is its additive left adjoint, ordinaryAdjunction the specified
  adjunction, and ordinaryComplexPull its termwise complex functor.
* ordinaryPull_hasLeftDerived gives existence of the ordinary unbounded derived
  pullback. ordinaryDerivedPull uses that universal construction;
  ordinaryComplexCounit is its comparison on a cochain representative.
* ordinaryRoosEndomorphism uses the existing strict quotient tower's 1-s.
* ordinaryQuotientAugmentation_existsUnique fixes the augmentation on adjunction
  generators; completed linearity gives the b-tensor formula. Its target retains
  the actual quotient transitions. ordinaryProductAugmentation takes its product.
  ordinaryCompletionChain_condition is the named zero-composite obligation;
  ordinaryCompletionChain is the mapping-cocone lift with coordinates (quotients,0).
  Every definition has real data, with unique-characterization theorems where needed.

Consumer preservation was checked against the live dependency record. It retains
all 14 names, including ordinaryIntegralModulePull, ordinaryIntegralModuleAdjunction,
ordinaryIntegralPullComplex and ordinaryIntegralCompletionChain. Thus the landed
citers def-real-lisse-pullback-normalization, lem-tw-ordinary-pullback-stratified-models,
lem-tw-finite-projective-model-pullback, lem-coef-dual-formula-scalar-transpose,
def-sf-ordinary-integral-derived-pullback, lem-tw-integral-comparison-descent,
lem-tw-ordinary-completed-integral-pullback and lem-tw-integral-quotient-augmentation
retain exactly their existing declaration interface; none is edited.

## Second reading by Q141

Self-check by the repair worker; no other agent was started. Read the item, the
combined module and the unchanged live dependency record. The theorem text from
`theorem qcqsCompletionUnitLocality` through the end of the file was checked
byte-identical before and after relocating the helpers. The prime, finite extension,
independent scheme/coefficient universes, qcqs and invertibility hypotheses render
the first paragraph without additional geometric assumptions. The canonical unit
is the recorded zero-second-coordinate strict Roos unit. The first conjunct is
exactly its invertibility iff Roos completeness. The second conjunct retains exact
ordinary restriction, every finite coefficient projection, the natural strict-tower
comparison tau, both cone coordinates of chi, good-representative normalization of
alpha by the actual derived counit, the unit equation and completeness preservation.
The third conjunct retains the finite open--closed tree, arbitrary-universe pro-etale
leaf covers, and detection of both unit invertibility and completeness. These are
the clauses already accepted by the independent return; no signature change was made.

The H13 mismatch was ownership: the dependency record lost its existing declarations.
The repair preserves that record and publicly imports its module, while assigning
all independent-universe helpers to this item. The helper docstrings still give their
sources and full proof plans, now with this item's blueprint id. The recorded main
signature is verbatim from the file; declarations lists the 22 helpers and the theorem.

Edge cases rechecked: d=0 admits no root, a one-vertex tree is a leaf, empty leaves
impose no condition, T empty is allowed, the cover index universe w remains arbitrary,
identity and empty-source restrictions remain allowed, and no boundedness or
completeness is assumed for H. No statement correction or STATEMENT-DISPUTED flag
is required.

## Validation

The repaired single module passed scompile.py against the live published library:
sandbox probe 17.6 s, library module 13.3 s, no errors or unexpected warnings.
No local compiler, lake build or global build was run. The final deliver2.py dry-run
and delivery are recorded by the wrapper.
