## Worker report

Module: `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology`.
Main declaration: `AlgebraicGeometry.derivedPullback_topCohomology`.
The node's statement is unchanged. Four concrete helper constructions belong to the
comparison stated by this node; no new mathematical notion or separate DAG node is needed.
The only postponed proof is the main theorem, whose docstring contains all eight DAG steps.
The truncation projection and the counit/single evaluation are implemented generically
over abelian categories in this same module; their scheme specializations use precisely
the shared module categories. `derivedSingleComparisonOfCounit` is the explicit
counit evaluation followed by Qh of the termwise/single isomorphism. It supplies no
extra data, hypothesis or theorem and has no postponed proof. This keeps concrete
sheafification data from expanding repeatedly while the comparison is typechecked.

Clause-by-clause translation:

- Schemes and their arbitrary morphism: `{T S : Scheme.{u}} (g : T ⟶ S)`.
- Integer degree: `(n : ℤ)`, including negative degrees and zero.
- Arbitrary derived object: `(C : schemeDerivedCategory S)` with the shared
  `[∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u}
  (moduleRings X.toRingedSpace))]`. This chooses localizations and adds no geometric
  condition. Both universes are explicit and independent, as in the dependency APIs. The
  homology and single functors explicitly use universes `{w, u, u + 1}`; this
  fixes their existing object/morphism sizes without equating u and w.
- Vanishing above n: `(hC : C.IsLE n)`, equivalent to the displayed cohomology vanishing
  by `DerivedCategory.isLE_iff`.
- Standard top truncation: `derivedTopTruncationProjection n C hC`. It is the unique
  map to the single H^n(C) in degree n whose H^n is the inverse of the canonical
  single/cohomology identification. After that identification its H^n is identity.
  `DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE` proves uniqueness and
  existence for precisely these bounds. `Equiv.ofBijective` selects this uniquely
  determined morphism; this is not a choice of an arbitrary truncation or isomorphism.
- The normalized c_g,M: `pinnedModulePullbackComparisonAt g 0 M`. The body is exactly
  the counit/single-identification composite appearing in
  `IsDerivedModulePullbackComparison`, using the particular counit selected by
  `exists_derivedPullbackComposition`. This is the counit to which the selected
  derived adjunction is pinned. The dependency's adjunction-transpose formula identifies
  it with the ordinary tensor-pullback unit followed by the derived pushforward unit.
- The second arrow at general n: `pinnedModulePullbackComparisonAt g n M`, evaluated
  on the single module in degree n. These are concrete evaluations of one fixed counit.
  `exists_pinned_pullback_counit_shifts` identifies them with c_g,M[-n] using its
  compatible shift comparisons. Hence this writes exactly the canonical shift comparison
  in the node without introducing arbitrary shift data as a hypothesis.
- κ: `derivedPullbackTopCohomology g n C hC` is the explicit composite of H^n(Lg*τ),
  H^n of that degree-n counit evaluation, and the canonical single/cohomology iso.
- Upper vanishing after pullback: `∃ hbound : ((derivedPullback g).obj C).IsLE n`.
  This witness is a proof, and supplies precisely the already-concluded bound needed
  to type κ_h,Lg*C in the last clause; it adds no assumption.
- H^0(c_g,M) invertible: the first conjunct quantifies over every `M : S.Modules`
  and asserts `IsIso` of H^0 of the pinned comparison itself, without replacing it
  by any other map or asserting invertibility in the derived category.
- κ invertible: the next conjunct is `IsIso (derivedPullbackTopCohomology g n C hC)`.
- Naturality: the third conjunct quantifies over every D, proof `hD : D.IsLE n`,
  and arbitrary derived morphism `a : C ⟶ D`; its equation is H^n(Lg*a) ≫ κ_D =
  κ_C ≫ g*H^n(a), which is the node's formula in Lean composition order.
- Composition: the last conjunct quantifies over every `T'` and `h : T' ⟶ T`.
  On the left it first applies H^n of the specific comparison selected by
  `exists_derivedPullbackComposition` at C, then κ_(h≫g),C. The right side is
  κ_h,Lg*C followed by h*(κ_g,C) followed by
  `(tensorPullbackSectionComp h g).inv.app (H^n C)`.
  This inverse has the direction h*g* → (h≫g)* required by the statement.
  Its construction is the unique left-adjoint comparison for the section-normalized
  tensor adjunctions and the actual pushforward composition iso; it is not an arbitrary
  inhabitant of `nonempty_tensorPullbackComp`. Inserting H^n of derived composition
  on the left is the fully typed version of the node's phrase "under the canonical
  derived composition isomorphism".
- No lower bound, flatness, quasi-coherence or finite rank appears in the signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, `DerivedCategory.isLE_iff`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, `derivedPullback_spec`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, `nonempty_tensorPullbackId`,
  `nonempty_tensorPullbackComp` (the latter two are existence statements, so the actual
  composition map is taken from the normalized interface of the module-pullback node).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`; the underlying functor remains the upstream tensor construction.
- `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`:
  `AlgebraicGeometry.IsDerivedModulePullbackComparison` (its explicit counit formula).
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`:
  `AlgebraicGeometry.exists_derivedPullbackComposition`; the same selected counits and
  composition are used throughout, through `pinnedPullbackCounit`,
  `pinnedPullbackComposition` and `Scheme.Modules.canonicalTensorPullbackAdditive`.
  The additive family is instantiated inside the concrete definition, not hypothesized.

Proof imports retained as the DAG plan requires:
`WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
(`CochainComplex.exists_functorial_boundedAbove_flat_replacement`),
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
(`CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace`),
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
(`AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction`, transitively imported),
`WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts`
(`AlgebraicGeometry.exists_pinned_pullback_counit_shifts`, imported through composition shifts),
`WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts`
(`AlgebraicGeometry.pinnedPullbackComposition_commShift`),
`Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition`
(`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition`),
`WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`
(`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackMap`), and
`Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`
(`AlgebraicGeometry.Scheme.Modules.canonicalSingleAdjunctionTranspose`).
The abstract derived category dependency is Mathlib's `DerivedCategory`/`HasDerivedCategory`.
All are already stated; no dependency record needs changing.

Edge cases checked mathematically before writing:

- C=0 and H^n(C)=0: κ is a map between zero objects and the assertion remains valid.
- C=M[-n]: the top projection is identity after the single/cohomology identification,
  and κ reduces to the specified normalized H^0(c_g,M).
- Nonflat map Spec(Z/2) → Spec(Z) and M=Z/2: lower Tor may be nonzero. The theorem only
  asserts H^0(c) invertible, not c invertible; it therefore includes this case.
- Complexes unbounded below: no lower bound occurs anywhere in the constructions;
  the same-upper-bound flat replacement and cokernel calculation do not need one.
- Identity g or h: the same pinned comparisons and normalized composition are used;
  there is no exclusion or replacement by arbitrary lifts.
- Empty schemes and zero sheaves, arbitrary n including n<0: no nonempty, nonzero,
  natural-degree or positive-rank hypothesis excludes them.

Searches performed with the prescribed `msearch.py N9 <item>` wrapper:

- `leanfinder`: "For a bounded above derived complex the top cohomology of derived
  pullback is ordinary pullback of top cohomology". Eight unrelated homology and Ext
  hits (including CochainComplex.HomComplex and projective/injective resolution Ext);
  no total derived sheaf pullback top comparison.
- `loogle`: `"leftDerived", "homology"`. Zero hits.
- `grep`: `truncGE.*homology|homology.*truncGE` in `Algebra/Homology/DerivedCategory`.
  Zero hits for that spelling. Direct source reading found the needed inverse-Hom
  bijection in the upstream Mathlib extension instead.
- `leansearch`: "Top cohomology of total derived pullback of sheaf modules is ordinary
  pullback of highest cohomology". Eight ordinary sheaf/module pullback and adjunction
  hits; none is this derived statement.
- `rg` of the item id in `lean/WeilConjectures`: no hits.
- `rg` of top-cohomology/truncation/single-map concepts in Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: found generic truncation, single functors,
  ringed tensor cohomological bounds and the listed canonical pullback tools; none
  states this normalized top comparison with its naturality and composition.
- `rg` of all four proposed names in both project roots and
  `dag/lean_names_upstream.json`: no existing declaration.

Source read: `literature/stacks-project/derived.tex`, lemma-negative-vanishing
(Tag 05TC), and remark-truncation-distinguished-triangle (Tag 08J5).
The eight proof steps in the node were read, including the reviewed step 7 that pins
ordinary composition and identifies the single comparisons by adjunction transpose.
No statement dispute or source correction was necessary.

## Self-check

Checked the node against the complete module again. The dispatch brief explicitly
forbids starting another agent; the maintainer's independent review remains to follow.

Matched every binder and every conclusion as detailed above. Checked the order and
sources/targets of all three factors of κ and both sides of the composition formula.
The first compile exposed inference of the distinct `Scheme.Modules` category instance
in implicit cohomology arguments; made all those coefficient categories explicit instead
of changing any universe or hypothesis. Checked that the existential upper-bound proof is
a conclusion, and proof irrelevance makes it immaterial to the actual comparison.
Checked that only the cohomology of the single comparison is inverted by the assertion;
the comparison itself is never inverted. Checked that ordinary composition is normalized
by sections, and derived composition and all degree-n evaluations use one selected counit.
All definitions have explicit data; only the theorem has `sorry`.

Validation: the final module passed `scompile.py N9
lem-weil-pbc-derived-pullback-top-cohomology <module>` in both modes: sandbox 30.4 s,
library module 16.6 s, each under the unchanged 60 s limit. No errors or warnings.
The generic construction removes the previous timeout without splitting the file,
changing a mathematical hypothesis, or raising any compiler limit.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
