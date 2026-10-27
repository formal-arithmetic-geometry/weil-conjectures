## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCoverStackAlgebraic` defines the node's
`C_d` as `AlgebraicGeometry.finiteCoverStack` and states
`AlgebraicGeometry.finiteCoverStack_isAlgebraic`, with `sorry` as its only proof.
The helper contains actual data, with no choice of an unidentified object or new
copy of the finite-cover category. It wraps the existing Hilbert base projection.
Source read: `literature/stacks-project/criteria.tex`, Tag 05YQ,
`proposition-finite-hilbert-point`, including the preceding smooth groupoid and the
relative-Spec, full-faithfulness and unit-adapted-basis parts of its proof.

Hypotheses and clauses, individually:

- Arbitrary scheme S: the binder `(S : Scheme.{u})`, with explicit `universe u`.
  No separatedness, finiteness, Noetherian, nonemptiness or characteristic binder.
- The size convention is implemented by the universe-polymorphic scheme category,
  `Over S`, and the recorded `BasedCategory` and discrete-groupoid constructions.
  No unrelated smaller test-scheme universe is introduced.
- Integer d at least 1: `(d : ℕ+)`, the exact positive-integer interface of the
  recorded relative finite Hilbert category, coerced there to the degree in ℕ.
- The big fppf base category is `Over S`; its topology is the recorded
  `Scheme.fppfTopology.over S`, exported by the Hilbert dependency through
  `Sheaf.CategoryTheory.SiteStackification`. As in the source, the category is
  defined before imposing descent. The algebraic-stack predicate includes étale
  descent, exactly as specified by def-sfb-algebraic-moduli-stack; fppf descent
  is a proof input, not an added hypothesis or a replacement site.
- The discrete represented h_S is
  `discreteModuli (yoneda.obj (Over.mk (𝟙 S)))`. `Over.mk (𝟙 S)` is the terminal
  S-scheme. The discreteModuli construction uses the existing Yoneda
  costructured-arrow presentation, retaining objects rather than isomorphism classes.
- The identification C_d = H_d(id_{h_S}) is the definition of `finiteCoverStack`:
  `BasedCategory.ofFunctor (RelativeFiniteHilbert.base
  (F := BasedFunctor.id (discreteModuli (yoneda.obj (Over.mk (𝟙 S))))) (d := d))`.
  This is definitionally `RelativeFiniteHilbert.groupoid` at the same F and d
  whenever its stack-proof arguments are supplied. Those arguments are unused in
  its definition; using the recorded `base` avoids adding an h_S-stack hypothesis
  or a separate postponed theorem just to supply them.
- Finite locally free degree-d objects are exactly the existing
  `RelativeFiniteHilbert` fields `T`, `Z`, `p`, and
  `finite : p.left.IsFiniteLocallyFreeOfDegree d`. The latter is the upstream
  finite/flat/locally-finitely-presented predicate plus fibre-degree equality at
  every point. The additional y, x and comparison in the terminal represented
  groupoid carry only unique structural data, so the fibre category is precisely
  equivalent to the cover groupoid, including all automorphisms.
- Arrows above g are the existing `RelativeFiniteHilbert.Hom`, whose `cartesian`
  field is `IsPullback h A.p B.p g`. Its other fields are the unique arrows of h_S.
  Over an identity this cartesian square gives exactly a T-isomorphism of covers.
  It does not permit arbitrary non-cartesian maps or quotient arrows.
- Pullback is the recorded Hilbert scheme-base-change construction:
  `RelativeFiniteHilbert.pullback` has cover `Limits.pullback A.p g`, projection
  `Limits.pullback.snd A.p g`, and the actual cartesian `pullbackArrow`.
- The entire conclusion is
  `IsAlgebraicModuliStack (finiteCoverStack S d)`: the recorded étale-stack,
  algebraic-space-diagonal, and smooth-surjective-scheme-atlas predicate. The
  theorem asserts algebraicity, without incorrectly asserting smoothness over S.

Dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; exported by the public imports.
- def-weil-size-convention: metatheoretic convention, with null declaration/module;
  implemented by explicit universes, not a new Lean definition.
- def-pc-fppf-site: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`; the slice uses
  `GrothendieckTopology.over` as the recorded note specifies.
- def-pc-finite-locally-free:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `Scheme.Hom.IsFiniteLocallyFree` and `Scheme.Hom.IsFiniteLocallyFreeOfDegree`;
  used by the existing Hilbert object's `finite` field.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst` and `pullback.snd`;
  used by the recorded cartesian arrows and pullback operations.
- def-sfb-relative-finite-hilbert-groupoids:
  `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`,
  `AlgebraicGeometry.RelativeFiniteHilbert`, `.Hom`, `.base`, `.groupoid`,
  `.pullback` and `.pullbackArrow`. Read the full module and used `.base` directly.
- def-sfb-algebraic-moduli-stack:
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`, whose full definition was read.

Proof-only imports (the complete five-step proof plan is in the theorem docstring):
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`
(`AlgebraicGeometry.affine_morphism_relative_spec`),
`Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum`
(`AlgebraicGeometry.specMap_isFiniteLocallyFree_of_basis`),
`Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
(`AlgebraicGeometry.relative_spec_base_change`),
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
(`AlgebraicGeometry.finiteLocallyFree_structureSheaf_properties`), and
`Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`
(`CategoryTheory.Pseudofunctor.exists_groupoid_stackification_local_description`).
The finite-integral and fppf-site proof dependencies are already exported by the
statement imports. The algebraic-stack definition is a public statement import.
The three proof dependencies lem-sfb-unit-framed-algebra-smooth-groupoid,
lem-sfb-smooth-groupoid-fppf-quotient and lem-sfb-finite-hilbert-stack-descent
have no recorded Lean module on this base, so there is no module to import for them.
They are not missing objects needed to type the theorem. Their names remain in the
proof docstring and the unchanged DAG proof/proof_deps.

Edge cases checked before writing:

- d = 1 is included by ℕ+; the smooth-groupoid argument has trivial unit stabilizer
  and the unique rank-one unital algebra, consistent with algebraicity.
- d = 0 is excluded exactly as in the node, not by an accidental nonemptiness
  assumption on the cover. The unit-adapted-basis proof specifically uses d > 0.
- Empty S and empty test T remain allowed. Fibre-degree equality is vacuous over
  the empty scheme, and the unique empty cover is retained for every positive d.
- Nonreduced, positive-characteristic and non-Noetherian bases remain allowed.
  Only source/target of the presenting groupoid are claimed smooth; X/S need not be.
- Automorphisms and arbitrary base arrows are retained. The construction takes
  neither a skeleton of the fibres nor their sets of isomorphism classes.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Finite locally free covers of fixed positive degree
  form an algebraic stack"`: 8 hits, on scheme covers, finite morphisms, finite
  presentation of affine spaces, and locally finite type; no stack algebraicity.
- `msearch.py ... loogle '"AlgebraicGeometry", "Stack"'`: 0 hits.
- `msearch.py ... grep 'finiteCoverStack|finite_cover_stack|IsAlgebraicModuliStack'`:
  0 Mathlib hits.
- `msearch.py ... leansearch "The stack of finite locally free covers of degree d
  is algebraic"`: 8 scheme-cover and base-change hits, no matching stack statement.
- `rg -n 'finiteCoverStack|finite_cover_stack|lem-sfb-finite-cover-stack-algebraic'
  lean/WeilConjectures lean/Sheaf`: no hits before creating this module.
- `rg` on `IsAlgebraicModuliStack` and finite-cover/algebraicity patterns in both
  algebraic-geometry trees: the stack predicate and unrelated consumers exist;
  none states this theorem. `rg --files` located the recorded Hilbert and stack
  modules, whose full definitions were read rather than copied.

No new nodes, dependency repairs, statement corrections or statement disputes.
The only node delta is `lean`. The named finiteCoverStack definition merely
introduces C_d from this very node using the already recorded Hilbert category.
The prescribed scompile.py checked both sandbox and library module paths cleanly
(9.0 s and 5.8 s respectively). No global or direct local build was run.

## Second reading by NL

A separate final pass reopened the node and finished Lean file and followed the
Hilbert object, Hom, base and pullback definitions. S and its universe are explicit;
ℕ+ matches d ≥ 1; the identity is on h_S represented by the terminal Over object;
finite degree is the recorded fibre-degree predicate; arrows are cartesian squares,
so fibre arrows are T-isomorphisms. All terminal-groupoid data are unique, without
removing automorphisms of the covers. The conclusion is the exact recorded
algebraic-stack predicate, not smoothness of the stack over S. Using `.base` rather
than manufacturing stack proofs adds no hypothesis: unfolding `.groupoid` gives
this same BasedCategory. No missing clause or mismatch was found, and no statement
change was made. This is the dispatcher's single-worker delivery; the maintainer's
independent review remains the independent reading by another person/agent.
