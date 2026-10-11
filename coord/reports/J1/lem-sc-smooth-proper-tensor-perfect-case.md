## Worker report

Module: `lean/Sheaf/AlgebraicGeometry/SmoothProperTensorPerfectCase.lean`.
Declaration: `AlgebraicGeometry.smoothProper_tensor_perfect_case`.
This is one theorem, with `sorry` as its entire proof. There are no definitions,
private copies, local instances, local notation, or auto-bound variables. The
item's node changes only in `lean`; no statement correction or additional node
is needed. The declaration's docstring carries both proof steps of the node.

Source read: [Stacks Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T), Lemma
48.8.1 and its proof. The local `literature/stacks-project/duality.tex` is absent
on this machine, so the official page was opened. The lemma applies to the
right adjoint of pushforward, and its particular case with L = O_Y is this
node's comparison. The proper, Noetherian, finite-Tor-dimension specialization
in the node is retained, although the source proves the perfect-K assertion
more generally. The proof is the perfect-dual tensor-Hom chain, projection
formula, adjunction, and Yoneda. The canonical formula is the ordinary mate
of the projection formula, and the theorem spells out both adjunctions.

Hypothesis and clause correspondence:

- Schemes and the morphism: `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`.
- Noetherian schemes: `[IsNoetherian X] [IsNoetherian Y]`.
- Properness: `[IsProper f]`, with Mathlib's separated, universally closed,
  locally finite type definition; universal closedness also gives quasi-compactness.
- Perfectness of f in the precise pointwise sense stated by the node: `hTor`
  quantifies over every x, with a finite bound n independent of the test module,
  and says Tor_i(O_X,x, M) is zero for i > n. `ModuleCat.restrictScalars
  (f.stalkMap x).hom` supplies exactly the O_Y,f(x)-module structure on O_X,x.
  Over rings, this is the finite-flat-dimension criterion, equivalent to finite
  Tor dimension. No projective-finiteness requirement is imposed on this
  generally non-finite stalk module. The bound can vary with x, as in the node.
- The two derived categories: the shared `HasDerivedCategory` binders and
  `schemeDerivedCategory`; the extra binders over Y's opens are precisely
  those required by the recorded `Scheme.IsPerfect` definition. They are
  localization choices, not restrictions on the geometry or on K.
- Restricting Rf_* to D_QCoh: the existential witness `hRf` and the existing
  `ObjectProperty.lift` applied to the composite of the QCoh inclusion with
  `schemeDerivedDirectImage f`. This is not a replacement pushforward functor.
- The given right adjoint c: universally quantified
  `(c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)` and `adj`
  from that lifted Rf_* to c. No c is assumed to exist; the assertion applies
  to every c equipped with the right-adjunction data in the node.
- The perfect complex K: `(K : schemeDerivedQCohCategory Y)` and
  `Scheme.IsPerfect Y K.obj`. This uses the recorded definition, unchanged.
- Lf^*: the existing `derivedPullback f`, which is computed by the recorded
  K-flat construction. Derived tensor: the global
  `schemeDerivedTensorMonoidal` instance, with `⊗` and `◁`.
- O_Y: `𝟙_ (schemeDerivedCategory Y)`, the degree-zero structure sheaf, with
  its quasi-coherence witness `hO`; its QCoh object is `⟨𝟙_ _, hO⟩`.
- Source of the comparison: the full-subcategory object with ambient object
  `((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj`. Its
  quasi-coherence is supplied by the existential `hTensor` witness, for all
  quasi-coherent arguments. This is not a hypothesis added to the theorem.
- The canonical projection-formula isomorphism: `pf` has source
  `Rf_*(Lf^*K ⊗ c(O_Y))` and target `K ⊗ Rf_*c(O_Y)`. Its inverse is
  explicitly equated to `a.homEquiv` of the inverse monoidality isomorphism
  followed by `Lf^*K ◁ a.counit.app c(O_Y)`. This is exactly the defining
  projection-formula map; an arbitrary object isomorphism does not qualify.
- The arrow after the projection isomorphism: `pf.hom ≫ K.obj ◁
  (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom` tensors the c counit
  with K and then identifies K tensor O_Y with K.
- The comparison itself: `ObjectProperty.homMk` regards that composite as a
  QCoh morphism, and `adj.homEquiv` takes its mate from the stated source
  to c(K). The conclusion `IsIso` is about this morphism, not the existence
  of an unrelated isomorphism of its two objects.

Presentation data: the theorem concludes existence of the QCoh preservation
witnesses, of a strong monoidal structure on the existing Lf^*, and of the
existing pullback/direct-image functors' adjunction. It then states the
comparison assertion for every choice of that monoidal structure and
adjunction. These are not hypotheses on f or K. The canonical K-flat choices
are included. The assertion is independent of those presentation choices:
a strong monoidal Lf^* carries the evaluation/coevaluation of a perfect K
to a dual pair, and the two triangle identities give exactly the source's
Hom argument and its identification with the displayed mate. Changing
adjunction data conjugates the mates by natural isomorphisms. Consequently
this quantified form states invertibility of the canonical map without
introducing a private, unconstrained projection-formula isomorphism or
postponing the map itself with `sorry`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its locally
  affine locally ringed space fields and morphism category.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (extends `IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`, with their
  sheaf-of-modules carrier and full-subcategory signatures.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, the specialization of ringed-space derived
  module direct image; the full signature and docstring were read.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, using
  strictly perfect complexes on a covering and derived restriction.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback` and
  `exists_derivedPullback`; the functor comes from the left-derived universal
  property and K-flat computation, rather than Mathlib's other pullback.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and
  `IsKFlatResolution`, read in full; they occur in the construction imported
  through DerivedPullback, so there is no redundant direct import here.
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeDerivedTensorMonoidal`, the global K-flat monoidal structure.
  This existing notion is used directly, without creating another definition.
- Mathlib `Tor'`, `ModuleCat.restrictScalars`, `Functor.Monoidal.μIso`,
  `Adjunction.homEquiv`, `ObjectProperty.lift`, `ObjectProperty.homMk`:
  signatures read from the pinned Mathlib source. ModuleCat monoidal and
  projective imports provide the instances needed by Tor'.

The proof-dependency record for `lem-pc-projection-formula` names the source's
`Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`, which
only handles invertible-module twists of higher direct images. It is not
one of this item's statement dependencies. The theorem does not misuse that
restricted signature: its projection map is written from the monoidal
pullback adjunction, and its invertibility is part of the existential `pf`
conclusion. The generic projection formula remains a stage-3 proof step.
The already landed `perfect_tensor_hom_duality` was also read to check the
proof interface and universe conventions, but need not be imported to state
this theorem.

Edge cases checked mathematically before writing:

- K = 0: the comparison is the unique map between zero objects; both
  pullback and right adjoints preserve zero. No nonzero assumption occurs.
- K = O_Y: the unit coherence and adjunction triangle identities identify
  the comparison with the unit identification on c(O_Y).
- The empty X or Y: all pointwise Tor/perfect conditions have their proper
  vacuous meaning; the derived QCoh categories are zero categories. Nothing
  assumes a point, nonemptiness, positive dimension, or nonzero ring.
- A flat morphism: n = 0 is permitted in hTor; no positive Tor bound is
  required. Bounds vary by point rather than adding a uniform condition.
- Unbounded c(O_Y): no boundedness hypothesis was introduced. Only K is
  perfect; the duality argument works against any quasi-coherent complex.
- All characteristics are included. Test modules have the stalk rings'
  universe u, not an unrelated smaller universe. The derived Hom universe w
  is explicit; no auto-implicit variables or universes are used.

Searches actually run (logged by msearch.py in searches.jsonl):

1. LeanSearch, `derived projection comparison perfect complex right adjoint
   proper scheme`: unavailable, HTTP Internal Server Error. Not counted as
   a negative mathematical search result.
2. Loogle, `Adjunction.homEquiv`: zero hits, unknown identifier. Its actual
   signature was then located and read in the pinned local Mathlib source.
3. Mathlib grep, `projectionFormula|projection_formula|compareWithPullback`:
   zero hits.
4. LeanFinder, `For a proper perfect morphism of Noetherian schemes the
   projection formula comparison from derived pullback of a perfect complex
   tensor the right adjoint applied to the structure sheaf to the right
   adjoint of the complex is an isomorphism`: eight hits, concerning ordinary
   sheaf pullback/free objects and ordinary pullback composition; none is
   this derived comparison theorem.
5. Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the
   item id: no hit. Searches for projection/perfect/rightAdjoint and the
   proposed declaration name found ordinary module projection formula and
   étale six-functor material, no statement for these O_X derived categories.
6. Direct rg in `lean/Sheaf` located the existing derived tensor structure,
   derived pullback tensor-product theorem, Tor stalk coordinates, and
   perfect tensor-Hom duality. None already states this mate's invertibility.
   Searches in `dag/lean_names_upstream.json`, Mathlib, and the source for
   `smoothProper_tensor_perfect_case` found no declaration with that name.

Server validation: `scompile.py J1 lem-sc-smooth-proper-tensor-perfect-case`
compiled this module in 3.2 seconds, exit code 0, no errors or warnings.
The node's lean.statement is extracted verbatim from the theorem keyword
through its type, before `:=`; UTC date 2026-10-11. Maximum Lean line width
is 90 characters. The only remaining task belongs to the independent second
reader; no second-reading section was written by this worker.

## Second reading by J1

Independent reading of the node, its Stacks source (Tag 0A9T), and the delivered
module follows. The source objects and clauses are rendered as follows.

- The schemes and map are `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`; the Lean
  declaration has exactly these binders. Noetherianity is `[IsNoetherian X]`
  and `[IsNoetherian Y]`, and properness is `[IsProper f]`, matching the
  source's proper Noetherian setting.
- Finite Tor dimension is the explicit `hTor`: for every `x : X` there is a
  natural bound `n`, and for every stalk test module `M` and `i > n`, the
  corresponding `Tor'` object applied to the restricted-scalars stalk module
  is `IsZero`. The bound depends on `x` and is independent of `M`, exactly as
  required; no projectivity or uniform bound was added.
- The derived-category universe and site instances are the two ambient
  `HasDerivedCategory` binders and the open-localization instances over
  `Y.Opens`. They provide the derived categories used by the recorded
  definitions and do not impose geometric hypotheses.
- The conclusion first supplies the quasi-coherence witnesses `hRf`, `hO`,
  and `hTensor`, then the monoidal structure and pullback/direct-image
  adjunction presentation data. These are existential implementation witnesses
  for the node's restriction of `Rf_*`, `O_Y`, tensor, and `Lf^*`; they are not
  assumptions on `f`, `K`, or `c`.
- The right adjoint is rendered by universally quantified `c` together with
  `adj` from the lifted derived direct image to `c`. Thus the assertion applies
  to every supplied right-adjoint presentation, as the node's “let c be a
  right adjoint” clause requires.
- `K` is a QCoh object with `Scheme.IsPerfect Y K.obj`. The source object is
  `((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj`, and the target is
  `K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj`, exactly the
  two sides of the projection formula after applying `c` to the unit.
- `pf` is the projection-formula isomorphism. Its inverse is constrained by
  `a.homEquiv` applied to the inverse monoidal comparison followed by the
  pullback counit, so it is the canonical projection-formula mate rather than
  an arbitrary isomorphism. The displayed `ObjectProperty.homMk` composite
  tensors the right-adjoint counit with `K` and applies the right unitor.
  `adj.homEquiv` takes its mate, and the final `IsIso` is precisely the
  comparison morphism in the node.

No mismatch was found requiring a repair. The additional existential witnesses
are forced by the full-subcategory encoding of quasi-coherent derived
categories and by the existing global derived tensor/pullback interfaces; they
express the source's implicit preservation and presentation data. The Lean
statement remains verbatim equal to the node's `lean.statement`.

Edge cases were rechecked: empty schemes and empty point sets make `hTor`
vacuous; `K = 0` gives the zero comparison; `K = 𝟙_` is covered by the unitors;
`n = 0` permits flat morphisms; no nonzero, connectedness, dimension, or
characteristic assumption appears; and all explicit universes are shared with
the stalk and derived-category carriers.

Searches were repeated with `rg` in `lean/Sheaf`, Mathlib, and
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, plus the recorded
LeanSearch/Loogle/LeanFinder searches. No declaration of this comparison or
of `smoothProper_tensor_perfect_case` exists. The used notions resolve to the
recorded declarations `schemeDerivedCategory`, `schemeDerivedDirectImage`,
`Scheme.IsPerfect`, `derivedPullback`, and the global
`schemeDerivedTensorMonoidal`; no private copy or duplicate definition was
introduced. The module compiles with only its intentional `sorry` proof.
