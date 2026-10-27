## Worker report

The delivery states `lem-sfb-stack-smooth-permanence` in
`Sheaf.AlgebraicGeometry.StackSmoothPermanence`. Its main theorem is
`CategoryTheory.stack_smooth_permanence`; the three additional theorems express
exactly the scheme, algebraic-space and representable interpretation clause.
Every theorem has proof `sorry`; the new definition has explicit propositional data.
Its characterization theorem repeats that data without changing any hypotheses.
The accepted node statement and proof are unchanged.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`, with base scheme `Spec (.of k)`.
  No algebraic closedness, perfection or characteristic restriction is added.
- X, Y and Z are `BasedCategory` objects over `Over (Spec (.of k))`, with
  independent explicitly declared object and morphism universes. Their algebraicity
  is `hX`, `hY`, `hZ : IsAlgebraicModuliStack ...`. This retains automorphisms.
- The arbitrary map f is `BasedFunctor X Y`; its smoothness is `hf` using the
  new `IsSmoothModuliMap`. That predicate uses Tag 06FM(2)'s smooth scheme
  presentation: source `a` is `IsSmoothModuliAtlas X U a`; target `b` has
  `ModuliSpaceTest @Smooth b`; `q : U ⟶ V` has `Smooth q.left`; and
  `Nonempty (a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b)` supplies
  the specified 2-commutative diagram. It requires neither representability of f
  nor surjectivity of the target chart. `Nonempty` here expresses existence of
  the diagram's 2-isomorphism, without choosing any construction from a theorem.
- The composition clause is the first conjunct, quantifying over
  `g : BasedFunctor Y Z` and assuming `IsSmoothModuliMap g`; its conclusion
  is `IsSmoothModuliMap (f.comp g)`.
- The base-change clause is the second conjunct, quantifying over every
  `h : BasedFunctor Z Y`; it concludes smoothness of `moduliTwoFiberSnd f h`.
  This is the actual second comma projection from `moduliTwoFiberProduct f h`,
  whose objects include the specified comparison isomorphism. There is no
  quasi-compactness, separation, finite-type, flatness, or representability
  assumption on h.
- `smoothModuliMap_iff_space` identifies smoothness for the discrete stack map
  of `f : A ⟶ B` with `AlgebraicSpace.MapIsLocally @Smooth f`, the existing
  ordinary smoothness test on all compatible etale scheme charts.
- `smoothModuliMap_iff_scheme` identifies the Yoneda scheme map's stack
  smoothness with `Smooth f.left`.
- `smoothModuliMap_iff_representable` assumes exactly algebraicity of its source
  and target and `IsRepresentableByAlgebraicSpaces f`, and identifies smoothness
  with `ModuliSpaceTest @Smooth f`. The latter quantifies over every scheme
  base change, represents it by an algebraic space with its actual projection,
  and tests that projection on every representable etale scheme chart.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (commutative division ring).
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  `BasedFunctor`-based stack vocabulary, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`.
  Read the full declarations and docstrings, including the comparison with
  the actual scheme projection in `HasSpaceBaseChange`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and its scheme-test representation convention.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties:
  `CategoryTheory.ModuliSpaceTest`. Despite its module's name this definition
  has no DM hypothesis and applies verbatim to arbitrary fibred groupoids.
- Sheaf.AlgebraicGeometry.OpenModuliSubstack: `CategoryTheory.moduliTwoFiberSnd`,
  with its original projection equality, retaining the second comma projection.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.

The first five are the original statement dependencies. The item also cites
its new definition and the landed owners of the space-property and second
projection interfaces. These are additive statement-dependency changes allowed
by brief-stage2 section 5. They do not change the natural-language statement.
The new definition cites the existing owner of the representable scheme-test
predicate instead of writing another copy of it.

Available proof dependencies are imported without `public`:
AlgebraicStackFibreProducts, SpaceEtalePresentationPropertyCriterion,
SchemeEtaleSourceTargetProperties, Mathlib's Smooth and pullback modules.
`lem-sfb-fibred-groupoid-representable-smooth-calculus` and
`lem-sfb-stack-smooth-presentation-criterion` currently have no Lean record;
no phantom module is imported. They are mathematical proof prerequisites,
not missing notions required to type this statement; no proof is attempted.
The general smoothness definition is now supplied explicitly by its own node.

Edge cases checked against the sources before writing:
empty source and empty test schemes (smoothness and surjectivity have their usual
vacuous interpretation); identities; arbitrary base-changing maps; arbitrary
characteristic; nonsurjective target charts; and nonrepresentable smooth maps
such as BG to Spec k for a smooth positive-dimensional group G. In the last case
Spec k to BG is a representable smooth surjective source atlas and the scheme
map Spec k to Spec k is smooth, so the new predicate includes this essential
case. Conversely no representable-only predicate is substituted for smoothness.
The tests range over the same scheme universe as the base field. Independent
stack object and morphism universes are retained; no extra universe equalities
are imposed. No counterexample or statement fault found; no STATEMENT-DISPUTED flag.

Searches (actual msearch.py runs plus read-only source searches):

- LeanFinder: “Smooth morphisms of algebraic stacks are stable under composition
  and arbitrary base change”: eight results, all scheme/ring smoothness, including
  `AlgebraicGeometry.isSmooth_comp` and `isSmooth_isStableUnderBaseChange`.
- LeanSearch: “smooth morphism of algebraic stacks defined by smooth scheme
  atlases”: eight hits for Mathlib's scheme `IsSmooth` and constructors;
  no general stack morphism definition.
- Loogle: `"Smooth", "comp"`: twelve ring algebra/formal smoothness hits;
  no general stack definition or permanence theorem.
- Mathlib grep: `algebraic.?stack|smooth_isStableUnderBaseChange`, restricted to
  AlgebraicGeometry: two scheme base-change instance/alias hits, no stack match.
- rg of project and upstream sources: `IsSmoothModuliMap`,
  `IsSmooth.*StackMap`, `stack_smooth_permanence`, and the item id; no matching
  definition or theorem. The two item-id hits in existing proof docstrings
  merely cite this missing result. Read the available AlgebraicModuliStack,
  DmStackMorphismProperties, StackSmoothAtlasBaseChange, and
  StackChartwiseSmoothEtaleCalculus declarations. Their structural smoothness,
  representable calculus and DM properties do not state this node.
- DAG searches for general smooth stack maps and `blueprint_refs.py search
  "smooth morphism"`: no existing definition node. The criterion theorem
  node is a theorem about equivalent presentations and presently has no Lean.
  `blueprint_refs.py ancestor` reports the inherited null ancestor, retained
  in the new node. Read the current `literature/blueprint/latest` direct-image
  proof and the inherited via chain; this helper supports its alteration route.
- Source read directly: stacks-morphisms.tex, 06FM and section-smooth,
  definition-smooth (075U), lemma-composition-smooth (075V), and
  lemma-base-change-smooth (075W). No web-only interpretation was needed.

Validation: the resumed initial dry run reproduced the failure: exposing
`IsSmoothModuliMap` took 57.6 seconds and the consumer reported
`resource exhausted (error code: 28, no space left on device)`.
The repair marks this explicit definition `@[no_expose]` and supplies
`CategoryTheory.isSmoothModuliMap_iff`, whose statement repeats the defining
existential presentation and whose proof is `sorry`, with a source and proof
docstring. This helper belongs to `def-sfb-smooth-moduli-map` and is listed in
its `lean.declarations`. The predicate's data and every consumer signature
are unchanged; neither consumer unfolds the predicate.

Both delivered modules now pass the prescribed server scompile.py together
in dependency order: SmoothModuliMap 3.7 seconds, StackSmoothPermanence
4.4 seconds; their separate sandbox checks took 3.9 and 4.3 seconds.
No errors or unexpected warnings remain. The earlier storage diagnostics
are resolved by this definition repair, superseding the previous attempts.

## New nodes

`def-sfb-smooth-moduli-map` owns the missing general smooth-morphism predicate.
It is Tag 075U using the existential scheme presentation of 06FM(2), with
existing `IsSmoothModuliAtlas` and `ModuliSpaceTest @Smooth`. Its own module is
Sheaf.AlgebraicGeometry.SmoothModuliMap; its definition contains no `sorry` and
chooses no atlas. The existing algebraic-moduli-stack node only defines
smoothness of an object over a scheme, whereas the DM morphism-properties node
only supplies a source-local test for representable morphisms. The separate
smooth-presentation criterion theorem does not own a definition module. The
LeanSearch, Loogle, and Mathlib grep outputs are recorded verbatim in
mathlib_searches, with additional DAG/project search evidence. The new node
has the item's chapter and unit and the inherited null blueprint ancestor.

## Second reading by Q44

No second reading by a worker: under the dispatcher's instructions the worker
delivers directly and the maintainer's independent review is the review.

## Final self-check (2026-10-24)

The repaired packet passed `deliver2.py --no-push`: commit 4ea7daf774d,
preflight and every per-file compile OK. Read the retained item and new definition
against the current dependency signatures and Stacks 06FM(2), 075U, 075V, 075W.
The item changes only lean and the previously added statement dependencies.
The definition keeps its real data, its characterization has the same quantifiers
and clauses, and all five theorem proofs are sorry. No live source was edited.
The example Sheaf CompactObject module is now withdrawn; its node points to
the upstream WeilConjectures.CategoryTheory.CompactObject definition.
