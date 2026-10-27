## Worker report

The module `Sheaf.AlgebraicGeometry.StackFibreUnramifiedEtale` states
`CategoryTheory.stack_fibre_unramified_etale`; its only theorem proof is `sorry`.
Read the node and Stacks `stacks-morphisms.tex`, Tag 06N2,
`lemma-etale-at-point` (lines 4335–4370), including the proof. The node's scheme
specialization and its nonsurjective étale chart formulation agree with the source.
No statement correction, new definition, dependency repair or disputed assertion.

Hypothesis and clause correspondence:

- The scheme base is `{S : Scheme.{u}}`. The arbitrary algebraic stack is
  `{X : BasedCategory.{v, w} (Over S)}` with `hX : IsAlgebraicModuliStack X`:
  a stack in groupoids, algebraic-space diagonal, smooth surjective scheme atlas.
  Its category object and morphism universes `w` and `v` remain independent.
- The scheme `U` over `S` is `U : Over S`; its map to the stack is `q` from
  `discreteModuli (yoneda.obj U)`. `hqFlat : ModuliSpaceTest @Flat q` and
  `hqLfp : ModuliSpaceTest @LocallyOfFinitePresentation q` are precisely the
  specified tests on every étale scheme chart of every scheme base change.
- The field is `(k : Type u) [Field k]`; `s : Spec (.of k) ⟶ S` records its
  structure over the base, and `a` is its map to `X`.
- The fibre is the actual `moduliTwoFiberProduct q a`. The chart is given by
  `V : Over S`, its projections `b : V ⟶ U`, `r : V ⟶ Over.mk s`, and the
  specified based natural isomorphism `e` between their composites to `X`.
  `moduliTwoFiberLift` constructs exactly the map `h_V → h_U ×_X h_Spec(k)`
  from these data. `hc : IsEtaleModuliMap (...)` asserts that this map is
  representable étale. Every chart gives these projections and comparison,
  and conversely these data give a chart when `hc` holds. No fibre presentation,
  unrelated canonical map, scheme representability of the whole fibre, or
  surjectivity of the chart is assumed.
- `v : V.left` is the given point. The hypothesis `hv` is exactly
  `∃ N : V.left.Opens, v ∈ N ∧ IsUnramified (N.ι ≫ r.left)`:
  the composite `V → Spec k` is unramified on an open neighbourhood of `v`.
- The image `u` is the expression `b.left v`, rather than a separately bound
  point requiring an equality. The conclusion quantifies over
  `W : U.left.Opens`, requires `b.left v ∈ W`, and asserts étaleness of
  `h_W → h_U → X`. The first arrow is induced by the actual open subscheme
  inclusion `Over.homMk W.ι : Over.mk (W.ι ≫ U.hom) ⟶ U`.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`,
  `HasSpaceBaseChange`, `IsModuliStack`, `HasAlgebraicSpaceDiagonal` and the
  based-groupoid vocabulary. Read the full signatures and source docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  used by the algebraic-stack atlas definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the neighbourhoods use the actual scheme open subscheme inclusions.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified`, the recorded local-finite-type and
  open-diagonal conjunction, not merely formal unramifiedness.
- Mathlib `Algebra/Field/Defs.lean`: `Field`, the dependency's mathlib_match.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSpaceTest`; despite the module title, this definition
  quantifies over arbitrary based categories and algebraic-space scheme tests,
  with no Deligne–Mumford hypothesis.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`:
  `CategoryTheory.moduliTwoFiberLift` and `IsEtaleModuliMap`; these definitions
  likewise have no normalization or Deligne–Mumford hypothesis.

The last three owning definition nodes are already landed, with usable Lean
records. They are added to `stmt_deps` under brief-stage2 §5 (STMT_DEPS MAY GAIN
LANDED NODES). No existing notion is redefined. The recorded proof dependency
`lem-sfb-stack-chartwise-smooth-etale-calculus` is imported privately. Read its
signature, docstring and recorded node. The other proof-only theorem
`lem-sfb-stack-unramified-locus-base-change` has no Lean record, so it has no
module to import; it is named in the four-step proof docstring. It is not needed
to formulate this statement, and its proof is not recreated here.

Edge cases checked before writing and in the second reading: an empty `V` has
no `v`; an empty `U` cannot receive `b(v)`; empty base therefore makes the field
map unavailable. A non-surjective chart is permitted. There is no assumption of
unramifiedness elsewhere in the fibre. The conclusion may take all of `U` when
appropriate; `W` is not required proper, affine, quasi-compact, or connected.
No perfectness, algebraic closure, characteristic-zero, noetherianity,
separatedness, finite-type base, or surjectivity of `q` is added. Arbitrary
stabilizers are retained in the 2-fibre product. Scheme and field sizes use the
same arbitrary `u`, with the stack's category universes independent.

Searches actually run via `msearch.py Q60 lem-sfb-stack-fibre-unramified-etale`:

- LeanFinder: `A flat locally finitely presented scheme presentation of an
  algebraic stack is etale near the image of an unramified field fibre point`.
  Eight hits: scheme étale definitions/composition and ring étale loci; no exact
  stack field-fibre statement.
- Loogle: `AlgebraicGeometry.Etale, AlgebraicGeometry.Flat`. Three hits:
  `Etale.of_formallyUnramified_of_flat`, `Etale.iff_flat_and_formallyUnramified`,
  and the flat-descent instance. These are scheme assertions, not this theorem.
- Mathlib grep: `unramified.*[Ff]lat|[Ee]tale.*[Ff]ib[er]` in `AlgebraicGeometry`.
  Eight hits in `Sites/EtalePoint.lean`, `Morphisms/LocalFlatDescent.lean`, and
  `Morphisms/Etale.lean`; none states the node.
- Mathlib grep: `stack_fibre_unramified_etale|stack_fiber_unramified_etale|etale_at_point`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch: `A flat locally finitely presented morphism of algebraic stacks is
  etale near a point of an unramified field fibre`. Eight hits: `Flat`,
  `LocallyOfFinitePresentation`, `IsEtale`, scheme/ring constructors; no match.
- Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `unramified.*[Ff]ibre|unramified.*[Ff]iber`, and the proposed theorem names and
  `etale_at_point`. The former found other scheme/ring results; the latter
  found no existing statement. The exact node-id search in `WeilConjectures`
  and `dag/lean_names_upstream.json` also found no attachment.

Validation: prescribed `scompile.py` compiled both the sandbox and delivered
module paths cleanly (6.3 s and 3.4 s). No error or extra warning.

## Second reading by Q60

Re-read the node, Tag 06N2, the drafted signature, and the definitions of
`moduliTwoFiberLift`, `ModuliSpaceTest`, and `IsEtaleModuliMap`. This is the
worker's separate second pass; no other agent was started, as required by the
dispatcher's brief. The maintainer's independent delivery review remains separate.

Checked the hypotheses and conclusion against the correspondence above. In
particular the 2-isomorphism `e` is over the base, the lift's first projection is
`b` and second projection is `r`, so the point used in the conclusion is exactly
the image asked for. The unramified neighbourhood uses the scheme composite
`N.ι ≫ r.left`; it is not a stronger global assertion. The conclusion uses the
canonical open inclusion, followed by the given `q`. The general
algebraic-stack predicate is used, so no DM specialization was introduced.
No mismatch was found and no source statement was changed. The only dependency
list change records the three already existing interfaces actually used.
