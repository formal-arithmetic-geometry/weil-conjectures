## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedEtaleCompatibleCharts` states
`AlgebraicGeometry.AlgebraicSpace.unramified_etale_compatible_charts` with one postponed
proof. No definitions or other theorems are introduced. The mathematical statement is
unchanged. The only additional node field change is adding the already landed
statement dependency `def-sfb-space-morphism-properties`, which owns the reused
chartwise predicate. Compatible diagrams are quantified explicitly in the signature.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the algebraic spaces and their morphism are
  `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`. These use the recorded scheme and
  algebraic-space definitions, including fppf sheaves, representable diagonals and
  existence of representable surjective étale scheme atlases.
- Either scheme property is expressed by quantification over
  `P : MorphismProperty Scheme.{u}` restricted by
  `P = @IsUnramified ∨ P = @Etale`. `IsUnramified` is the recorded conjunction of
  locally finite type and open-immersion diagonal. `Etale` is Mathlib's recorded
  affine-local étale ring-map predicate, equivalent to the node's lfp, flat,
  unramified conjunction.
- A compatible diagram is quantified explicitly by `∀ (U V : Over S)` and
  `(a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V)`.
  Its assumptions are `IsEtale a → IsEtale b →
  a ≫ f.hom.hom = yoneda.map h ≫ b →`. Thus the schemes over S, the
  representable étale chart maps, the S-scheme morphism and its commutative square
  are precisely those in the node. `h.left` is the underlying scheme morphism.
- The chartwise property of f is the reused `MapIsLocally P f`. Its full definition
  universally quantifies over exactly those two schemes, two representable étale
  chart maps and commuting scheme morphism. It imposes no chart surjectivity.
- The first conjunct universally quantifies over every such compatible diagram, assumes
  `IsSurjective a`, and concludes `MapIsLocally P f ↔ P h.left`.
  This states recognition in any fixed compatible diagram with surjective source
  chart for each of the two properties. In particular it adds no surjectivity
  assumption on the target chart.
- The second conjunct fixes an arbitrary `(V : Over S)` and
  `(b : yoneda.obj V ⟶ Y.obj.obj)` and assumes `IsEtale b → IsSurjective b →`.
  These are exactly the prescribed surjective étale target scheme atlas hypotheses.
  The conclusion supplies `∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
  (h : U ⟶ V), IsEtale a ∧ IsSurjective a ∧
  a ≫ f.hom.hom = yoneda.map h ≫ b`. This gives the source scheme, its
  representable surjective étale atlas map, the scheme morphism, and the required
  equation. `IsEtale` already includes scheme-test representability.
- There are no separation, finite-type, finite-presentation, quasi-compactness,
  Noetherian, characteristic, or nonemptiness assumptions on f or the spaces.

Declarations used, read with their complete signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
  The first two relative predicates test on every scheme and are independent of
  the scheme-level `Etale` class; no deprecated scheme `IsEtale` alias is used.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, its
  `iff_flat_and_formallyUnramified`, `Etale.etale_comp`, and `Etale.of_comp`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.
- Proof-only `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `AlgebraicGeometry.AlgebraicSpace.etalePresentation_property_criterion`, with its
  `EtalePresentation` and `HasEtalePresentationProperty` interfaces for the proof plan.
  None of these declarations occurs in the repaired signature.
- Proof-plan imports use
  `Sheaf.AlgebraicGeometry.SchemeUnramifiedEtaleLocality.scheme_unramified_etale_locality`
  (declaration namespace `AlgebraicGeometry`),
  `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties.scheme_etale_source_target_properties`
  (declaration namespace `AlgebraicGeometry`), and the three declarations
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (declaration namespace `AlgebraicGeometry.AlgebraicSpace`). Scheme surjectivity
  composition is the instance in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, following the `Surjective` class.
  These proof modules are imported without `public`; statement modules are public.

Sources read: `spaces-morphisms.tex`, lemma-local-source-target (03MJ),
definition-unramified (03ZH), lemma-etale-local (03XT), specifically (7)--(8);
`spaces.tex`, lemma-lift-morphism-presentations (02X1), including its actual construction
U = W ×_Y V; `descent.tex`, remark-list-local-source-target (04R3), items (7) and (9).
The latest blueprint's direct-images proof was also read: this auxiliary chart lemma
is not its unit statement and no blueprint statement or route changes.

Edge cases checked before writing:

- X empty: every source scheme mapping to X is empty; the chartwise test and any
  surjective-source chart have unramified and étale horizontal map. The prescribed
  target-atlas construction has empty U. Nothing requires a point or a nonempty atlas.
- Y empty: f implies X empty; the same conclusions apply.
- An empty target chart b is allowed in the first conjunct, with no surjectivity
  requirement on it. If the source chart is surjective and maps to that empty V,
  X is empty, as required. In the second conjunct an empty prescribed atlas can be
  surjective only for empty Y; that case is retained.
- Identity atlases of scheme spaces are permitted. There is no imposed
  quasi-compactness or separatedness on either étale chart.
- All schemes and presheaf values use the same universe u as the existing
  algebraic-space definition; no test-scheme universe is reduced. u is explicit
  and arbitrary, and `set_option autoImplicit false` enforces explicit binders.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leansearch "A morphism of algebraic spaces is unramified if and
  only if a compatible surjective etale scheme chart morphism is unramified"`:
  eight hits, all about formal unramifiedness of schemes or algebras, no exact match.
- `msearch.py ... leanfinder "Unramified algebraic space morphism tested on
  compatible etale scheme chart"`: eight hits, including scheme IsEtale,
  FormallyUnramified and IsEtale.of_comp; none state the algebraic-space result.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, AlgebraicGeometry.IsUnramified"`:
  zero hits, service reports unknown identifier AlgebraicGeometry.IsUnramified.
  The local project definition was found and read directly instead.
- `msearch.py ... grep "EtalePresentation|etalePresentation|MapIsLocally"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `EtalePresentation|unramified_etale_compatible_charts|etalePresentation_property`:
  no existing exact theorem. Project hits found the reused general criterion;
  `SpaceLocalPropertiesChartTest` covers flat, lfp and lft rather than these two
  properties, and lacks this prescribed-atlas existence statement. Its declarations
  were read to check the difference. Upstream hits were unrelated ring standard
  étale presentations. Searching the item id in `lean/WeilConjectures` found none.

No statement dispute, correction, new notion, or dependency-interface repair is needed.
The theorem has exactly the requested `sorry` proof and a step-by-step source proof
in its docstring. After the H2 repair, compilation through `scompile.py` succeeded
against current server sources for both the sandbox and library module checks, with
no errors or warnings. No launcher tool was changed.


## Repair H2

The returned immutable head `177eebb9aa06` cited the theorem node
`lem-sfb-space-etale-presentation-property-criterion` in `stmt_deps` only to use
its plain `EtalePresentation` structure. Following the maintainer's explicit
inline-quantifiers correction, the signature now binds `U V a b h` and assumes
`IsEtale a`, `IsEtale b`, the commutative-square equation and `IsSurjective a`
directly. The theorem node was removed from `stmt_deps`, and its module is now
an ordinary proof import, as its theorem remains a recorded proof dependency.
No new notion or node is introduced. The current shared node still has the original
four statement dependencies and no Lean binding; the sandbox adds only the landed
`def-sfb-space-morphism-properties` definition dependency and the repaired Lean record.
The natural-language statement, proof, proof dependencies and all other node fields
are unchanged from the returned packet and current shared node.

## Second reading by O1

Repair self-check, with the node and repaired file open: `S`, `X`, `Y`, `f` and the
restriction to the two scheme properties are unchanged. The explicit `U V a b h`
binders and their three diagram hypotheses express exactly the former presentation
fields; the separate `IsSurjective a` still applies only to the source chart.
`MapIsLocally P f ↔ P h.left` is the fixed-diagram equivalence. The second conjunct
still quantifies over every prescribed surjective étale target atlas and supplies
`U`, `a`, `h`, both source-atlas properties and the same commuting equation.
No target surjectivity was added to the first conjunct and no nonempty, finiteness,
separation or universe hypothesis was added. The signature uses no
`EtalePresentation`, so the ownership defect H2 is removed. This is the repairing
worker's self-check; the maintainer supplies the independent review.
