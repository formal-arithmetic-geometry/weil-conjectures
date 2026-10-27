## Worker report

The module `Sheaf.AlgebraicGeometry.CurveEtaleSchemeCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_scheme_cover`, with `sorry` as its only
proof. No definition is introduced. I read Stacks `moduli-curves.tex`,
`section-stack-curves` and Tag 0E6F, `lemma-etale-locally-scheme`, including its proof.
The statement is the first assertion, without the additional H-projectivity conclusion.
The node's statement, proof and proof dependencies are unchanged. Its statement
dependencies gain the already landed `def-sfb-proper-curve-moduli`, because the statement
uses precisely its `IsProperCurveFamily` predicate instead of copying that definition.

The inherited BLOCKED ending concerned a stage-1 re-split. The current node has a Q18
stage-1 PASS but no Lean record; `coord/queue.tsv` assigns it stage 2, and
`coord/brief-stage2.md` section 0 explicitly authorizes this handoff. There is no repair
note for this item. This delivery retains the reviewed split and supplies its Lean statement.

Hypothesis and clause correspondence:

- The scheme T is `T.left` for `T : Over S`, with `{S : Scheme.{u}}` an arbitrary ambient
  base. This is the existing algebraic-space framework, not an additional geometric
  assumption: every scheme T is available by taking S=T and T to be its identity object.
  `T.hom` simply remembers the common ambient base.
- The algebraic space X is `X : AlgebraicSpace S`, the recorded full subcategory of fppf
  sheaves with representable diagonal and a surjective etale scheme atlas.
  `f : X.obj.obj ⟶ yoneda.obj T` is the morphism to T, expressed as a natural
  transformation of the underlying presheaves, as in the dependency's interface.
- All family hypotheses are exactly `hf : IsProperCurveFamily X T f`. I read its full
  definition, not only its name. Its first conjunct is
  `MapToSchemeIsLocally (@Flat) X T f`, testing flatness on representable etale scheme
  charts. Its separatedness conjunct represents the relative diagonal by closed
  immersions. `MapIsQuasiCompact f` together with
  `MapToSchemeIsLocally (@LocallyOfFiniteType) X T f` is finite type.
  `MapToSchemeIsUniversallyClosed X T f` tests closedness on point spaces after every
  scheme base change. These render properness without assuming X is already a scheme.
- Finite presentation is the same quasi-compactness conjunct, quasi-compactness of the
  relative diagonal, and `MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`.
  Thus this is finite presentation, not merely local finite presentation.
- The last conjunct of `IsProperCurveFamily` quantifies over every `Ω : Type u` with
  `[Field Ω] [IsAlgClosed Ω]` and every `a : Spec (.of Ω) ⟶ T.left`. It bounds
  `topologicalKrullDim (Point (Limits.pullback f ...))` by one. The pullback map is
  exactly Yoneda of the scheme map a over S. `Point` is the existing quotient of
  field-valued representatives; its existing topology is final for etale scheme charts.
  This is the intrinsic dimension of the algebraic-space fibre, equivalently the
  supremum of the dimensions of its affine etale charts in the node. This equivalence
  uses etale invariance of local dimension and is a mathematical identification of the
  two standard dimension descriptions, not a new assumption in the statement.
  `topologicalKrullDim` has codomain `WithBot ℕ∞`, so empty fibres have dimension bottom
  and satisfy the bound. No positive-dimension, purity or nonemptiness hypothesis appears.
- The covering is `∃ (I : Type u) (Tᵢ : I → Over S) (e : ∀ i : I, Tᵢ i ⟶ T)`.
  Its members are actual schemes `(Tᵢ i).left` and its morphisms are `(e i).left`.
  The existential small index is appropriate to the scheme/site universe: an etale
  cover can be chosen from affine neighbourhoods of the u-small point set of T.
  There is no independent lower universe for test schemes or geometric fields.
- `∀ i : I, Etale (e i).left` renders etaleness of each covering morphism.
  `∀ t : T.left, ∃ (i : I) (tᵢ : (Tᵢ i).left), (e i).left.base tᵢ = t`
  renders joint surjectivity, not individual surjectivity of every member.
- For each i, `∃ Y : Over S, Nonempty (Limits.pullback f (yoneda.map (e i)) ≅ yoneda.obj Y)`
  says exactly that the sheaf fibre product is represented by a scheme Y. Its existence
  is a proposition, not a chosen or hollow definition. Since the given presheaves are
  sheaves, their presheaf pullback is the underlying sheaf fibre product. Forgetting
  from sheaves reflects these isomorphisms. No arbitrary comparison map is substituted.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`; the recorded algebraic-space
  definition and full-subcategory natural transformations.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used inside the existing
  family predicate; its definition is `krullDim (IrreducibleCloseds T)`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. I read all three signatures and their proof docstrings.
  They provide the existing sheaf-pullback and etale-cover interfaces.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `IsProperCurveFamily` and its five
  named morphism-property helpers, read in full. This is a landed definition, now cited
  in stmt_deps; no dependency module or duplicate predicate is needed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback` and
  its projections, the recorded `def-pc-fibre-product` interface.

The module publicly imports the two statement modules, which transitively expose the
other statement definitions. The two additional proof prerequisites
`lem-sfb-curve-smooth-polarization-cover` and
`lem-sfb-smooth-space-cover-etale-sections` have no recorded Lean declaration on the base,
so there is no module to import for them. They remain named in the theorem's complete
three-step natural-language proof docstring, ready for stage 3. Both supply proof steps,
not missing notions required to type this statement.

Edge cases checked before accepting the existing draft: for empty T the existential
cover may use an empty index and the point-surjectivity condition is vacuous. For empty X
and nonempty T one may use the identity cover and the empty representing scheme. Nothing
requires f to be surjective. Zero-dimensional, nonreduced, disconnected and geometrically
disconnected fibres are included. The base need not be Noetherian, affine, connected or
reduced, and no genus or Hilbert polynomial is fixed. Scheme-source families are included
and can use the identity cover; non-scheme-source families are retained in the hypotheses.
All binders and the universe u are explicit and `autoImplicit` is disabled.

Searches actually run through the prescribed msearch wrapper in this turn:

- LeanFinder: "A proper flat finitely presented family of algebraic space curves is
  representable by schemes after an etale covering of the base". Eight hits concern
  `UniversallyOpen.of_flat`, `Scheme.Etale`, etale composition/base change, flatness,
  and local finite presentation. None is the scheme-cover assertion.
- Loogle: `"AlgebraicSpace", "IsScheme"`. Zero hits.
- grep of Mathlib: `etale.*locally.*scheme|curve.*scheme.*cover|IsProperCurveFamily`.
  Zero hits.
- LeanSearch: "A proper flat family of algebraic space curves is representable by
  schemes after an etale cover of its base". Eight hits concern scheme flatness and
  properness, without the algebraic-space scheme-cover conclusion.
- Direct `rg` of `lean/WeilConjectures` for the node id, curve/etale/scheme terminology,
  `IsProperCurveFamily` and `exists_etale_scheme_cover` found no matching statement.
  The same project search in `lean/Sheaf` found `IsProperCurveFamily` in the existing
  proper-curve-moduli module and its use by `CurveLimitPreservation`, but no assertion
  supplying the requested etale scheme cover. A direct Mathlib grep for the two names
  also found none. `dag/lean_names_upstream.json` has no matching declaration.

No new nodes, dependency repairs, statement correction or disputed statement.
The prescribed scompile.py check compiled this file in both sandbox and library-module
contexts cleanly. The only proof is the single expected `sorry`.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
