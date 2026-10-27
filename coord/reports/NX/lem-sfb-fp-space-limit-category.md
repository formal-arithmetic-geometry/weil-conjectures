## Worker report

The module `Sheaf.AlgebraicGeometry.FpSpaceAffineLimitCategory` states
`AlgebraicGeometry.AlgebraicSpace.fp_space_affine_limit_category`, with its entire proof
postponed by one `sorry`. No new definition or helper theorem is introduced. The natural-language
proof in its docstring follows all ten steps of the node, including relation-witness equations,
the check that the descended morphism is over the stage base, and the categorical interpretation.

The source was read at `literature/stacks-project/spaces-limits.tex`,
`lemma-descend-finite-presentation`, lines 1931–2010 (Stacks 07SK). The node is its specialization
to affine scheme bases. The source and node agree; there is no statement correction or dispute.

Hypothesis and clause correspondence:

- Work over Spec Z: `Over (Spec (.of (ULift.{u} ℤ)))` for schemes, and
  `AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` for spaces. ULift places the integer base in
  the same universe as its schemes; it imposes no characteristic restriction.
- Size convention: the explicitly declared `universe u` and `I : Type u` put the small
  directed index in the schemes' universe. Scheme slice objects live in the larger universe;
  representable presheaves and algebraic spaces retain the published `Type u` values.
  All binders are explicit, with `set_option autoImplicit false`.
- Nonempty directed set: `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`.
  No antisymmetry or chosen initial stage is required.
- Inverse system of affine schemes: `D : Iᵒᵖ ⥤ Over (...)` and
  `[∀ i : I, IsAffine (D.obj (op i)).left]`. Its transition over `i ≤ j` is
  `D.map (homOfLE h).op`. All maps between affine schemes are affine, so affine transitions
  follow from the stated affine-stage assumption. No separate redundant instance is imposed.
- T is the inverse limit: `c : Cone D` with `hc : IsLimit c`. This is a limit in the
  scheme slice. Limits in a slice are created by forgetting to schemes; conversely, the
  compatible map to Spec Z puts the scheme limit in this slice. The cone point is therefore
  the specified limit. Its affineness follows from the affine limit theorem, and is not
  required as an additional assumption.
- A finitely presented algebraic space over a scheme U: a published algebraic space X
  together with `f : X.obj.obj ⟶ yoneda.obj U`, satisfying exactly
  `MapIsQuasiCompact f`, `MapIsQuasiCompact (pullback.diagonal f)`, and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) X U f`. The last predicate tests
  each representable etale source scheme chart, using the existing scheme property.
  This is the scheme-target chart test, not a representability requirement on f.
- Objects and every U-morphism: the family is `Over.mk f` in the presheaf slice over
  `yoneda.obj U`. Algebraic spaces form a full subcategory of fppf sheaves, and those
  sheaves form a full subcategory of presheaves, so the slice Hom type is exactly all
  U-morphisms, without an isomorphism, etaleness or cartesianness restriction on arrows.
- Base-change transition/comparison functors: `Over.pullback (yoneda.map a)` for the
  actual base map a. Their objects and maps are the chosen categorical fibre products,
  with the usual projections. The sheaf and algebraic-space closure statements are already
  `lem-trf-space-fibre-products-etale-covers`; finite presentation is stable by
  `lem-sfb-space-flat-proper-fp-locality`. Thus the ambient presheaf-slice notation computes
  precisely the geometric base changes and does not replace a space by an arbitrary presheaf.
- Object descent (first conjunct): for every X,f with the three finite-presentation
  properties, there exist `i`, `Y` and `g` with the same three properties, and
  `Nonempty ((Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk g) ≅ Over.mk f)`.
  The isomorphism is in the slice over the represented T, hence over T.
- Morphism descent (second conjunct): for every i and two finitely presented families f,g
  at i, every morphism `α` between their limit pullbacks equals the pullback of a
  morphism `β` at some `j` with `h : i ≤ j`. The displayed equality conjugates β's
  pullback by the canonical direct-to-iterated-pullback isomorphism, retaining equality
  with the prescribed α rather than merely asserting existence of an unrelated map.
  `Over.pullbackComp` supplies that canonical isomorphism. Its two `eqToHom` casts
  identify the composite base map with the direct map using precisely
  `yoneda.map_comp` followed by `c.w (homOfLE h).op`; no arbitrary comparison is chosen.
- Eventual equality (third conjunct): arbitrary `α β : Over.mk f ⟶ Over.mk g` with
  equal images under the limit pullback become equal under the pullback to some
  `j ≥ i`. Two originally different stages first move to a common upper bound;
  base-change stability makes this equivalent to the stated common-stage clause.
- The canonical filtered 2-colimit equivalence: the conjunction expresses its full
  explicit content, exactly as the node spells it out. Objects are represented at stages,
  and arrows are stage maps modulo eventual equality. The first clause is essential
  surjectivity, the second fullness, and the third faithfulness. The final docstring
  paragraph explains how the inverse Hom bijections construct an inverse equivalence.
  This follows the already published encoding used by `properCurve_limit_preservation`
  and `fp_over_space_limit_descent`; it does not introduce a second category definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, the full subcategory of
  fppf sheaves with representable diagonal and surjective etale scheme atlas, and
  `IsEtale` / `IsRepresentableWith` used by the chart predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `MapToSchemeIsLocally`. These are the precise published affine-test and scheme-target
  chart predicates, independent of the proper-curve condition. The landed owning node
  `def-sfb-proper-curve-moduli` is added to stmt_deps to record this use.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property; `pullback.diagonal` is the usual relative diagonal.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`, `Over.pullbackComp`;
  `CategoryTheory.Limits.Cone`, `IsLimit` and the preorder category encode the diagram.
- `def-weil-size-convention` is explicitly a universe convention, not a Lean object.
  Its null declaration is therefore not an unusable dependency.

The original statement dependencies are all used through their existing declarations;
none was restated. The additional landed dependency supplies the morphism predicates already
used by sibling space statements. All proof dependencies with recorded modules are imported
privately, along with the Mathlib scheme permanence inputs. The two proof nodes
`lem-sfb-fp-etale-presentation-criterion` and `lem-sfb-lfp-space-scheme-limit-test`
have no recorded module in the read clone, so there is no module to import for those
postponed proof inputs. They are not needed to type this statement; their full roles remain
in its proof docstring and the unchanged proof dependency list.

Edge cases checked before and after writing:

- Empty I is excluded as in the source. A singleton I gives the identity descent clauses.
  A directed preorder with equivalent distinct indices is permitted.
- Empty scheme stages and an empty limiting scheme are allowed. For an empty limiting
  base the presheaf maps still force families over that base; there is no added
  nonemptiness hypothesis on T, X or Y.
- Empty finitely presented spaces are allowed. No connectedness, reducedness, flatness,
  properness, separatedness or dimension hypothesis has entered the finite-presentation test.
- Nonseparated spaces are included: the diagonal is only quasi-compact, not closed.
- Every over-base arrow is quantified, including noninvertible maps, identity maps,
  and equal maps. Equality descent asks for a late stage, not equality at the initial one.
- β's pullback is compared to α with correctly oriented direct-to-iterated and inverse
  comparison arrows. Both endpoint casts use the same cone equality.
- The index universe matches the scheme universe. No equality between independent
  site object and morphism universes has been assumed.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`, query: "The category of finitely presented algebraic spaces
  over a directed affine inverse limit is the filtered colimit of categories at finite stages".
  Eight hits, on ring finite presentation, affine scheme limits and generic filtered
  colimit presentations; no algebraic-space descent theorem.
- `msearch.py ... loogle`, query: `AlgebraicSpace, FinitePresentation`.
  Zero hits; Mathlib has no identifier AlgebraicSpace.
- `msearch.py ... grep`, query: `AlgebraicSpace|algebraic space.*limit`, AlgebraicGeometry.
  Zero hits. The CategoryTheory query `AlgebraicSpace|filtered.*[Cc]olimit.*[Cc]ategor`
  produced 11 generic filtered-colimit declarations and no space statement.
- `msearch.py ... leansearch`, query: "Finitely presented algebraic spaces over an inverse
  limit of affine schemes descend with their morphisms and equalities". Eight hits,
  including RingHom.FinitePresentation, LocallyOfFinitePresentation, scheme limit global
  sections and descent of scheme morphism properties; no matching space theorem.
- `rg` on `lean/WeilConjectures`, by the item id and by finite-presentation/space/limit
  patterns, found scheme/ring results only and no declaration for this node.
- `rg` on `lean/Sheaf` found uses of this item in proof docstrings, and the sibling
  general space-base statement `fp_over_space_limit_descent`. That theorem is not this
  exact affine-scheme-base statement, and its proof route uses scheme-base descent;
  it is not imported here. The scheme-base qcqs node has no Lean record.
- Source reads of `ProperCurveModuli.lean`, `AlgebraicSpaceMorphismProperties.lean`,
  `AlgebraicSpace.lean`, `AlgebraicSpaceFibreProductsEtaleCovers.lean`,
  `EnlargedEtaleRingedSite.lean` and the two sibling limit statements confirmed the
  existing shared definitions and comparison conventions. No missing notion was found.
- The chosen declaration name was searched in Mathlib/upstream/project and the upstream
  name index; no existing declaration uses it.

Validation: the prescribed `scompile.py NX lem-sfb-fp-space-limit-category` compiled the
single delivered module cleanly in sandbox mode (4.6 s) and its final library module
name (3.7 s), with no errors or unexpected warnings. All lines are at most 100 characters.
The only `sorry` is the whole proof of the named theorem corresponding to this DAG node.

## Second reading by NX

This is a second self-check, not a claimed independent worker review: the dispatcher brief
prohibits starting other agents, and the maintainer supplies the independent delivery review.
Re-read the node, the source, the full dependency predicates and the final signature side by
side. Checked the three finite-presentation conditions in each of the three clauses; the
unrestricted slice arrows; nonempty directed index; affine stages; the actual limit cone;
and both endpoint transports in the morphism equation. No mathematical mismatch was found.
Added the existing owning node for the scheme-target predicates to stmt_deps. Removed no
hypothesis or conclusion and changed no source statement. No new or dependency modules
need review.
