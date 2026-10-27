## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDescendSeparated` states
`AlgebraicGeometry.AlgebraicSpace.eventually_separated_of_affine_isLimit`.
Its sole theorem has proof `sorry`; no mathematical data or helper definition is postponed.
The item statement and accepted proof are unchanged. Three already-landed statement
interfaces are added to stmt_deps so their definitions are explicitly cited:
`def-sfb-proper-curve-moduli`, `def-sfb-space-quasi-compact-presheaf-map`, and
`def-sfb-presheaf-map-separated-diagonal`. There are no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- The ground scheme is literally `Spec (.of (ULift.{u} ℤ))`. Lifting the integers
  supplies Spec Z in the same universe as the schemes; it changes no geometry.
- `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, and `[Nonempty I]`
  express a small nonempty directed index set, including preorders without antisymmetry.
- `D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))` is the inverse system of schemes
  over the specified ground. `haff` asserts that every underlying scheme is affine.
  Transition maps between affine schemes are automatically affine; this source condition
  follows from `haff` and is not imposed as a redundant extra hypothesis.
- `c : Cone D` supplies T, all its projection maps and their compatibility.
  `hc : IsLimit ((Over.forget ...).mapCone c)` says exactly that the underlying
  scheme T is the inverse limit of the underlying T_i. Because Spec Z is terminal,
  writing schemes and their cone in its over-category loses no schemes or maps.
- `i₀ : I` fixes the original stage. `X₀ : AlgebraicSpace (Spec ...)` retains a
  genuinely arbitrary algebraic-space source, not a scheme or a representable morphism.
  `f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀))` is its natural transformation
  to the scheme T_i₀. This is the ordinary space morphism to a represented scheme;
  no extra atlas or presentation is chosen.
- The first conjunct of `hfp`, `MapToSchemeIsLocally (@LocallyOfFinitePresentation)
  X₀ (D.obj (op i₀)) f₀`, tests local finite presentation on every representable
  étale scheme chart of X₀. Since the target is a scheme, its identity chart gives
  exactly the usual source-and-target étale chart convention.
- The second conjunct `IsQuasiCompactPresheafMap f₀` is quasi-compactness via
  quasi-compact scheme atlases of affine scheme tests, the standard affine-test
  formulation of the node's tests by every quasi-compact algebraic space (Tag 03KG).
  This uses the definition owned by `def-sfb-space-quasi-compact-presheaf-map`;
  it does not use an fppf-locality theorem in the statement. The same criterion applies
  to the relative diagonal in the third conjunct,
  `IsQuasiCompactPresheafMap (pullback.diagonal f₀)`, giving quasi-separatedness.
  Thus no part of finite presentation has been omitted.
- `pullback.snd f₀ (yoneda.map (c.π.app (op i₀)))` is exactly f at the limit.
  Its source is the actual presheaf fibre product X₀ ×_{T_i₀} T, the underlying
  presheaf of the sheaf fibre product; it is algebraic by the recorded fibre-product
  theorem. `hsep` asserts `IsSeparatedPresheafMap` of this projection, namely that
  every scheme test of its representable relative diagonal is a closed immersion.
- The conclusion supplies `i : I`, `hi : i₀ ≤ i`, and then every `j : I` with
  `hj : i ≤ j`. The transition `D.map (homOfLE (le_trans hi hj)).op` is T_j → T_i₀.
  Its Yoneda map and `pullback.snd` construct exactly f_j, and the conclusion asserts
  its separatedness. In particular j=i gives the first separated stage.
- The prefatory finite-type, properness, universal-closedness and absolute
  quasi-separatedness conventions introduce no additional assumptions or conclusions
  in this particular theorem; no hypothesis of properness is inserted.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; schemes and represented scheme targets.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  sheaf pullback closure and its presheaf universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  through the proper-curve interface.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally`, with the full
  signature and source-chart definition read. Only its general morphism interface
  is used, and no curve-family hypothesis is present.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `diagonalPresheafMap`, `IsSeparatedPresheafMap`. These are the existing generic
  predicates, owned respectively by `def-sfb-space-quasi-compact-presheaf-map`
  and `def-sfb-presheaf-map-separated-diagonal`. The stronger covering-family
  theorem in that module is not used by the statement.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` in the chart predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` in
  the existing separatedness predicate.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` in the existing atlas predicate;
  it has no Hausdorff condition.
- The recorded scheme `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`,
  `IsSeparated`, and `UniversallyClosed` signatures were inspected; they are scheme
  notions and are not substituted for properties of arbitrary space morphisms.
- `def-weil-size-convention` is metatheoretic and has no declaration to import.
  All universes and variables here are explicit and auto-implicit binding is disabled.

The docstring carries all four accepted proof steps: diagonal qcqs and local finite
  type checks, identification of the base-changed diagonal, closed-immersion descent,
  and persistence by arbitrary base change. The four space proof dependencies
  `lem-sfb-space-descend-closed-immersion`, `lem-sfb-space-diagonal-locally-finite-type`,
  `lem-sfb-space-qcqs-source-products`, and `lem-sfb-space-separated-fp-composition`
  currently have no recorded Lean declaration, so there is no module of theirs to
  import. Existing proof dependencies for affine qcqs and closed-immersion base change
  are available through the imported Mathlib modules. The theorem does not require
  any of these proof results as hypotheses.

Edge cases checked: singleton and non-antisymmetric directed systems; arbitrary i₀;
empty X₀; empty affine bases (zero rings); a limit that is empty although some stages
are not; disconnected and nonreduced schemes; nonrepresentable space morphisms;
non-surjective transition maps; every characteristic. There is no nonempty geometric
fibre assumption, no surjectivity assumption, and no equality of unrelated universes.
The index universe is the scheme universe, as required for directed affine limits.
The entire index set cannot be empty, exactly as the node specifies.

Searches actually run with msearch.py, group Q12 and this item:

- LeanFinder: `Separatedness of a finitely presented algebraic space over an affine
  inverse limit descends to a finite stage`. Eight hits, all scheme properties;
  none states the algebraic-space theorem.
- Loogle: `"IsSeparated", "IsLimit"`. Zero hits.
- LeanSearch: `Separatedness descends to a stage of an inverse limit for algebraic
  spaces`. Eight hits, concerning scheme separatedness and scheme affine limits;
  none states this result for spaces.
- Mathlib grep: `exists_isSeparated|descend.*separated|MapIsSeparated`. Zero hits.
- `rg` of `lean/WeilConjectures` for `algebraic.space|descend.*separated|exists_isSeparated`
  found scheme-only descent theorems (notably `Scheme.exists_isSeparated_overPullbackMap`
  and the affine-transition-limit results); no match with algebraic-space sources.
- `rg` of the upstream name table found the same scheme-only declarations.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id found only references
  in `SpaceDerivedChowNeighbourhood` and `SpaceCoherentStackGeneral`, no declaration.
- `rg` of `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` for separatedness,
  finite presentation and quasi-compactness found the generic interfaces cited above;
  they were opened and reused rather than duplicated.

The source text read was Situation 084W and Tags 0850, 0851 in
`literature/stacks-project/spaces-limits.tex`, and Tag 03KL in
`literature/stacks-project/spaces-morphisms.tex`. The node is the stated affine-base,
finitely presented specialization of that result, with the source's base-change
persistence. No statement correction or unresolved statement dispute was needed.

Validation: scompile.py compiled the delivered module in sandbox mode and library
mode, each clean (1.7 seconds each on the reported run).

## Second reading by Q12

I reopened the node and the finished module for a separate second pass. This is a
self-review: the dispatcher explicitly forbids starting another agent, and the
maintainer supplies the independent review of this delivery.

I checked the ground Spec Z, the scheme universe and index universe, all three directed
index instances, every affine stage, the underlying-scheme limit witness, i₀, the
arbitrary algebraic-space source, and its natural map to the represented stage. Each has
exactly the binder described above. I traced all three hfp conjuncts through the actual
existing definitions. In particular quasi-separatedness is the quasi-compact relative
diagonal, not absolute quasi-separatedness of X₀. The source-chart local-presentation
predicate is appropriate because the target is a scheme. The all-space quasi-compactness
convention uses the standard affine-test atlas formulation (Tag 03KG).

I expanded the two pullback projections in hsep and the conclusion: the first uses the
limit cone projection T → T_i₀; the second uses T_j → T_i₀ with the transitive inequality
in the correct direction after taking opposites. These are the required canonical
morphisms f and f_j. There is no arbitrary map, limit comparison choice, or replacement
of spaces by schemes. The quantifiers give one i working for every j ≥ i. I verified
that no unnecessary nonemptiness, representability, separation or transition-surjectivity
binder was introduced. No mismatch was found in this pass and no statement change was
made. The module has one theorem with `sorry`, no new definitions, no unbound variables,
no local notation or instance, and no diagnostic commands.

## Repair of returned head 5417b9190f23

H2 repaired: replaced the added theorem dependency
`lem-trf-space-qc-separated-etale-local` by the existing definition owners
`def-sfb-space-quasi-compact-presheaf-map` and
`def-sfb-presheaf-map-separated-diagonal`. I opened both live definition records
and verified their recorded declarations are exactly the predicates in hfp, hsep
and the conclusion. Their shared public import remains
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`.

Dropped `lem-sfb-space-quasicompact-fppf-local` from stmt_deps and removed its
unused import. The explanatory module remark now cites the affine-test convention
of Tag 03KG rather than naming the unused theorem. No theorem signature, proof,
mathematical statement, or other import changed. The report now names the actual
definition owners. Current main's non-delivery node fields are retained.

For this second reading I compared the retained returned signature with the repaired
file and confirmed it is byte-identical. I reread hfp's local finite presentation,
quasi-compactness and quasi-compact diagonal, the separated limit projection, and
the eventual-stage quantifiers; their clause correspondence above is unchanged.
The maintainer independently checked all of these against Tags 0851/084W/03KL in
the return, requesting only this dependency/import repair.
