## Worker report

Item: lem-sfb-space-qc-open-enlargement-induction. The module
`Sheaf.AlgebraicGeometry.SpaceQcOpenEnlargementInduction` states
`AlgebraicGeometry.AlgebraicSpace.qc_open_enlargement_induction`, with its single
proof postponed by `sorry`. No definition or auxiliary theorem is introduced.
The source was read at `literature/stacks-project/spaces-perfect.tex`,
`lemma-induction-principle-enlarge` (Tag 09IT), lines 1490–1555, together with the
existing Tag 08GP induction interface. The docstring reproduces all six DAG proof
steps, including the reduced-source factorization and affine refinement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention is the explicit universe `u`; the base is `S : Scheme.{u}`
  and the space is `X : AlgebraicSpace S`. No restriction on S is imposed.
- Quasi-compactness of the atlas point topology is
  `hXqc : CompactSpace (Point X.obj.obj)`.
- Absolute quasi-separatedness is `hXqs : IsAbsolutelyQuasiSeparated X`, the
  already landed affine-test predicate equivalent to the absolute diagonal being
  quasi-compact (Stacks Tag 0AHR). In particular it is not relative separation over S.
- The fixed open and its quasi-compactness are `W₀ : OpenSubspace X` and
  `hW₀ : CompactSpace (Point W₀.val.toFunctor)`.
- `P : Subfunctor X.obj.obj → Prop` is used only on quasi-compact open subfunctors,
  including the top subfunctor. Its unused values outside this domain impose no
  condition. `h_iso` states invariance under presheaf isomorphisms of quasi-compact
  open subspaces. These are precisely isomorphisms of their associated spaces.
- Hypothesis (i) is `h_start : P W₀.val`.
- In hypothesis (ii), `W₁ W₂ : OpenSubspace X` and their two CompactSpace premises
  give exactly the two quasi-compact opens; `W₀ ≤ W₁` gives the fixed-open condition,
  and `h₁₂ : W₁ ≤ W₂` is their inclusion. `Subfunctor.homOfLe h₁₂` is its canonical
  natural transformation.
- `Y : AlgebraicSpace S` and `e : Y.obj.obj ≅ W₂.val.toFunctor` are an arbitrary
  presentation of the upper open as an algebraic space, required to apply the
  recorded `ClosedSubspace` interface. Open subspaces are automatically algebraic
  spaces as specified by the dependency. Quantifying over presentations adds no
  geometric restriction. The lower-open inclusion into Y is exactly
  `Subfunctor.homOfLe h₁₂ ≫ e.inv`.
- The affine chart is `V : Over S` with `IsAffine V.left`. Its map is the actual
  presheaf map `f : yoneda.obj V ⟶ Y.obj.obj`; `IsEtale f` includes representability
  and etaleness on every scheme base change, by the dependency's definition.
- `C : ClosedSubspace Y`, `IsReduced (C.val : AlgebraicSpace S)`, and the displayed
  point-image equality with the complement of the lower-open image specify the
  reduced closed complement. Its existence and uniqueness are precisely
  `exists_unique_reduced_closed_subspace`, not an arbitrary unsupported complement.
- `IsIso (Limits.pullback.snd f C.val.arrow.hom.hom)` is the isomorphism of the
  actual fibre product V ×_Y C → C in the distinguished-square condition.
- The implication `P W₁.val → P W₂.val` finishes hypothesis (ii); there is no
  requirement P(V), P(overlap), chart surjectivity, or affineness of W₁/W₂.
- The first conclusion `P ⊤` is P(X), using the full subfunctor of X.
- The second conclusion repeats exactly the square conditions of (ii), independently
  of P(W₁). Its existential `H : Over S`, `i : H ⟶ V`, and
  `a : yoneda.obj H ⟶ W₁.val.toFunctor` with `IsPullback` express that H represents
  W₁ ×_W₂ V, after transport by e. `IsOpenImmersion i.left` and
  `CompactSpace H.left` say it is a quasi-compact open subscheme of V.

Dependency declarations used (their full definitions/signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`; the full fppf-sheaf/atlas encoding
  is retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `AlgebraicSpace.OpenSubspace`,
  the ordered subtype of subfunctors representable by open immersions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `AlgebraicSpace.Point`,
  `pointImage`, and `pointTopologicalSpace` (Point itself is imported from PointClasses).
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `AlgebraicSpace.exists_unique_reduced_closed_subspace`; its imported
  `AlgebraicSpace.ClosedSubspace` and `AlgebraicSpace.IsReduced` give the complement.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`. Added its existing node
  `def-sfb-space-absolute-quasi-separated` to stmt_deps, as permitted for a landed notion.
- `Mathlib.CategoryTheory.Subfunctor.Basic`: `Subfunctor.homOfLe` and the top
  subfunctor (available through the statement imports).

All recorded proof-dependency modules are imported privately: SpaceQuasiCompactAffineTests,
SpaceChangeBase, AlgebraicSpaceEtaleOpenImage, AlgebraicSpaceRepresentableEtaleSchemeTests,
AlgebraicSpacePointOpenCalculus, and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
(the finite affine cover declaration
`AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`). The currently
unstated proof nodes `lem-sfb-space-qcqs-permanence` and
`lem-sfb-qcqs-space-splitting-filtration` supply no module to import; they are not
needed to formulate this statement. No statement dependency is missing or replaced.

Edge cases checked before writing: X empty; W₀ empty; W₀ = X; equal consecutive
opens; empty affine chart; empty complement (the base-change isomorphism then is
automatic); an empty finite affine cover in the proof; and arbitrary, potentially
non-quasi-separated S. No nonempty, strict-inclusion, or separated-base binder
excludes these cases. The overlap conclusion concerns its scheme's compactness,
not the tautological quasi-compactness of an identity morphism.

Searches actually run:

- msearch.py leanfinder, query "Induction from a fixed quasi compact open of a quasi
  separated algebraic space by affine elementary distinguished squares": eight hits,
  including compact_open_induction_on and scheme quasi-separatedness results; no match.
- msearch.py loogle, query "AlgebraicGeometry.Scheme, IsCompact": twelve hits, including
  compact_open_induction_on and finite affine-cover statements; no algebraic-space
  distinguished-square enlargement principle.
- msearch.py grep, query `distinguished.*square|induction.*(qcqs|quasi.?compact)|enlarg.*open`,
  subdirectory AlgebraicGeometry: zero Mathlib hits.
- msearch.py leansearch, query "Induction from a fixed quasi compact open of an algebraic
  space by affine elementary distinguished squares": eight hits on scheme affine-open
  induction and finite covers, none stating this node.
- rg of `lean/WeilConjectures` for the item id: no match. Searches for enlargement/open
  induction found scheme finite-type-extension material, not this statement.
- rg of `lean/Sheaf` for distinguished squares found
  `SpaceQcqsDistinguishedSquareInduction.lean`; its theorem has an affine base case
  and requires P on both charts and their overlap. It is not the fixed-open enlargement
  principle, so cannot be recorded as an existing exact match. Its source was read.
- rg in both project roots and dag/lean_names_upstream.json for the proposed declaration
  and module names found no existing declaration before this delivery.

No STATEMENT-DISPUTED issue, statement correction, new node, or dependency repair.
The sole node changes are its Lean record and the added landed definition dependency.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
