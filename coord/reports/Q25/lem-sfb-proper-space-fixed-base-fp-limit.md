## Worker report

States `AlgebraicGeometry.AlgebraicSpace.exists_proper_finitePresentation_closedImmersion_limit`
in `Sheaf.AlgebraicGeometry.ProperSpaceFixedBaseFpLimit`, with its sole proof `sorry`.
No definitions or additional postponed theorems are introduced. The source read was
Stacks `spaces-limits.tex`, Tag 0A0W, label
`lemma-proper-limit-of-proper-finite-presentation`, including its proof. The current
blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read; this is a supporting lemma, not the unit statement.

Hypothesis and clause correspondence:

- The ambient base is `Spec (.of (ULift.{u} ℤ))`. `T : Over` that scheme is an
  arbitrary scheme with its integer structure map. This restricts no scheme: every
  scheme has its unique structure map to the spectrum of the integers. `ULift` places
  the integer ring in the same explicit universe as the schemes.
- `CompactSpace T.left` and `QuasiSeparatedSpace T.left` give exactly the qcqs
  hypothesis on the scheme base, including the empty scheme.
- `X : AlgebraicSpace ...` retains an algebraic-space source, with no scheme,
  representability, Noetherian or finite-presentation assumption on X.
- `f : X ⟶ schemeSpace T` is the specified morphism to T, regarded as its actual
  representable fppf sheaf. `hf : MapIsProper f` supplies separatedness, finite
  type and universal closedness. Reading its definition shows that the diagonal is
  representable by closed immersions, finite type is quasi-compact plus chartwise
  local finite type, and universal closedness quantifies over every algebraic-space
  base change. Its quasi-compactness uses compact point spaces of affine-test
  pullbacks; this agrees with the node's quasi-compact-atlas condition by the existing
  `points_compactSpace_iff` (AlgebraicSpaceEtaleOpenImage.lean:115). No new convention
  or stronger properness hypothesis is introduced.
- `K : Type u`, `PartialOrder K`, `Nonempty K`, and `IsDirected K (· ≤ ·)` give a
  small nonempty directed set. The index universe is the scheme universe, not an
  independent possibly smaller universe. Antisymmetry matches the directed-set wording.
- `D : Kᵒᵖ ⥤ AlgebraicSpace ...` is the inverse system. In the opposite preorder,
  an arrow `op l ⟶ op k` corresponds to `k ≤ l`, so the transition direction is
  exactly `X_l → X_k`.
- `p : D ⟶ (Functor.const Kᵒᵖ).obj (schemeSpace T)` supplies every structure map
  and its compatibility with every transition. This fixes T at every stage.
- The first conjunction states `MapIsProper (p.app k)` and all three components
  of finite presentation: `IsQuasiCompactPresheafMap` of the map, of its relative
  diagonal, and `MapIsLocallyOfFinitePresentation` on compatible etale charts.
  The atlas predicate is the existing affine-test predicate from
  `SpaceQCSeparatedEtaleLocal`; no second finite-presentation notion is defined.
- The second conjunction applies `IsRepresentableWith (fun _ _ q ↦
  IsClosedImmersion q.left)` to every transition. This includes representability
  and the closed-immersion property on every scheme test, as stipulated by the node.
- `π : (Functor.const Kᵒᵖ).obj X ⟶ D` is a compatible cone with vertex exactly X.
  The third conjunction makes each cone map a representable closed immersion and
  explicitly states `π.app k ≫ p.app k = f`, so every cone map is over T.
- `Nonempty (IsLimit (Cone.mk X π))` is the full categorical universal property,
  not just existence of compatible maps. A limit in the algebraic-space category,
  together with these over-T triangles, is precisely the limit over T: for a cone
  of maps over T the unique factorization is over T by any component triangle;
  an index exists by `Nonempty K`.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category
  of morphisms (locally ringed spaces locally isomorphic to spectra).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (affine-local finite presentation).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; the signature and docstrings were read. The module
  is publicly imported by the morphism-properties module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsLocallyOfFinitePresentation`, and the constituent definitions. Its existing
  definition node `def-sfb-space-morphism-properties` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, owned by
  the landed existing:true definition node `def-trf-scheme-algebraic-space`.
  The actual Yoneda sheaf data and its named algebraic-space proof obligation were
  read again. This definition owner is added to `stmt_deps`; the module is publicly
  imported directly.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap`, the quasi-compact atlas predicate for affine tests.
  Its landed existing:true definition owner
  `def-sfb-space-quasi-compact-presheaf-map` is added to `stmt_deps`.
- `def-weil-size-convention` is a metatheoretic convention, with no declaration.
  It is rendered by the explicit universe `u` and the existing universe-polymorphic
  scheme and algebraic-space categories.

The item statement is unchanged. The only node changes are its Lean record and
three added, already landed statement dependencies exposing the reused interfaces.
There are no new nodes and no dependency repairs.

The proof docstring follows all eight accepted steps. Non-public proof imports retain
all currently recorded project/upstream proof modules: `SpaceSeparatedFiniteTypeFPEnvelope`,
`AlgebraicSpaceFlatProperFpLocality`, `EventuallyClosedImmersion`, and `ProjectiveSpace`.
The generic fibre-products module is already public. Mathlib proof leaves are exposed
by `Morphisms.Immersion`, `Morphisms.Finite`, and the public scheme morphism imports.
The remaining algebraic-space proof nodes have no current Lean record, so no module
can yet be imported for them; the docstring names their use without restating them.

Edge cases checked: empty T and X are allowed, with a nonempty constant diagram of
empty spaces; for an already finitely presented proper f the one-point index and
identity cone suffice; no finite-presentation condition is imposed on the limit,
so closed subspaces cut out by infinitely generated ideals are not excluded.
There is no characteristic restriction, nonempty-source restriction, affine-base
restriction, or extra representability assumption on f. The order orientation and
all over-base triangles were checked explicitly. Every variable and universe is
bound; `autoImplicit false` is set.

Searches actually run:

- `msearch.py ... leanfinder`: "A proper algebraic space over a quasi compact quasi
  separated scheme is an inverse limit of proper finitely presented algebraic spaces
  with closed immersion transition and cone maps". Eight hits, all relevant hits
  scheme-only (`IsProper`, affine-transition scheme limits); no exact space theorem.
- `msearch.py ... loogle`: `"IsProper", "FinitePresentation"`. Zero hits.
- `msearch.py ... grep`: `proper.*limit|limit.*proper|AlgebraicSpace`, restricted to
  AlgebraicGeometry. Twenty-five hits, none an algebraic-space approximation theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for proper/limit and
  the candidate declaration names found the scheme-only
  `AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_limit` in
  `WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimit`. Its full
  signature was read: X is a scheme and the conclusion includes a further envelope
  clause, so it cannot bind this algebraic-space node. The new name lies in the
  `AlgebraicGeometry.AlgebraicSpace` namespace and is distinct.
- Direct search for `lem-sfb-proper-space-fixed-base-fp-limit` in
  `lean/WeilConjectures` returned no hit. DAG and Sheaf searches found the existing
  morphism-properties, atlas quasi-compactness and scheme-space interfaces above;
  those are reused rather than copied.

Validation: prescribed `scompile.py`, single file, default 60-second limit. The initial
syntax error (one extra closing parenthesis) was fixed; subsequent compile passed.
The repaired direct definition-module import is checked again by the prescribed
compile and dry run.
No statement fault or disputed assertion was found.

## Second reading by Q25

A separate pass by this worker reread the node and Lean file after compilation;
no second agent was started, as the dispatch brief forbids it. Independent review
is supplied by the maintainer after delivery, not claimed here.

The pass checked the fixed ambient integer base, the arbitrary qcqs scheme T,
algebraic-space X, intrinsic properness and all three finite-presentation components.
It checked that D and p encode transitions over T, that opposite-order arrows have
the specified direction, that both transitions and cone legs satisfy the full
scheme-test closed-immersion predicate, and that the cone vertex is exactly X.
It checked the equality to the originally supplied f at every stage and the full
limit universal property, including the empty-base case and singleton index.
It also reread both landed existing:true definition owners and their source
signatures. The H2 repair replaces the enlarged-site theorem dependency with
`def-trf-scheme-algebraic-space`, and the etale-locality theorem dependency with
`def-sfb-space-quasi-compact-presheaf-map`. The signature uses the plain definitions
`schemeSpace` and `IsQuasiCompactPresheafMap`, not either theorem. The public import
for `schemeSpace` is now its direct module `EnlargedEtaleRingedSite`. The mathematical
statement, its signature, and its sorry-only proof are unchanged.

## Repair of return H2

Return at immutable head `3e7ade9406e3` identified two theorem nodes incorrectly
used as owners of plain definitions. Applied exactly the requested dependency swaps:
`lem-trf-space-enlarged-etale-ringed-site-model` to
`def-trf-scheme-algebraic-space`, and `lem-trf-space-qc-separated-etale-local` to
`def-sfb-space-quasi-compact-presheaf-map`. Both replacement nodes are landed,
existing:true records of the same definitions used by this signature. Neither
replacement node is edited or duplicated. Also replaced the umbrella public import
`SpaceCotangentRingMap` with the owning `EnlargedEtaleRingedSite` module, as permitted
by the return. Compared the retained sandbox node with current main source: only
`lean` and the added `stmt_deps` differ, and the natural-language statement agrees
verbatim. The delivery wrapper refreshes and rebases against the current server main.
The previous immutable-head clause-by-clause review is retained; no mathematical
statement or proof change is made. Run the prescribed single-file compile, dry run,
and delivery again for this repaired version.
