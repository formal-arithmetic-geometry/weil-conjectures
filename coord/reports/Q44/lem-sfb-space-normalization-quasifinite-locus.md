## Worker report

The single module `Sheaf.AlgebraicGeometry.SpaceNormalizationQuasiFiniteLocus` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_normalization_quasiFinite_locus`.
It has one postponed theorem and no definitions. Its proof is `sorry`, with the five
DAG proof steps in its docstring. No statement correction or disputed statement is needed.

Read the statement, all statement-dependency nodes and their recorded interfaces, and
Stacks `spaces-morphisms.tex`, lemma-finite-type-separated (0ABR) and
lemma-characterize-normalization (0823). The source agrees with the DAG statement.
The exported theorem has no chosen normalization object: it quantifies over the fixed
factorization specified in the node.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `V Y N : AlgebraicSpace S` are the node's
  algebraic spaces over that base. All universes and variables are explicit, and
  `set_option autoImplicit false` is set. Scheme tests have exactly the universe of
  the existing algebraic-space definition; there is no smaller independent test universe.
- The morphism is `f : V ⟶ Y`. The hypothesis `hf : IsRepresentableWith
  (fun _ _ p ↦ LocallyOfFiniteType p.left) f.hom.hom` expresses both representability
  and local finite type on scheme tests. Unpacking the recorded IsRepresentableWith
  gives the representing scheme, its scheme projection, and its cartesian square.
  Combining these two stated assumptions avoids a redundant representability binder;
  it adds no scheme-chart choices or further properties.
- Separatedness is `hsep : MapIsSeparated f`, whose existing definition is precisely
  representability of `pullback.diagonal f.hom.hom` by closed immersions.
- Quasi-compactness is `hqc : MapIsQuasiCompact f.hom.hom`. Its existing definition
  tests every affine scheme and requires compactness of the point space of the actual
  presheaf pullback, with the recorded atlas topology. Thus finite type is exactly
  local finite type plus quasi-compactness; no qcqs assumption on Y is imposed.
- The fixed normalization factorization is `g : V ⟶ N`, `ν : N ⟶ Y`,
  `hfactor : g ≫ ν = f`. Integrality is `hν : IsRepresentableWith
  (fun _ _ p ↦ IsIntegralHom p.left) ν.hom.hom`.
- For every factorization through an integral `π : Z ⟶ Y`, `huniv` supplies exactly
  one `c : N ⟶ Z` satisfying `g ≫ c = h ∧ c ≫ π = ν`. The second equation makes
  c a Y-morphism; the first is its required compatibility with the incoming arrow.
  Both equations occur inside the unique-existence predicate, as in Tag 0823.
- The open in N is `∃ W : OpenSubspace N` using the recorded open-subfunctor notion.
  Its full inverse image is literally `W.val.preimage g.hom.hom`, with its inclusion
  `.ι`. The first conjunct says this inclusion is representable by open immersions,
  recording the induced open-subspace structure.
- The induced map from that full inverse image to W is the existing canonical
  `Subfunctor.fromPreimage`, and the second conjunct asserts `IsIso` of this very map.
  This is not an arbitrary isomorphism of the two functors. Pointwise the preimage is
  the set of sections whose g-image lies in W, hence is the canonical open sheaf
  fibre product V ×_N W. Since it is representably open in V, it has the induced
  open-subspace structure. No replacement by a mere point subset is made.
- The third conjunct identifies `pointImage` of the full inverse-image inclusion
  with precisely the pointwise quasi-finite locus. On the right, T and `a : h_T → Y`
  are an arbitrary existentially chosen representable etale scheme chart (`IsEtale a`).
  `U`, `q : h_U → V`, and `p : U → T`, with
  `IsPullback q (yoneda.map p) f.hom.hom a`, are an actual scheme representative
  of V ×_Y T with both projections. A point `x : U.left` satisfies
  `schemePointMap q x = v` and `p.left.IsQuasiFiniteAtPoint x`. This is the exact
  recorded Stacks predicate from pqf-def-quasifinite, including its finite-type
  requirement. The node defines quasi-finiteness using existence of such a lift;
  the equivalent every-lift characterization is not substituted as an extra hypothesis.

Dependency declarations used in the public statement:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (the existing sheaf-fibre-product convention).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`; `Point` and `schemePointMap` from its public
  `AlgebraicSpacePointClasses` dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, via
  the existing `MapIsSeparated` definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom` (the integral
  declaration recorded by def-weil-finite-integral-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFiniteAtPoint`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`.
- `Mathlib.CategoryTheory.Subfunctor.Image`: `Subfunctor.preimage` and
  `Subfunctor.fromPreimage`, publicly imported by the open-subspace module.

The two already-landed definition nodes `def-sfb-space-morphism-properties` and
`def-sfb-proper-curve-moduli` are added to stmt_deps solely to cite the existing
separatedness and quasi-compactness definitions. They are not new notions, repairs,
or additional mathematical hypotheses. All other original node fields are preserved.
The size-convention node is metatheoretic and is implemented by explicit universes.

All stated proof-dependency modules are imported privately, except those also used
by the public statement. The scheme-normalization leaf and universal property are
in Mathlib.Normalization and Mathlib.ZariskisMainTheorem. The project modules
QuasiFiniteAtPointIsolated, IsolatedFiberPointQuasiFiniteAffinePairs,
SpaceInvariantOpenQuotient, AlgebraicSpacePointOpenCalculus, and
SpaceOpenImmersionEtaleLocal are imported directly. The two proof-only nodes
lem-sfb-space-integral-factorization-etale-base-change and
lem-sfb-scheme-quasifinite-at-base-change currently have no recorded declaration or
mathlib_match, so have no module to import; their proof roles are retained verbatim
in the DAG and named in the theorem docstring. They are not prerequisites for typing
this statement, which explicitly states its factorization hypotheses.

Edge cases checked before writing:

- Empty V: the universal property tested against the empty integral factorization
  forces N empty. The open W and its preimage may be empty. No nonemptiness is assumed.
- The identity or an integral finite-type morphism: the normalization can be V itself,
  and W can be the full open. Nilpotents remain in the sheaf and its isomorphism.
- A¹ → Spec k: the quasi-finite locus is empty and W may be empty. No quasi-finiteness
  everywhere is assumed, nor is the whole normalization map required to be open.
- Spec k ⊔ A¹ → Spec k: the normalization separates the two components, and W is the
  finite component. This checks the full inverse-image clause, including points outside
  the quasi-finite locus, rather than just an isomorphism from a chosen restricted open.
- There is no reducedness, characteristic, Noetherian, affine-base, or qcqs-base
  restriction. A chart containing a given lift need not be surjective globally.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "For a representable separated finite type morphism of
  algebraic spaces the quasi finite locus is an open in the relative normalization"`:
  eight scheme-normalization results, including normalizationOpenCover,
  toNormalization, and instQuasiCompactToNormalization; no algebraic-space result.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.toNormalization"`:
  twelve scheme declarations, including normalizationDesc and normalization.hom_ext;
  none states the algebraic-space theorem.
- `msearch.py ... grep "AlgebraicSpace|exists_isIso_morphismRestrict_toNormalization"
  AlgebraicGeometry`: three lines in ZariskisMainTheorem.lean, including the scheme
  theorem at line 206, with no algebraic-space match.
- `msearch.py ... leansearch "The quasi finite locus of a representable separated
  finite type morphism of algebraic spaces is an open in its relative normalization"`:
  eight scheme results, including toNormalization, normalizationDesc and
  LocallyQuasiFinite.recOn; none applies directly to algebraic spaces.
- `rg` across the project's WeilConjectures and Sheaf roots for the node id,
  normalization/quasi-finite and normalization-factorization names found the already
  delivered consumer SpaceEtaleFiniteFpEnvelope and the existing morphism-property
  definitions, but no statement of this theorem. The literal requested
  `grep -rn` of the item id in WeilConjectures returned no hits. The proposed fully
  qualified theorem name and module name are absent from both project roots and
  dag/lean_names_upstream.json.

Validation: prescribed `scompile.py` succeeded in sandbox and library module modes,
with no errors and no warnings (1.8 s and 1.7 s Lean invocations). All writes were
confined to this item's sandbox; no direct Git operation or global build was run.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
