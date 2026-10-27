## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal` states
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_baseChange_and_fppfLocal`, with one
`sorry` proof. It defines nothing. The informal statement, source, five proof steps,
and proof dependencies are unchanged. Two already landed definition nodes are added
to `stmt_deps`: `def-sfb-space-quasi-compact-presheaf-map` and
`def-sfb-space-morphism-properties`, for the existing predicates used in the signature.
No new node, dependency repair, statement correction, or disputed assertion is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The spaces are `{X Y : AlgebraicSpace S}`;
  the arbitrary map is `(f : X ⟶ Y)`. No representability, separatedness,
  quasi-separatedness, finite type, or compactness assumption is imposed on `f`.
- The size convention is rendered by the explicit `universe u w`. Schemes, test
  fields, atlases, and values of the underlying presheaves use the established `u`
  of `AlgebraicSpace S`. The arbitrary small cover has index `(I : Type w)`, with
  no nonemptiness, finiteness, or relation between `w` and `u` required.
- A quasi-compact space `Z` means exactly
  `∃ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
   CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
  `CompactSpace` has no Hausdorff requirement. `IsEtale` includes scheme-test
  representability, so this is a representable surjective etale scheme atlas.
  No arbitrary choice of an atlas or hollow construction occurs.
- The first conjunct is an explicit normalization of the existing
  `IsQuasiCompactPresheafMap f.hom.hom`: it is equivalent to testing every
  `(Z : AlgebraicSpace S)` satisfying precisely that atlas condition and every
  `g : Z ⟶ Y`, and requiring an atlas with the identical conditions for
  `Limits.pullback f.hom.hom g.hom.hom`. Thus the all-quasi-compact-space tests in
  the node remain in the signature, rather than being silently replaced by a
  special case. The affine-test equivalence renders the definition paragraph;
  it introduces no second definition of quasi-compactness.
- The second conjunct assumes `IsQuasiCompactPresheafMap f.hom.hom` and quantifies
  over every `(Y' : AlgebraicSpace S) (g : Y' ⟶ Y)`. Its conclusion is
  `IsQuasiCompactPresheafMap (Limits.pullback.snd f.hom.hom g.hom.hom)`.
  The second projection is exactly `X ×_Y Y' → Y'`.
- The third conjunct introduces every small family `(Yᵢ : I → AlgebraicSpace S)`
  and `(g : ∀ i : I, Yᵢ i ⟶ Y)`. Its three hypotheses are respectively
  `∀ i, MapIsFlat (g i)`, `∀ i, MapIsLocallyOfFinitePresentation (g i)`, and
  `IsJointlySurjective (fun i ↦ (g i).hom.hom)`. The first two use every compatible
  pair of etale scheme charts, exactly as in the node, without requiring the
  family maps themselves representable. The third is the recorded condition on
  field-valued point classes, allowing extension of the representative's field.
- The conclusion of that conjunct is the required iff between the global
  predicate and `∀ i, IsQuasiCompactPresheafMap
  (Limits.pullback.snd f.hom.hom (g i).hom.hom)`, i.e. all the base changes
  `X ×_Y Y_i → Y_i`.

The limits in the signature are actual presheaf pullbacks. The forgetful functor
from fppf sheaves preserves limits, so they represent the underlying presheaves
of the sheaf fibre products in `lem-trf-space-fibre-products-etale-covers`.
This avoids introducing a second bundled algebraic-space pullback. Atlases and
properties are invariant under the canonical comparison isomorphism. The main
conjunct on all space tests states the intended meaning explicitly, even though
its affine-test interface is convenient for later consumers.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, and `IsSurjective`; the latter predicates give
  representing pullback squares on every scheme test.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, on the underlying atlas scheme.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap`, the already owned
  affine-test atlas predicate, not the stronger old joint-surjectivity convention
  in that module's etale-locality theorem.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`. Their underlying scheme
  predicates are `AlgebraicGeometry.Flat` from
  `Mathlib.AlgebraicGeometry.Morphisms.Flat` and
  `AlgebraicGeometry.LocallyOfFinitePresentation` from
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Their full affine-local
  definitions and docstrings were read; flatness agrees with the stalkwise node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
  Its full signature quantifies over every field representative and a field
  extension lift, exactly the recorded point-class notion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. The module is a public statement dependency;
  its first theorem supplies closure and the universal property of the sheaf limit.
- Proof-only imports include `AlgebraicSpaceAffineEtaleCover` for
  `exists_affine_etale_cover_and_point_topology`,
  `AlgebraicSpaceFlatLfpUniversallyOpen` for
  `universallyOpen_of_flat_of_locallyOfFinitePresentation`, and Mathlib's
  `AffineScheme` / `Morphisms.QuasiSeparated` for the two clauses of the affine
  scheme qcqs leaf. They are plain imports. The three proof nodes without Lean
  records (`lem-a1-space-finite-affine-subatlas`,
  `lem-a1-space-point-open-calculus`, `lem-sfb-qc-space-affine-etale-atlas`) cannot
  yet be imported; their uses are retained explicitly in the proof docstring.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no
  module or declaration to import.

Sources read: local Stacks `spaces-morphisms.tex`, definition-quasi-compact
(Tag 03HE) and lemma-base-change-quasi-compact (03HF);
`spaces-descent.tex`, lemma-descending-property-quasi-compact (041L);
`spaces-topologies.tex`, lemma-zariski-etale-smooth-syntomic-fppf-fpqc (0DFQ).
The node's proof expands the latter's finite affine refinement, with arbitrary
quasi-compact space tests instead of only affine tests. The declaration docstring
retains all five proof steps and identifies the initial affine-test normalization.

Edge cases checked mathematically:

- The empty index type is admitted. Joint surjectivity then excludes every
  target field-valued point, so `Y`, and consequently `X`, are empty. Global
  quasi-compactness holds; the local condition is the empty universal statement.
- Empty tests admit the empty quasi-compact scheme as their atlas. The finite
  chart selection in the proof can be empty and gives the empty pullback.
- For empty `X` and arbitrary `Y`, every test pullback is empty, so the statement
  has the expected value. Empty `Y` forces `X` empty as well.
- The identity map passes the full space-test condition: its pullback is the
  test space with its given quasi-compact atlas. The one-member identity cover
  recovers the same property on both sides of descent.
- Arbitrarily infinite families and non-quasi-compact family members are allowed;
  only finitely many affine charts over a fixed quasi-compact test are selected.
- Flat lfp maps need not be representable and may have nontrivial relative
  diagonal. The chart predicates do not insert representability or separation.
- The finite-atlas/topological argument never assumes intersections of affine
  charts quasi-compact, so no quasi-separatedness enters.

Searches performed before writing:

- `msearch.py ... leanfinder "Quasi compact morphisms of algebraic spaces are stable
  under arbitrary base change and local on the target for a jointly surjective
  flat locally finitely presented family"`: 8 hits, all scheme morphism results,
  including `quasiCompact_isStableUnderBaseChange`; no algebraic-space match.
- `msearch.py ... loogle '"QuasiCompact", "DescendsAlong"'`: 12 hits concerning
  scheme descent and scheme properties; no exact match.
- `msearch.py ... leansearch "Quasi compact algebraic space morphisms descend along
  jointly surjective flat locally finitely presented covering families"`: 8 hits,
  all scheme quasi-compactness/descent APIs, not the algebraic-space statement.
- `msearch.py ... grep 'AlgebraicSpace|MapIsQuasiCompact' AlgebraicGeometry`:
  zero Mathlib hits. The scheme APIs do not give this statement.
- `rg` over `lean/WeilConjectures` for algebraic spaces, quasi-compactness and the
  item's id found no implementation; direct item-id search returned no hit.
- `rg` over `lean/Sheaf` found the existing affine atlas predicate in
  `TraceFormula/SpaceQCSeparatedEtaleLocal.lean`, its all-quasi-compact-scheme
  characterization and base-change lemma in `SpaceQuasiCompactAffineTests.lean`,
  and chart predicates in `AlgebraicSpaceMorphismProperties.lean`. These are reused.
  The four-property fppf theorem concerns affine/finite-type/quasi-finite/separated
  morphisms and is downstream of this item, so it is not imported or reused as a
  purported proof of quasi-compactness descent.
- `rg` over the DAG identified the two existing definition owners above. There
  is no need to create a node or another definition. Name search for
  `quasiCompact_baseChange_and_fppfLocal` in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` returned no collision.

Validation: all compilation uses `scompile.py` against the published server library.
The initial compile identified the namespace collision with `AlgebraicSpace.pullback`;
the limit is now explicitly `Limits.pullback`. No proof was filled in.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
