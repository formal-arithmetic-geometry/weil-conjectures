## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineSpaceTarget` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_representation_of_finite_surjective`,
with its proof exactly `by sorry`. It is Stacks 07VS for algebraic spaces, including
non-Noetherian spaces and finite morphisms not of finite presentation. No definitions,
new nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence with the unchanged node:

- The base scheme is `{S : Scheme.{u}}`, with `universe u` explicitly declared.
- The two algebraic spaces over that base are `{X Y : AlgebraicSpace S}`. This is
  the recorded full subcategory of fppf sheaves, not the category of schemes.
- The morphism is `(f : X ⟶ Y)`, hence a natural transformation of the underlying
  sheaves; its presheaf natural transformation is `f.hom.hom`.
- The hypothesis that X is represented by an affine scheme is
  `hX : ∃ U : Over S, IsAffine U.left ∧ Nonempty (X.obj.obj ≅ yoneda.obj U)`.
  `Over S` retains the structure map to S, `IsAffine` is Mathlib's scheme affineness,
  and the isomorphism of presheaves is exactly representability by that scheme.
  This does not assert that the structure map U → S is an affine morphism.
- Finiteness on every scheme test is
  `hfinite : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom`.
  Unfolding the recorded definition quantifies over every `T : Over S` and
  `a : yoneda.obj T ⟶ Y.obj.obj`, and supplies a scheme `U : Over S`, a projection
  `p : U ⟶ T`, and a cartesian presheaf square with `IsFinite p.left`.
  Its square represents exactly X ×_Y T and its second projection; this is the
  scheme-test clause in the node, using its recorded fibre-product interface.
- Surjectivity on field-valued point classes is
  `hsurj : pointImage f.hom.hom = Set.univ`. The existing `pointImage` consists of
  classes of `a.map f` for field-valued representatives a of X; equality to the
  whole target point set means every class has a preimage. It is precisely the
  surjectivity of |f|, without introducing a second map on points or replacing it
  by epimorphism/surjectivity on sections. Its ambient points have the existing
  atlas topology; the surjectivity assertion depends on their underlying set.
- The conclusion is
  `∃ V : Over S, IsAffine V.left ∧ Nonempty (Y.obj.obj ≅ yoneda.obj V)`.
  Thus an affine scheme with its map to S represents Y over S.
- There are no Noetherian, finite-presentation, flatness, nonemptiness, separation,
  or additional site-size hypotheses. All test schemes use the same u as S and
  the recorded AlgebraicSpace interface, so the test condition is not vacuous
  through an independently smaller universe. Point classes live in Type (u+1).

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`. The latter's full
  definition was read, including the `IsPullback q (yoneda.map p) f a` order.
- `def-weil-size-convention` is explicitly a metatheoretic convention with no Lean
  object; `universe u` and the existing size-polymorphic space/test types render it.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, declarations
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme`. The finite-test
  hypothesis uses the existing cartesian-square definition rather than constructing
  another pullback. This statement-dependency module is imported publicly.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
  Its definition extends `IsAffineHom` and requires finite ring maps on affine
  opens. The integral sibling was also inspected; integrality is not substituted
  for finiteness here.
- `def-a1-space-point-topology`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, declarations
  `AlgebraicGeometry.AlgebraicSpace.PointRepresentative.map`, `pointImage`, and
  `pointTopologicalSpace`. Their point type and field representatives come from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` (read in full).

All proof dependencies currently carrying a Lean module are imported without
`public`: point-open calculus, universally closed surjection separation,
change of base, finite/finitely presented approximation, descent over a space
limit, flat/proper/fp locality, eventual finiteness, and eventual surjectivity.
The finite-proper and affine-qcqs Mathlib leaves are supplied by the imports of
`Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (AffineScheme is already in
its public finite-morphism dependency chain). Proof nodes with no recorded Lean
module are not invented in this statement delivery. The theorem docstring
contains all five accepted DAG proof steps with their prerequisite names.

Edge cases checked against the source and signature:

- Empty X: surjectivity forces the target point set empty; the conclusion permits
  the affine empty scheme Spec(0). No `Nonempty` hypothesis on schemes or rings
  excludes this; `Nonempty` only truncates an isomorphism type into a proposition.
- The identity on any affine scheme satisfies the finite-test and image conditions.
- Spec(k) → Spec(k[ε]/ε²) is a finite surjective closed immersion and is included;
  no flatness, reducedness, or characteristic restriction was introduced.
- Arbitrary nonaffine S is permitted. Affineness concerns U.left and V.left, not
  their structure morphisms to S. Conversely, the identity of a nonaffine scheme
  does not satisfy hX just because its structure morphism is affine.
- The conclusion remains over the given S because the representation is in
  presheaves on Over S; no unstructured absolute representation is substituted.

Searches (2026-10-24; raw wrapper output also logged in searches.jsonl):

- `msearch.py ... leanfinder` with “A finite surjective morphism from an affine
  scheme to an algebraic space has affine target”: 8 results, all scheme-only,
  including `IsFinite.toIsAffineHom`, `isFinite_iff`,
  `IsClosedImmersion.isAffine_surjective_of_isAffine`, and
  `isAffine_of_isAffineHom`; none asserts representability of a space target.
- `msearch.py ... leansearch` with the same query: 8 results, including
  `AffineTargetMorphismProperty`, `HasAffineProperty`, and `IsFinite`; no match.
- `msearch.py ... loogle` with
  `"AlgebraicGeometry.IsFinite", "AlgebraicGeometry.IsAffine"`: 0 results.
- `msearch.py ... grep` with
  `AlgebraicSpace|[Ii]sAffine.*[Ss]urjective|[Ss]urjective.*[Ii]sAffine`, restricted
  to Mathlib AlgebraicGeometry: 16 hits. They concern schemes, effective epimorphisms,
  affine-space projections, or closed immersions; no exact space theorem.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, 07VS, the prospective declaration,
  and finite/surjective/affine combinations finds no exact theorem. In particular,
  `WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTarget` was opened:
  `AlgebraicGeometry.isAffine_of_isFinite_surjective` takes X,Y : Scheme,
  so it cannot conclude that an arbitrary algebraic-space target is a scheme.
- Searches for existing affine-space representability predicates found no separate
  definition needed here. The statement combines the existing `IsAffine` and
  Yoneda isomorphism directly, as the landed representability statements do.

Source checked directly: literature/stacks-project/spaces-limits.tex, lines
3374–3420, the complete statement and proof of Tag 07VS (lemma-affine).
The module compiles through the prescribed scompile.py in sandbox and library
modes, with no errors or warnings. No STATEMENT-DISPUTED issue was found.

## Second reading by N0

Author's separate second pass, not an independent agent review (the dispatcher
brief forbids spawning agents; independent review belongs to the maintainer).
I reread the node and the completed Lean file together. The binders cover the same
base, spaces, and map. The source hypothesis and conclusion use the same existential
Yoneda representation with affineness of the underlying scheme. I unfolded
IsRepresentableWith and verified that its square puts p over the test scheme,
so hfinite has exactly the node's projection and ranges over every test map.
I reread pointImage and verified that equality to Set.univ says every target
field-valued class is represented by the image of a source representative; the
quotient equivalence, base map, and field-extension convention are unchanged.
No extra geometric assumptions occur, all universes and variables are bound,
and no new notion duplicates a dependency. The five proof paragraphs reproduce
the accepted node proof rather than the shorter scheme-only theorem. No mismatch
was found and no statement change was made. The server compile is clean.
