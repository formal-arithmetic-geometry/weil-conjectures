## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiAffineAffineDescent` states
`AlgebraicGeometry.AlgebraicSpace.exists_quasiAffine_representation_of_flat_surjective_affine_baseChange`.
Its only theorem has proof `sorry`; it introduces no definitions. The node is copied from
the current shared repository with only `lean` added. The accepted stage-1 split is preserved.
There are no new nodes, dependency repairs, statement changes, or disputed statements.

The source was read at `spaces-descent.tex`, Tag 0423,
`lemma-descending-property-quasi-affine`, specifically the affine flat-surjective reduction
at lines 1690–1719, and `spaces-morphisms.tex`, Tag 03WL,
`definition-quasi-affine`. The source descends a scheme representing the base change,
then identifies the descended scheme with the original algebraic space by fpqc descent.
Over an affine target the absolute quasi-affineness in this node is the relative
quasi-affineness used in that proof.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A scheme S in the prescribed universes | Explicit `universe u` and `{S : Scheme.{u}}`; the recorded algebraic-space interface uses schemes in this universe and values in `Type u`. |
| Affine S-schemes U and V | `(U V : Over S) [IsAffine U.left] [IsAffine V.left]`. `Over S` includes each structure morphism to S. |
| A morphism p:V → U over S | `(p : V ⟶ U)`; commutation with the structure morphisms is part of an Over morphism. |
| Flat p | `[Flat p.left]`; Mathlib's `Flat.iff_flat_stalkMap` identifies it with flatness of all local-ring homomorphisms. |
| Surjective p | `[Surjective p.left]`; this class means surjectivity on underlying points. |
| An algebraic space X over S | `(X : AlgebraicSpace S)`, using the recorded fppf-sheaf full subcategory. |
| A morphism f:X → U | `(f : X.obj.obj ⟶ yoneda.obj U)`; these are natural transformations on S-schemes, exactly the recorded algebraic-space morphisms to a represented scheme. |
| X ×_U V is represented by a scheme P | `∃ P : Over S, ... ∧ Nonempty (yoneda.obj P ≅ Limits.pullback f (yoneda.map p))`. The Yoneda presheaf of V maps to that of U through `yoneda.map p`. |
| P is quasi-affine, including quasi-compactness | `P.left.IsQuasiAffine`. Mathlib's class extends `CompactSpace P.left` and the immersion of its canonical map to Spec of global sections; the following instance makes that map an open immersion. Conversely, a quasi-compact open subscheme of an affine scheme satisfies the class by `Scheme.IsQuasiAffine.of_isImmersion`. |
| X is represented by a quasi-affine scheme Y | `∃ Y : Over S, Y.left.IsQuasiAffine ∧ Nonempty (yoneda.obj Y ≅ X.obj.obj)`. The isomorphism is natural on S-schemes. |
| No further assumptions on f | There is no representability, separation, finite-type, or finite-presentation binder on f. |

The use of a presheaf pullback changes no object: the forgetful functor from sheaves
to presheaves preserves limits, so this pullback is naturally isomorphic to the
underlying presheaf of the sheaf fibre product. A representation of either one is a
representation of the other. The isomorphism is existential under `Nonempty`; no
arbitrary representing map or chosen descent datum replaces a canonical construction.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, and `AlgebraicGeometry.Spec.map`.
  These are available through the public statement imports.
- `def-weil-size-convention` has a convention record, not a Lean object; the explicit
  universe and the already recorded algebraic-space interface implement it here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, and `IsRepresentableWith`. Its full subcategory has fppf sheaves
  as objects and natural transformations as morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`, together with its
  recorded fibre-product and étale-cover interface. It is a public import; the
  statement uses its underlying presheaf fibre product without duplicating the notion.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, reused through
  `Scheme.IsQuasiAffine`, without a second compactness definition.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `AlgebraicGeometry.Scheme.IsQuasiAffine`
  and its canonical-open-immersion instance supply the exact absolute notion.

Recorded proof dependencies are imported without `public`: the upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` for `IsQuasiAffineHom`,
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` for `Over.DescentDatum`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf` for
`existsUnique_section_and_eq_of_fpqc_cover`,
`Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality` for
`isQuasiAffineHom_iff_of_affine_open_cover`, and
`Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent` for
`Over.DescentDatum.isEffective_of_isQuasiAffineHom_fpqc`.
Mathlib's `Morphisms.Affine`, `Morphisms.Separated`, and `Sites.Fpqc` imports supply
the affine-locality/permanence and fpqc base-change/subcanonicality proof leaves.
`lem-sfb-scheme-quasi-affine-fpqc-descent` is currently an unstated proof dependency:
its module is omitted until it is stated. Its notion is already `IsQuasiAffineHom`,
and its proof is not needed to type this stage-2 statement. No proof dependency was removed.
The docstring records all six steps of the accepted proof with their node citations.

Edge cases checked before finalizing:

- The empty affine scheme is allowed; no nonempty hypothesis on U, V, P, or Y is
  present. If V is empty, surjectivity forces U empty; the algebraic space mapping to
  empty U is itself represented by the empty scheme. The empty open of an affine
  scheme is quasi-compact and quasi-affine in the class used here.
- The identity cover is allowed and simply recovers the assumed representation.
- Neither S nor f is assumed separated, of finite type, or of finite presentation.
  Separation and quasi-compactness of the resulting Y are conclusions contained in
  quasi-affineness, rather than hidden assumptions on X.
- No independently smaller test-scheme universe or extra equality of universes is
  imposed: Yoneda tests all objects of the existing `Over S` category.
- No chosen representative is required in the input: `h` is an existence statement,
  and both representation isomorphisms retain their full presheaf naturality.

Searches for an existing declaration (preserved search log and fresh checks):

- `msearch.py`, LeanFinder, query “An algebraic space over an affine scheme is
  represented by a quasi affine scheme if its faithfully flat affine base change is
  quasi affine”: eight hits, including `Scheme.IsQuasiAffine`,
  `Scheme.IsQuasiAffine.of_isAffineHom`, and affine-scheme declarations; none states
  representability descent of an algebraic space.
- `msearch.py`, Loogle, query `"IsQuasiAffine", "DescendsAlong"`: zero hits.
- `msearch.py`, LeanSearch, query “An algebraic space becomes a quasi affine scheme
  after a faithfully flat affine base change then it is a quasi affine scheme”:
  eight hits on absolute quasi-affine scheme results and generic affine-property
  base change; none states this algebraic-space result.
- `msearch.py`, grep in Mathlib `AlgebraicGeometry`, query
  `QuasiAffine.*[Dd]esc|[Dd]esc.*QuasiAffine|quasi.affine.*fpqc|fpqc.*quasi.affine`:
  zero hits. The earlier broader `quasi.affine|IsQuasiAffine` search found the
  Mathlib quasi-affine definition and affine-transition limits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for quasi-affine/descent names
  found the existing relative notion, scheme target locality, and effective descent
  of a specified scheme datum. Those do not identify the original algebraic space
  with a quasi-affine scheme and hence do not already state this node.
- `grep -rn` for this node id under `lean/WeilConjectures` and `rg` for the proposed
  declaration name under both source roots and `dag/lean_names_upstream.json`:
  no existing declaration for this node.

Validation: the prescribed `scompile.py` checked this file alone against the live
server library in both sandbox and library module forms, with exit code zero and
no compiler warnings. The node's signature is extracted verbatim from the file.
The previous stage-1 unchanged-item rejection is superseded for this assignment by
the explicit stage-handoff paragraph in `coord/brief-stage2.md` §0: the item is queued
at stage 2 and lacks a Lean record, so this is a statement delivery preserving the split.

## Second reading by NQ

No second reading by another worker: the dispatch brief forbids starting other agents.
Since 2026-10-17 the worker delivers directly; the maintainer's independent review
is the independent reading. The clause table above records this worker's own check
with the node and module open and does not claim an independent review.
