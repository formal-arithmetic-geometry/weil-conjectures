## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable`
states `AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_separated_locally_quasi_finite`.
Its sole theorem has the stage-2 `sorry` proof. No new notion, dependency repair,
statement correction, or proof split is needed. Only the item's `lean` field changes.

The previous blocked dispatch confused stages: the current node's `split_report` and
`reviewed` record, and the ledger at 2026-10-18 02:01 UTC, record N9's stage-1 split.
There is no `lean` record. This delivery preserves that reviewed split verbatim and
supplies its stage-2 statement; it neither splits the node again nor replaces a
landed Lean declaration.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the universe is explicitly bound.
- The scheme over `S` is `(T : Over S)`, including its structural scheme morphism.
- `(E : AlgebraicSpace S)` uses the recorded full subcategory of fppf sheaves with
  representable diagonal and a representable surjective etale scheme atlas. No
  extra presentation or chosen atlas is assumed.
- The morphism `f : E → T` is `(f : E.obj.obj ⟶ yoneda.obj T)`. Algebraic-space
  morphisms are natural transformations on `Sch/S`; `yoneda.obj T` is exactly
  the functor of points of the target scheme. Using this presheaf directly
  requires no new chosen algebraic-space structure on a represented sheaf.
- Every scheme chart is quantified as `(V : Over S)` and
  `(a : yoneda.obj V ⟶ E.obj.obj)`. The implication `IsEtale a → ...` uses the
  dependency's predicate, which includes representability and etaleness after
  every scheme base change. The chart need not be surjective.
- Its composite with `f` is `a ≫ f`. The fully faithful Yoneda embedding gives
  its unique scheme morphism `yoneda.preimage (a ≫ f) : V ⟶ T`; `.left` is
  its underlying scheme morphism. Thus
  `Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f)).left` renders
  precisely the stated chartwise hypothesis. This is the recorded Stacks
  predicate, including local finite type, rather than Mathlib's weaker
  `LocallyQuasiFinite` predicate.
- The relative diagonal is `pullback.diagonal f`, into the presheaf pullback
  `E ×_{h_T} E`. It is the canonical diagonal supplied by Mathlib, not a new
  arbitrary map or a product over `S` in place of the relative product over `T`.
- `hsep` applies the recorded `IsRepresentableWith` to that diagonal, using
  `fun _ _ p ↦ IsClosedImmersion p.left`. This quantifies over every scheme
  test map into the relative square and requires a representing scheme
  pullback square whose scheme projection is a closed immersion. It is
  exactly the stipulated closed-immersion condition after every scheme base
  change. Closed immersions are invariant under isomorphism, so existence
  of the representing witness has the usual testwise meaning.
- The conclusion `∃ (Z : Over S) (g : Z ⟶ T)` supplies a scheme over `T`:
  `Z.left` is the scheme and `g.left` its map to `T.left`; the `Over S`
  triangle expresses its induced structural map to `S`.
- `(e : yoneda.obj Z ≅ E.obj.obj)` is the isomorphism of represented functors.
  Both are fppf sheaves and algebraic spaces, so the presheaf isomorphism
  is equally an isomorphism of algebraic spaces. The equality
  `e.hom ≫ f = yoneda.map g` states that the isomorphism is over `T`.
  Thus the conclusion includes the required relative compatibility, not
  just schemehood of the underlying sheaf.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. Read their
  full structure definitions and docstrings.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsEtale`, and
  `IsRepresentableWith` in its namespace. Read their full definitions and
  docstrings; in particular the scheme-valued pullback witnesses in the last.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, with
  `IsQuasiFiniteAtPoint`. Read the finite-type affine-neighbourhood definition,
  its dependency on `Algebra.IsQuasiFiniteAtPrime`, and the docstrings.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and `pullback.lift`.
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal` supplies
  `CategoryTheory.Limits.pullback.diagonal`; read its definition as the lift
  of the two identity maps and its full signature and docstring.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; read its closed-embedding and
  surjective-stalk-map fields and docstring.
- `CategoryTheory.Functor.preimage`, in
  `Mathlib.CategoryTheory.Functor.FullyFaithful`, and its `map_preimage` and
  `preimage_map` identities were read. Since Yoneda is fully faithful, this
  construction picks the unique map corresponding to the specified composite;
  it introduces neither arbitrary mathematical data nor a new definition.

The eight-step proof docstring follows the node's unchanged reviewed proof,
including its local affine reduction, finite relation, quotient, schematic
open-image descent, and final Yoneda compatibility over `T`. Proof-only modules
are imported privately: `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
(finite locally free), `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`
(the scheme criterion), `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`,
`Sheaf.AlgebraicGeometry.EtaleRelationQuotient`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, and
`Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange`. The Mathlib proof leaves use
`Sites.Fpqc`, `Morphisms.Etale`, `Morphisms.Finite`, `Pullbacks`, and the already
publicly imported `Morphisms.ClosedImmersion`. The four new N9 stage-1 supporting
statements have no Lean declarations yet; their node ids are retained explicitly
in the docstring. They are proof dependencies, not missing statement notions.

Source and edge cases checked before writing:

- Read `literature/stacks-project/spaces-morphisms.tex`, the statement and proof
  of `proposition-locally-quasi-finite-separated-over-scheme` (Tag 03XX).
  It assumes a representable target, local quasi-finiteness and separatedness,
  with no quasi-compactness or Noetherian assumptions. The node is its stated
  chartwise formulation with the relative representing isomorphism made explicit.
- Empty `E` is included and is represented by the empty scheme over `T`.
  No nonemptiness condition on `E`, the base, or any chart is imposed.
- Empty `T` forces the given space over it to be empty. Keeping `f` explicit
  retains this case, rather than accidentally providing an unrelated structure map.
- An infinite disjoint union of copies of `T` is permitted. Its separated
  etale structure map is locally quasi-finite and need not be quasi-compact;
  there is no finite-atlas, finite-index, or quasi-compact hypothesis.
- For a represented space `E = h_Z`, the identity chart is tested by `hqf`:
  it recovers local quasi-finiteness of the actual given map `Z → T`.
  The diagonal hypothesis is precisely its relative closed diagonal.
- The target `T` need not equal `S` or be affine or separated over `S`.
  `pullback.diagonal f` and the commuting equality retain this generality.
- No base-field or characteristic restriction occurs. All schemes and test
  schemes range over the same universe as the recorded algebraic-space notion.

Searches for an existing statement:

- `msearch.py leanfinder`: “A separated locally quasi-finite algebraic space
  over a scheme is represented by a scheme”. Eight hits, including
  `AlgebraicGeometry.LocallyQuasiFinite`, scheme separatedness, and finite-map
  permanence. All are scheme predicates or facts, not this space theorem.
- `msearch.py loogle`: `"AlgebraicSpace", "IsSeparated"`; zero hits.
- `msearch.py grep`: `AlgebraicSpace|algebraic.space.*quasi.finite`; zero hits
  in Mathlib.
- `rg` in upstream `WeilConjectures` for `AlgebraicSpace` and the exact node id:
  no hits. Searches for separated/quasi-finite combinations find only scheme
  facts and unrelated compactification or six-functor results.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for `exists_scheme_of_separated`,
  separated/locally-quasi-finite names, and algebraic-space modules: found
  `exists_scheme_of_separated_etale` and
  `affine_etale_relation_separated_locally_quasi_finite`, and the quotient
  representability machinery. Read the relevant signatures and docstrings.
  The first assumes the stronger etale chart condition and concludes an etale
  representing map; the second concerns the affine atlas relation, and the
  quotient lemma only represents its scheme base changes. None is this node.
- `rg` in `dag/lean_names_upstream.json` for the node id, proposed declaration,
  and `AlgebraicSpace`: no corresponding declaration.

No statement dispute or node fault was found. No new nodes or dependency modules
are delivered. The required `scompile.py` compilation passed cleanly for both
sandbox and library positions, under the unmodified 60-second limit; the final
module took approximately two seconds per position.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
