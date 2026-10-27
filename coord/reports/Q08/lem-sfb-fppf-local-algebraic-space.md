## Worker report

The module `Sheaf.AlgebraicGeometry.FppfLocalAlgebraicSpace` states
`AlgebraicGeometry.isAlgebraicSpace_of_fppf_cover`, with its whole proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes.

Source read: `literature/stacks-project/bootstrap.tex`, Tag 04SK,
`lemma-locally-algebraic-space`, including the paragraph immediately before it
identifying the local-product condition with restriction to the site over each
cover member. Also read `literature/stacks-project/spaces.tex`, Tag 02WQ,
`lemma-coproduct-algebraic-spaces`, which supplies the sufficient chart-size condition.

Hypotheses and conclusion, matched individually:

- The scheme `T` of the prose is named `S : Scheme.{u}`. Explicit universe `u`
  implements def-weil-size-convention, using the project's existing big-site model.
- `F : Sheaf (Scheme.fppfTopology.over S) (Type u)` is exactly a sheaf of sets on
  the big fppf site of `S`.
- `I : Type v` and `T : I → Over S` give the family of schemes over `S`.
  `hcover` asserts membership of their actual arrows in `Scheme.fppfPrecoverage`.
  By `Scheme.ofArrows_mem_precoverage_iff`, this is joint surjectivity and flatness
  and local finite presentation of every member, with no quasi-compactness condition.
- `Fi : ∀ i, AlgebraicSpace (T i).left` and the presheaf isomorphisms `e` state that
  the restriction of `F` to each cover member is an algebraic space. The actual
  restriction is `(Over.map (T i).hom).op ⋙ F.obj`: on `W → T i` it has value
  `F(W → T i → S)`, with the same restriction maps. This is the equivalent formulation
  explicitly authorized in the paragraph preceding 04SK. Viewed over `S`, its
  extension has sections `Σ (a : W → T i), F(W)`, exactly `(h_{T i} × F)(W)`;
  this identification adds no representability, diagonal, or descent assumption.
- `V : ∀ i, Over (T i).left` gives the scheme charts. The natural transformations
  `p i : yoneda.obj (V i) ⟶ (Fi i).obj.obj` are precisely their chart maps.
  `hp i` supplies `AlgebraicSpace.IsEtale` and `AlgebraicSpace.IsSurjective`;
  both existing predicates include representability on every scheme test.
- `Vcoprod : Over S`, the arrows `ι` from the underlying `S`-schemes of `V i`,
  and `hV : Nonempty (IsColimit (Cofan.mk Vcoprod ι)))` give exactly a site-valued
  scheme coproduct. The slice's forgetful functor creates these colimits, so this
  is also the scheme coproduct, with its uniquely induced map to `S`.
  It asserts the universal property rather than assuming a global large-coproduct
  instance. It neither demands a smaller indexing universe nor chooses an arbitrary
  replacement map.
- The conclusion `AlgebraicSpace.IsAlgebraicSpace F` says that this same `F` has
  representable diagonal and a representable surjective étale scheme atlas.
- The final sufficient-size sentence is metatheoretic: if the indices and charts are
  small in a common universe and their scheme coproduct belongs to the big site,
  use that coproduct and its coprojections as `Vcoprod`, `ι`, `hV`. Thus it is exactly
  the hypothesis already quantified over, not an additional mathematical restriction.
  The module docstring and theorem docstring spell this out.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (lines 35–75); schemes are locally ringed spaces locally affine.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology` (lines 37–54). `GrothendieckTopology.over` is the existing
  slice topology used by the algebraic-space declaration.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
  Read their full signatures and docstrings: the diagonal and atlases are scheme-tested,
  and the category bundles precisely those fppf sheaves satisfying the predicate.
- `Mathlib.AlgebraicGeometry.Limits`: small-index scheme coproduct instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι` (lines 178–244). A concrete cofan
  records the coproduct condition also for a potentially larger index universe.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct`:
  `AlgebraicGeometry.algebraicSpace_coproduct`, whose chart-size hypothesis is likewise
  a site-valued scheme cofan with a colimit witness. Imported for the recorded proof.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.map` (lines 197–215) keeps the
  underlying scheme and composes its structure map with the given base map.

Recorded proof modules are imported plainly: `AlgebraicSpaceCoproduct`,
`FppfSheafCoproductPartition`, `SpaceChangeBase`, `SpaceLocalPropertiesChartTest`,
`EnlargedEtaleRingedSite`, and the Mathlib pullback, precoverage, flatness and finite
presentation modules. Read the relevant declarations and proof docstrings, including
`exists_spaceChangeBase` and both chart-test statements. The proof-only dependency
lem-sfb-fppf-space-atlas-bootstrap has no recorded declaration/module in the current
DAG, so no fabricated import is added; it is referenced in the natural-language proof.
It is not needed to type this statement. The theorem docstring carries all four
accepted proof steps, including the partition calculation and point-class argument.

Edge cases checked: empty `I` forces an empty base by joint surjectivity, without
excluding that case; the identity singleton cover recovers the supplied local space;
infinite covers require no quasi-compactness; empty chart summands are permitted;
no assumption on characteristic, nonemptiness, separation, or finiteness is introduced.
The independent index universe `v` has no smallness instance: the actual cofan records
exactly the necessary coproduct size bound. Every variable and universe is explicit,
with `set_option autoImplicit false`.

Searches actually run using `msearch.py Q08 lem-sfb-fppf-local-algebraic-space`:

- leanfinder: “An fppf sheaf is an algebraic space if it is an algebraic space locally
  for an fppf covering of the base” — eight hits, including local finite presentation,
  finite type, Zariski scheme representability and the étale topology; no exact match.
- loogle: `"AlgebraicSpace"` — zero hits.
- grep: `AlgebraicSpace|fppfLocal|locally_algebraic_space` in `AlgebraicGeometry` — zero hits.
- leansearch: “Algebraic space representability is local for an fppf cover of the base” —
  eight hits on scheme representability and Zariski locality; no exact match.
- Local `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `locally.algebraic.space|fppf.local|fppfLocal|algebraicSpace.*[Ll]ocal` found related
  locality/descent modules and proof-docstring mentions of this node, but no statement
  of the claimed theorem. Searching its exact id in `lean/WeilConjectures` found none.
  Searching the proposed declaration name across both roots, Mathlib and
  `dag/lean_names_upstream.json` found none.

Validation: `scompile.py` compiled the delivered file both under its sandbox module
name and its library module name, with no errors or warnings (8.9 s and 5.0 s).
No statement dispute or source fault was found.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
