## Worker report

Stated `AlgebraicGeometry.AlgebraicSpace.open_cover_representable_diagonal` in
`Sheaf.AlgebraicGeometry.OpenCoverRepresentableDiagonal`. Its only proof is `sorry`.
No definitions, helper theorems, new nodes, dependency repairs, or statement corrections
are needed. The node copy changes only `lean`.

The previous attempt's complaint concerns an already reviewed stage-1 split.
The current node has that split but no Lean declaration or reviewed_lean attachment.
This delivery supplies its stage-2 statement. No repair note exists for the item.
The example CompactObject module is now withdrawn; I read its node's current upstream
binding and followed the module-mode/public-section convention in the standing brief.

Hypotheses, clause by clause:

- `S : Scheme.{u}` is the base scheme; `Over S` is the category of schemes over it.
  `yoneda.obj T` is exactly `Mor_S(-, T)`.
- `F : Sheaf (Scheme.fppfTopology.over S) (Type u)` is a sheaf of sets on the
  recorded big fppf site. The universe `u` is explicit and polymorphic, with the
  schemes, Hom sets, sheaf values, and small index family in the chosen bound,
  as in the recorded algebraic-space framework. No fixed universe or characteristic
  is imposed. `I : Type u` is the small family of the statement.
- `H : I → Subfunctor F.obj` gives the actual sectionwise subsets, including their
  restriction stability; `hH` says each underlying subfunctor is an fppf sheaf.
- `hopen` uses the recorded `AlgebraicSpace.IsRepresentableWith` with property
  `IsOpenImmersion p.left`. It gives actual scheme-test pullback squares with
  open-immersion projections, precisely the hypothesis on each inclusion.
- `hdiag` is exactly the node's stated pair-of-schemes meaning of representable
  diagonals of H i: for every two schemes and maps into H i, their presheaf
  fibre product `Limits.pullback a b` is representable by a scheme over S.
- `hlocal` gives, for every T and a, an actual `Scheme.Cover.{u}` for
  `Scheme.fppfPrecoverage`. Its arrows are jointly surjective, flat, and locally
  finitely presented; `k : 𝒰.I₀ → I` chooses the index on each covering member.
  The last membership is exactly the restriction of a along that member lying
  in H (k j). The source schemes carry the structure maps `𝒰.f j ≫ T.hom`.

Conclusions, clause by clause:

- The first conjunct quantifies over every test T, its section a, and any opens
  V i representing its inverse images of H i. Their universal property is the
  displayed equivalence for every W and f: restriction of a belongs to H i iff
  `Set.range f.left ⊆ V i`. Factoring through the open subscheme is exactly this
  range criterion for a scheme morphism, including nonreduced schemes. The
  conclusion `(⨆ i, V i) = ⊤` says these opens cover T.
  Existence of such opens is already supplied by `hopen`, and the recorded
  `exists_opens_of_relative_isOpenImmersion` states this characterization.
  Thus this universal conclusion concerns every actual representing family;
  it neither postulates an unrelated choice nor presupposes its coverage.
- For every pair a,b, `Limits.pullback a b` is G. Its canonical common map to F
  is `Limits.pullback.fst a b ≫ a`. `Subfunctor.preimage` along that map is
  exactly G_i = G times_F H i: its sectionwise condition is that the common
  F value lies in H i. This reuses Mathlib's real preimage construction.
- The next conjunct says every G_i's `toFunctor.IsRepresentable`.
- The following conjunct says each actual inclusion G_i into G is
  `IsRepresentableWith` open-immersion scheme projections.
- The next conjunct quantifies over every scheme W, every section c of G on W,
  and every representing family of opens V in W, with the full test-morphism
  membership equivalence. Its union is top. By Yoneda, sections c are precisely
  scheme tests into G. This is the required covering assertion on every test,
  with existence of these opens supplied by the preceding openness assertion.
- The last clause of this pairwise conjunction is G.IsRepresentable, meaning a
  representing object of Over S, not an abstract object in another category.
- The final conjunct uses the recorded `AlgebraicSpace.IsRepresentable` on
  `prod.lift (𝟙 F.obj) (𝟙 F.obj)`, the actual diagonal F into F times F.
  It gives a representing scheme for every scheme base change of that diagonal.
- There is no atlas, algebraic-space assumption on any H i, or coproduct datum
  anywhere in the signature. Thus the last sentence of the node is respected.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`. These are reexported by AlgebraicSpace.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the record's `IsSiteForCoverings`
  governs general site axioms; the sheaf component remains Mathlib `Sheaf` and
  `Presheaf.IsSheaf`, as that dependency's note explicitly specifies.
- `Mathlib.CategoryTheory.Subfunctor.Basic`: `Subfunctor`, `toFunctor`, `ι`;
  `Mathlib.CategoryTheory.Subfunctor.Image`: `Subfunctor.preimage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace.IsRepresentableWith`
  and `AlgebraicSpace.IsRepresentable`. Their full source definitions use actual
  Over-S scheme projections and `IsPullback`, with no unknown data construction.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Yoneda`: `yoneda`, `Functor.IsRepresentable`,
  `Functor.RepresentableBy`. Read the record's upstream isomorphism criterion too.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, and their universal property.
- The size convention is metatheoretic, as its record explicitly says; it is
  rendered by the explicit universe and small index type, with no new predicate.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`:
  `exists_opens_of_relative_isOpenImmersion` and its converse give the exact
  open-subfunctor characterization; `isRepresentable_of_isSheaf_of_zariskiCovers`
  is the proof's 01JJ criterion over S. This module is a public statement-dependency import; the proof also uses
  its criterion and the plain proof import `Mathlib.AlgebraicGeometry.Gluing` (`Scheme.Cover.glueMorphisms`,
  restriction and uniqueness). The remaining proof dependency, Zariski covers
  are fppf covers, is already exported by the public Fpqc import of AlgebraicSpace.

Source and small cases:

Read the entire Tag 02WR statement and proof, in particular its first two proof
paragraphs, and spaces.tex lemma-representable-diagonal (all three equivalent
conditions). The extracted node removes the atlas/coprod assumptions because
those paragraphs use only the hypotheses retained in this node. Read the recorded
relative open-subfunctor equivalences and the full relative 01JJ signature.

The index can be empty: local covering then forces absence of F sections on
nonempty schemes; on the empty scheme the empty cover is allowed. Both asserted
unions then equal top on an empty scheme. No Nonempty binder was introduced.
For a singleton family the open on each actual section is all of its test
scheme. Empty T or T', empty fibre products, repeated opens, disjoint subsheaves,
infinite small families, nonaffine and nonreduced schemes all remain included.
The range condition describes factoring through an open, not an assertion that
arbitrary subsheaf membership is determined by underlying points. Both pairwise
maps are allowed to be equal, and there are no separation or finiteness hypotheses.

Searches actually run through the prescribed msearch wrapper:

- leanfinder: "A sheaf of sets has representable diagonal if an fppf locally
  covering family of open subfunctors has representable diagonals". Eight hits,
  including `Functor.relativelyRepresentable.diag_iff`, `diag_of_map_from_obj`,
  and `Scheme.LocalRepresentability.isRepresentable`; none has the open-cover
  descent hypotheses and all intermediate conclusions of this node.
- loogle: `CategoryTheory.Functor.relativelyRepresentable.diag_iff`; one hit,
  the generic diagonal test equivalence. Read its full signature and docstring;
  it does not establish the local covering or representability of G_i and G.
- grep: `diag_iff|representable.*diagonal` under Mathlib AlgebraicGeometry/Sites;
  zero hits from the wrapper.
- leansearch: "The diagonal of a sheaf covered fppf locally by open subfunctors
  with representable diagonals is representable". Eight hits, again generic
  diagonal equivalences, scheme local representability, and scheme morphism
  properties; none is this statement.
- Direct rg of the item id in both `lean/WeilConjectures` and `lean/Sheaf`:
  zero hits. Direct rg of `open_cover_representable_diagonal` and the proposed
  CamelCase name in Mathlib, both project trees, and the upstream names index:
  zero hits. Broader representable-diagonal/open-cover searches located the
  existing parent `AlgebraicSpaceOpenGluing`, which assumes algebraic summands
  and an algebraic coproduct and concludes algebraicity, so is a distinct node.
  Reused the existing AlgebraicSpace and Subfunctor APIs instead of duplicating them.

No STATEMENT-DISPUTED flag or source fault was found. The first compile identified
only the existing `AlgebraicSpace.pullback` name shadowing the categorical
pullback; all categorical pullbacks are now explicitly qualified `Limits.pullback`.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
