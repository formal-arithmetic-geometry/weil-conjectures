## Worker report

Stage 2, Q60, 2026-10-23. The accepted stage-1 split is preserved. The inherited
BLOCKED ending concerned stage-1 re-splitting, whereas coord/brief-stage2.md §0
explicitly permits this stage-2 assignment. The live node has no Lean record,
coord/queue.tsv lists it at stage 2, and no released repair note exists.

The module Sheaf.AlgebraicGeometry.StackReducedLocallyNoetherianFppfDescent states
AlgebraicGeometry.exists_reduced_locallyNoetherian_smoothAtlas_of_fppf_cover.
Its only theorem has proof `sorry`; it introduces no definitions or axioms.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. `Over S` gives precisely S-schemes and
  S-morphisms. Explicit universes `u v w` retain arbitrary total-category object
  and morphism sizes independently of the scheme universe.
- The stack Z is `F : BasedCategory.{v, w} (Over S)`. Its total category retains
  objects and automorphisms. `hstack : IsFppfModuliStack F` supplies fibredness in
  groupoids and the big-fppf descent condition, exactly as the item requires.
- The algebraic-stack diagonal is `hdiag : HasAlgebraicSpaceDiagonal F`.
  The remaining algebraicity hypothesis is `hatlas`, existence of a scheme W
  with `IsSmoothModuliAtlas F W q`. Algebraicity is deliberately unpacked:
  `IsAlgebraicModuliStack` uses the etale stack condition, while this item's own
  definition specifies fppf stack descent. Adding both stack predicates would
  repeat the same mathematical requirement. The existing smooth-atlas predicate
  is reused, with no private replacement.
- V is `V : Over S`; its morphism p is
  `BasedFunctor (discreteModuli (yoneda.obj V)) F`. This is the recorded interface
  for a morphism from a scheme to a fibred groupoid over S.
- Representability of p is the first part of `hp`: for every scheme T and map
  t into F there are an algebraic space Z and projection a with
  `HasSpaceBaseChange p T t Z a`. This is the actual 2-fibre product, together
  with an equivalence compatible with its projection to T, not an arbitrary map.
- Surjectivity of p is `SpaceMapIsSurjective Z T a` for each such base change.
  This existing predicate means every point of T is reached by a point of an
  etale scheme chart of Z. It is equivalent to the node's field-lifting condition:
  given a target object over Spec K, apply the predicate to its unique point;
  a chart point supplies its residue field extension and an object of the fibre
  product, hence the required isomorphism. Conversely, apply field lifting to
  the residue field at any point of T and then lift to an etale chart after a
  further field extension. Thus no smoothness or stronger lifting condition is
  imposed on p.
- Flatness and local finite presentation of p are the final part of `hp`:
  for every `U : Over S` and etale chart `b : yoneda.obj U ⟶ Z.obj.obj`,
  `Flat (yoneda.preimage (b ≫ a)).left` and
  `LocallyOfFinitePresentation (yoneda.preimage (b ≫ a)).left` hold.
  Yoneda recovers the actual composite U → T. These are exactly the chart tests
  specified in the node. No quasi-compactness, separatedness or finite-type
  condition is added. Local finite type appears only as explanatory vocabulary
  in the item, not as an additional hypothesis or conclusion.
- The two properties of V are `[IsReduced V.left]` and
  `[IsLocallyNoetherian V.left]`. Mathlib's reduced-sections definition equals
  reducedness of all stalks via `isReduced_of_isReduced_stalk` and its converse
  stalk instance. Its all-affine-opens Noetherian definition equals existence
  of a Noetherian affine cover by `isLocallyNoetherian_of_affine_cover` and
  `isLocallyNoetherian_iff_of_affine_openCover`.
- The conclusion supplies W and q with `IsSmoothModuliAtlas F W q`, together
  with `IsReduced W.left` and `IsLocallyNoetherian W.left`, all on the SAME atlas.
  There is no Noetherian condition on S and no smoothness condition on p.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom` (def-pc-scheme).
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `discreteModuli`,
  `IsFibredInGroupoids`, `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`,
  `SpaceMapIsSurjective`; its recorded 2-fibre-product and based-functor
  interfaces are used through these declarations.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` (def-trf-algebraic-space).
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology` (def-pc-fppf-site), used through fppf stack descent.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`, used through
  `SpaceMapIsSmooth` and `IsSmoothModuliAtlas`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`, and
  Morphisms.QuasiCompact: `QuasiCompact`, read for the explanatory finite-type
  vocabulary; no additional finite-type binder is needed.
- Mathlib.Algebra.Field.Defs: `Field`, read for the field-lifting convention.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian` (pqf-def-locnoeth).
- Mathlib.AlgebraicGeometry.Properties: `IsReduced` (def-pc-reduced-scheme).
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `IsSmoothModuliAtlas` and
  its `SpaceMapIsSmooth` (def-sfb-algebraic-moduli-stack).
- Sheaf.CategoryTheory.SiteStackification: `IsFppfModuliStack`
  (def-sfb-fppf-stackification).
- The size convention is realized by explicit Lean universes, not a new object.

The item's stmt_deps gains the three already landed nodes
`def-sfb-algebraic-moduli-stack`, `def-sfb-fppf-stackification`, and
`def-pc-reduced-scheme`, under brief-stage2 §5 (landed dependencies). Nothing
else about the accepted split or mathematical statement changes. There are no
new nodes or dependency repairs.

The proof-only import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra supplies
`Module.FaithfullyFlat.of_flat_of_isLocalHom` and
`Ideal.comap_map_eq_self_of_faithfullyFlat`, the two proof Mathlib matches.
The proof nodes `lem-sfb-stack-chartwise-smooth-etale-calculus`,
`lem-trf-smooth-reduced-dense-pullback`, and
`lem-sfb-scheme-locnoeth-fppf-descent` have no recorded Lean declarations yet;
there are no corresponding modules to import. Their accepted arguments and
uses are preserved verbatim in the node and rendered in the theorem docstring.
The proof needs no new objects to state this item.

Source checks: read stacks-properties.tex, lemma-type-property (04YF), and
lemma-unique-point-better (06MP), especially its (2)⇒(1) proof; read descent.tex,
lemma-Noetherian-local-fppf (034C) and lemma-reduced-local-smooth (034E).
The same common-chart argument works with V reduced locally Noetherian in
place of Spec k. First T → V is smooth, so T has both properties; reducedness
and local Noetherianity descend along the fppf scheme map T → W. This does not
ask for reducedness to ascend along an arbitrary flat map.

Edge cases checked before writing: empty V and the empty stack (surjectivity
then forces no target field points; an empty atlas is allowed); disconnected
or non-quasi-compact V; non-Noetherian base S; arbitrary characteristic and
imperfect fields; V → F flat but nonsmooth (for example a purely inseparable
field cover). None is excluded by the signature. Taking F representable by a
scheme recovers ordinary fppf descent. The test schemes are `Scheme.{u}` and
fields in their universe, with no smaller independently quantified test universe.
Every variable and universe is explicitly bound; autoImplicit is false.

Searches for an existing statement (2026-10-23):

- msearch.py leanfinder, query “An algebraic stack covered by a reduced locally
  Noetherian scheme by a representable surjective flat locally finitely presented
  morphism admits a reduced locally Noetherian smooth atlas”: eight hits,
  scheme smoothness, smooth ⇒ lfp, and `IsLocallyNoetherian`; no stack theorem.
- msearch.py leansearch, query “A representable surjective flat locally finitely
  presented cover of an algebraic stack by a reduced locally Noetherian scheme
  gives a reduced locally Noetherian smooth scheme atlas”: eight hits, including
  reduced scheme open-cover descent and the Noetherian affine-cover criterion;
  none states the item.
- msearch.py loogle, query `"IsReduced", "IsLocallyNoetherian"`: three hits,
  geometrically reduced flat scheme ascent/pullback; no stack atlas conclusion.
- msearch.py grep, query
  `AlgebraicStack|reduced.*fppf|locallyNoetherian.*descent`, subdirectory
  AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures for the item id: no hits. Search of reduced and
  Noetherian together found unrelated scheme/curve statements, no stack theorem.
- rg in lean/Sheaf and lean/WeilConjectures for algebraic-stack, fppf-stack and
  smooth-atlas names located the existing AlgebraicModuliStack and
  SiteStackification interfaces; their full definitions were read and reused.
  The ArtinCriterion namespace contains an older integer-base specialization,
  so the general recorded Q18 interface is used. Search of the stack modules
  found no reduced-locally-Noetherian descent theorem.

No statement fault or STATEMENT-DISPUTED finding. Validation: scompile.py compiled
both the sandbox and final module identities cleanly (3.5 s and 7.1 s), without
errors or warnings. The delivery dry run follows.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
