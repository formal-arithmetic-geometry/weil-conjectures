## Worker report

The module `Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation` states
`AlgebraicGeometry.exists_flat_stage_of_limit`, with proof `sorry`. It states exactly
lem-weil-pbc-descend-flat-finite-presentation; no definitions, extra nodes, dependency
modules, or statement corrections are needed. The declaration docstring carries the
six-step DAG proof with its dependencies. Nothing is proved.

Hypothesis and clause correspondence:

- The directed set is `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The chosen element called 0 in the node is `(i₀ : I)`; it is an arbitrary chosen
  index, not a least element. This binder already excludes an empty indexing set,
  as the node does, without needing an additional `Nonempty` instance.
- The inverse system of schemes is `(D : Iᵒᵖ ⥤ Scheme.{u})`. Its functor laws
  supply the identity and composition laws for the transition morphisms.
  `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]` states exactly that
  all transition morphisms are affine.
- The limit S with its projections is `(c : Cone D) (hc : IsLimit c)`:
  S is `c.pt`, and the projection to S₀ is `c.π.app (op i₀)`. This keeps an
  arbitrary specified limit, as in the node, rather than imposing a different
  choice of limit. Existence is supplied by the recorded dependency theorem
  `exists_limit_affine_transition`; an existing limiting cone is simply used
  as data in this statement.
- S₀ is `D.obj (op i₀)`, with `[CompactSpace (D.obj (op i₀))]` and
  `[QuasiSeparatedSpace (D.obj (op i₀))]`. CompactSpace does not assume
  Hausdorffness: it is precisely quasi-compactness of the underlying space.
- The S₀-schemes X₀,Y₀ are `(X₀ Y₀ : Over (D.obj (op i₀)))`, with their
  structure maps in `.hom`. The morphism over S₀ is `(f₀ : X₀ ⟶ Y₀)`;
  `Over.w f₀` is its compatibility with these structure maps.
- X₀ is quasi-compact and quasi-separated by `[CompactSpace X₀.left]` and
  `[QuasiSeparatedSpace X₀.left]`; Y₀ has the two corresponding binders.
  None of these six topological hypotheses is replaced by a condition on an
  identity morphism, and no hypothesis is imposed on every Sᵢ.
- Local finite presentation of f₀ is `[LocallyOfFinitePresentation f₀.left]`.
- The base-changed source and target over S are the underlying schemes of
  `(Over.pullback (c.π.app (op i₀))).obj X₀` and the corresponding object for Y₀.
  By Mathlib's definition these are `pullback X₀.hom (c.π.app (op i₀))` and
  `pullback Y₀.hom (c.π.app (op i₀))`. Their induced morphism f is
  `((Over.pullback (c.π.app (op i₀))).map f₀).left`, whose flatness is the
  explicit hypothesis `hflat`. This is f₀ times the identity, not the projection
  of X to S.
- The conclusion `∃ (i : I) (hi : i₀ ≤ i), Flat (...)` asserts precisely a
  stage i≥0 at which fᵢ is flat. Its base map is
  `D.map (homOfLE hi).op : D.obj (op i) ⟶ D.obj (op i₀)` and its morphism is
  `((Over.pullback (D.map (homOfLE hi).op)).map f₀).left`. Mathlib uses the
  fibre products X₀ ×_{S₀} Sᵢ and Y₀ ×_{S₀} Sᵢ here, with the same orientation
  as the node. There is no stronger eventual-flatness conclusion.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`, are schemes and their locally ringed-space
  morphisms. Their full definitions and docstrings were read.
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, says that the preimage of every
  affine open is affine.
- lem-weil-pbc-limit-affine-transition:
  `AlgebraicGeometry.exists_limit_affine_transition`, in the imported
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`; the complete signature and
  docstring were read. A cone with `IsLimit` is the limit notion in that record.
- def-weil-pbc-scheme-conventions is a convention record, not a declaration to
  duplicate. Its QC and QS notions are rendered using Mathlib `CompactSpace`
  (`Mathlib.Topology.Defs.Filter`) and `QuasiSeparatedSpace`
  (`Mathlib.Topology.QuasiSeparated`), whose definitions were read.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `.lift`, `.map` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Their full signatures and docstrings were read. The imported
  `Mathlib.CategoryTheory.Comma.Over.Pullback` packages exactly these objects
  and induced maps as `CategoryTheory.Over.pullback`; its body and docstring
  were read. No new base-change notion is introduced.
- def-weil-flat-morphism: `AlgebraicGeometry.Flat`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, with its equivalence
  `Flat.iff_flat_stalkMap`; the class and stalk equivalence were read.
- def-sbc-locally-finite-presentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, with its complete
  affine-local class definition and docstring read.

Source check: the local `literature/stacks-project/limits.tex` is not present on
this machine. Read the primary source directly at
https://stacks.math.columbia.edu/tag/04AI and
https://stacks.math.columbia.edu/tag/081D. They agree with the node: no missing
hypothesis or incorrect clause was found. The item's statement and proof records
remain unchanged.

Edge cases checked before writing: the chosen i₀ excludes the empty index set
exactly as the source does; the index need not have a bottom, be finite, or be
antisymmetric. Singleton systems are allowed and the witness may be i₀ itself.
Empty schemes X₀, Y₀ or S₀ remain permitted (when structure maps exist);
flatness on an empty source is allowed and no nonemptiness hypothesis is added.
No field, characteristic, dimension or nonzero-ring restriction is present.
The index universe v and scheme universe u are explicit and independent, so
there is no restriction to countable or same-universe systems. There is no
quantification over test schemes in a potentially vacuous smaller universe.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder`: query “flatness of a locally finitely presented
  morphism descends to a finite stage of an inverse limit of schemes with affine
  transition maps”; 8 hits including `flat_iff`, `UniversallyOpen.of_flat`,
  `Flat.instDescScheme` and affine-local flatness. None is inverse-limit descent.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`;
  12 hits concerning openness, étaleness, flat/fpqc descent and ranks, not this
  limit statement.
- `msearch.py ... grep`: query `04AI|descend.*[Ff]lat|[Ff]lat.*[Ll]imit`
  in `AlgebraicGeometry`; 12 hits on categorical flatness and fpqc/fppf descent,
  none on inverse-limit flatness descent.
- `msearch.py ... leansearch`: query “flat morphism locally of finite
  presentation descends to some stage of a directed inverse limit of schemes”;
  UNAVAILABLE, service Internal Server Error. No mathematical verdict is drawn
  from this unavailable search; the other kinds and direct searches were used.
- Direct `rg` with `04AI|descend.*[Ff]lat|[Ff]lat.*[Ll]imit` and the exact item
  id over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, plus corresponding
  `rg` over `lean/Sheaf`: only unrelated categorical flatness, fpqc descent,
  module-flatness descent and ring-flatness results. No matching statement.
- `rg` of the item id in `dag/lean_names_upstream.json`: no match.
- Direct name search `exists_flat_stage_of_limit` in Mathlib, WeilConjectures,
  lean/Sheaf and the upstream name table: no matches, so the full name is fresh.

Verification: `scompile.py J1 lem-weil-pbc-descend-flat-finite-presentation`
compiled the module on the server in 1.7 s, exit code 0, without warnings.
Every universe and variable is explicitly bound. The only proof is the named
node theorem's `sorry`. No STATEMENT-DISPUTED or node faults were found.

## Second reading by J1

Independent reading of the node, its six proof steps, all seven statement-dependency
records and their declarations, and the delivered Lean module. No mathematical or
signature mismatch was found. The Lean and node copy are retained unchanged; this
second-reading section is the only change.

Source: checked [Stacks 04AI](https://stacks.math.columbia.edu/tag/04AI) together with
[Situation 081D](https://stacks.math.columbia.edu/tag/081D), and independently read
`limits.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex
at `situation-descent-property` and `lemma-descend-flat-finite-presentation`.
The local literature checkout lacks the tex file. Situation 081D explicitly supplies
all three schemes' quasi-compactness and quasi-separatedness; 04AI adds flatness of
the limit morphism and local finite presentation of the original morphism.

Objects, hypotheses and conclusion, listed before comparing their Lean rendering:

1. Directed indexing set I, with chosen element 0: `{I : Type v} [Preorder I]
   [IsDirected I (· ≤ ·)]` and `(i₀ : I)`. PASS: chosen index, not a bottom element;
   preorder is the project's directed-set convention, without extra antisymmetry.
2. Inverse system of schemes and compatible transitions: `(D : Iᵒᵖ ⥤ Scheme.{u})`.
   PASS: functor identities/compositions provide exactly compatibility; objects are
   Mathlib schemes and morphisms are their locally ringed-space morphisms.
3. Every transition affine: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j),
   IsAffineHom (D.map a)]`. PASS: the dependency's IsAffineHom requires affine
   preimages of affine opens, and opposite order gives Si → Sj for i ≥ j.
4. Limit S with projections: `(c : Cone D) (hc : IsLimit c)`, S = `c.pt`,
   p₀ = `c.π.app (op i₀)`. PASS: arbitrary specified categorical limit and its
   projections, with no imposed choice or additional property of S.
5. S₀ = `D.obj (op i₀)` quasi-compact and quasi-separated:
   `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`.
   PASS: CompactSpace only asserts compactness of the whole underlying space,
   without Hausdorffness; QuasiSeparatedSpace asserts compact intersections of
   compact opens, equivalent to scheme quasi-separatedness.
6. Schemes X₀,Y₀ over S₀ and f₀ over S₀: `(X₀ Y₀ : Over (D.obj (op i₀)))`
   and `(f₀ : X₀ ⟶ Y₀)`. PASS: `.left` gives schemes/maps, `.hom` their structure
   maps, and `Over.w f₀` enforces the requisite triangle.
7. X₀ and Y₀ quasi-compact and quasi-separated: the four instances
   `CompactSpace X₀.left`, `QuasiSeparatedSpace X₀.left`,
   `CompactSpace Y₀.left`, `QuasiSeparatedSpace Y₀.left`. PASS: precisely these
   schemes, with no condition on every stage or on an identity morphism.
8. Xi,Yi,fi for i ≥ 0: `Over.pullback (D.map (homOfLE hi).op)` applied to X₀,
   Y₀ and f₀. PASS: read Over.pullback's definition: objects are
   `pullback X₀.hom q` and `pullback Y₀.hom q`; its morphism is the unique lift
   with components `pullback.fst _ _ ≫ f₀.left` and `pullback.snd _ _`.
   Thus its `.left` is exactly f₀ × id, with the correct base and orientation.
9. X,Y,f over S: the same functor at `c.π.app (op i₀)`. PASS: the pullbacks are
   over S₀ and the map uses the same f₀, not a structure-map projection.
10. f flat: `(hflat : Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left))`.
    PASS: read Flat and `Flat.iff_flat_stalkMap`: precisely flatness of each
    induced local-ring map at source points, as def-weil-flat-morphism says.
11. f₀ locally of finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
    PASS: read its affine-local class and `HasRingHomProperty.iff_exists_appLE`;
    the pointwise affine-neighbourhood condition in the dependency is equivalent.
    No quasi-compactness of the morphism or global finite presentation is added.
12. Some i ≥ 0 with fi flat: `∃ (i : I) (hi : i₀ ≤ i),
    Flat (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left)`.
    PASS: index followed by order witness followed by flatness of its induced map;
    neither an eventual-flatness conclusion nor an extra clause is imposed.

Dependency check: read Scheme and Scheme.Hom, IsAffineHom, Flat including its stalk
criterion, LocallyOfFinitePresentation including its pointwise criterion, pullback
and its projections/lift, and Over.pullback. Read the complete module and signature
of `exists_limit_affine_transition`: it supplies a limiting cone, affine projections,
limits on opens, and the affine-spectrum identification. This item only needs the
categorical meaning of a given limit, represented directly by Cone/IsLimit; it does
not call the existence theorem or import its same-universe restriction into the
statement. The convention node defines no new notion; CompactSpace and
QuasiSeparatedSpace are the established underlying-space properties. No private
copy, missing definition, new node or dependency module is present or needed.

Edge cases: i₀ already excludes the empty index set exactly as the node/source do;
no bottom, finite cardinality or strict later index is required. A singleton system
is allowed and i = i₀ is allowed. Empty schemes and zero-ring affine schemes are
allowed whenever the displayed structure maps exist. Flatness of an empty source
is covered; no nonemptiness or nonzero-ring hypothesis is introduced. There is no
n, field, characteristic or dimension restriction. Universes u and v are explicitly
bound and independent. The limit is supplied as data, so a large indexing universe
does not assert that all such diagrams have small limits. No test-object quantifier
can become vacuous by a smaller universe.

Independent searches with different wording from the worker:

- `msearch.py ... leanfinder "flat morphism at a stage of a cofiltered limit
  eventually flat"`: 8 hits, all categorical representable flatness, not scheme
  flatness descending to a stage.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, CategoryTheory.Limits.IsLimit"`:
  successful search, 0 hits.
- `msearch.py ... grep "flat.*stage|[Ff]lat.*[Ii]nverse|[Ll]imit.*[Ff]lat"`:
  17 hits about preservation of finite limits by flat tensor products and flat
  functors; no matching statement.
- Direct rg of that pattern and `exists_flat_stage_of_limit` in Mathlib's
  AlgebraicGeometry, WeilConjectures, repository lean/Sheaf and the upstream name
  table: unrelated K-flat complexes, module colimits and categorical flatness;
  no duplicate declaration or scheme inverse-limit descent statement.

H5–H9: no definitions or hollow data; the sole theorem has proof `by sorry`.
Module and theorem docstrings name 04AI in 081D and the exact blueprint id.
The proof docstring covers all six node steps and their dependency names:
finite affine triples, colimit rings on the tail, tensor-product base changes,
flatness on each limit piece, algebraic finite-stage descent, common upper bound
and local-to-global flatness. Header, namespace and topic path match conventions;
all Lean lines are at most 100 characters and binders/universes are explicit.
Imports supply the affine-limit vocabulary, flatness, local finite presentation
and Over base change. The node's `lean.statement` is verbatim the file signature.

Verification: recompiled the unchanged delivery module with scompile.py using its
absolute sandbox path; clean server compilation and delivery preflight are checked
again by deliver2.py below. The first scompile invocation used a relative path from
the read-only repository and failed before compilation; corrected the invocation
without changing any tool or source.

## Reviewer fix (R-dff1141)

The index type was `{I : Type v}` with a universe independent of `Scheme.{u}`. The recorded
form of limits of schemes with affine transitions (M1 d2371fc68, F1 a215660fd, J1 13cd55798,
M1 1f76496d8, K1 6fc533ce2; `exists_limit_affine_transition`) takes `D : Iᵒᵖ ⥤ Scheme.{u}` with
`I : Type u`. Fixed to `{I : Type u}` and `universe u`; nothing else changed. The statements
above that call u and v "explicit and independent" no longer apply.
