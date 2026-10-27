## Worker report

Item: lem-trf-space-qc-finite-affine-atlas-refinement. Module:
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineAtlasRefinement`.
It states two theorems, both with `sorry`, and introduces no definitions.
The main declaration is
`AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_atlas_refinement`;
`AlgebraicGeometry.AlgebraicSpace.exists_affine_atlas_of_quasiCompact` states
its final existence clause. No other field of the item's node is changed.

Sources read: `literature/stacks-project/spaces-properties.tex`,
`lemma-quasi-compact-space` (Tag 03E4), lines 632-648, and
`lemma-quasi-compact-affine-cover` (Tag 03H6), lines 747-768, together with
`definition-quasi-compact`, lines 624-630. The finite image subcover argument
of 03H6 applies to affine opens of any specified atlas, by the open-map
argument in 03E4. The already recorded source typo is retained as a source
observation: the final sentence of 03H6's proof says "finite surjective"
where its statement and argument give etale surjective. The Lean uses etale.
No statement correction or new node fault is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X : AlgebraicSpace S` is precisely
  the recorded fppf-sheaf algebraic space over that base. All schemes,
  coordinate rings, and scheme tests use the same universe `u` as its big site.
- Quasi-compactness is the explicit `hqc` existential: a scheme `Q : Over S`,
  a map `q : yoneda.obj Q ⟶ X.obj.obj`, and
  `CompactSpace Q.left ∧ IsEtale q ∧ IsSurjective q`. This is exactly the
  atlas definition in the statement, rather than a different notion of
  quasi-compact morphism. Both map predicates include scheme-test
  representability in their existing definitions.
- The specified atlas is `W : Over S`,
  `w : yoneda.obj W ⟶ X.obj.obj`, `hw : IsEtale w`, and
  `hs : IsSurjective w`. There is no compactness or separation binder on W,
  S, X, or their diagonals.
- `n : ℕ` renders the integer n >= 0, with index type `Fin n`.
  `V : Fin n → W.left.Opens` and `∀ i, IsAffineOpen (V i)` are the selected
  affine open subschemes of W, without requiring them to be disjoint in W.
- `U : Over S` and
  `j : ∀ i, Over.mk ((V i).ι ≫ W.hom) ⟶ U` supply the coproduct and its
  injections over S. `Nonempty (IsColimit (Cofan.mk U.left ...))` asserts
  exactly the scheme-coproduct universal property; `Nonempty` merely turns
  the categorical universal-property data into a proposition. It does not
  choose an object from a postponed existence theorem.
- `a : U ⟶ W` and
  `∀ i, j i ≫ a = Over.homMk (V := W) (V i).ι rfl` specify the induced
  map to W. Thus `yoneda.map a ≫ w` is the node's p. The coproduct property
  and these triangles determine it, and all maps are over the original S.
- `IsJointlySurjective (fun i ↦ yoneda.map (j i ≫ a) ≫ w)` is joint
  surjectivity of the composites V_i -> X: the triangles identify these
  composites with the original open inclusions followed by w. The recorded
  predicate uses lifts of field representatives after field extension.
- `IsEtale (yoneda.map a ≫ w) ∧ IsSurjective (yoneda.map a ≫ w)` gives
  representability, etaleness and surjectivity of p using scheme tests.
- `IsAffine U.left` asserts affineness of the scheme coproduct. The next
  universally quantified clause takes arbitrary
  `A : Fin n → CommRingCat.{u}` and affine presentations
  `∀ i, Nonempty ((V i).toScheme ≅ Spec (A i))`, and gives
  `Nonempty (U.left ≅ Spec (.of (∀ i : Fin n, A i)))`. The dependent
  function ring here is exactly the product of the coordinate rings.
- The empty-target clause is rendered without introducing a private notion
  of empty algebraic space: `IsEmpty W.left → n = 0`. For an etale scheme
  atlas of an algebraic space, W is empty if and only if X is empty. One
  direction follows from surjectivity of the atlas on point classes; the
  other follows by sending any point of W to its residue-field point of X.
  Thus when X is empty the witnesses choose the empty family. The further
  clause `n = 0 → Nonempty (U.left ≅ Spec (.of PUnit.{u + 1})))` records
  the specified `Spec 0` explicitly. `PUnit` is the zero commutative ring,
  as in Mathlib's `AlgebraicGeometry.specPUnitIsInitial`. The product formula
  also includes this empty product.
- The second theorem repeats exactly the same quasi-compactness hypothesis
  and concludes `∃ U p, IsAffine U.left ∧ IsEtale p ∧ IsSurjective p`, the
  final "in particular" assertion of the node. Its docstring explains
  applying the first assertion to the atlas in hqc. No new assumptions
  enter this clause.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `AlgebraicGeometry.Spec` and `Spec.map` (Scheme.lean,
  lines 36-63 and 470-481). The h_U maps use `CategoryTheory.yoneda` on
  `Over S`, exactly as the algebraic-space interface does.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`, and their common
  scheme-test definition `IsRepresentableWith`. The full definitions and
  docstrings were read, including the algebraic-space atlas predicate.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, lines 281-286; compactness
  has no Hausdorff assumption.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, lines 38-41;
  `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `ι`, and
  the open-immersion instance, lines 44-57. These give the actual open subschemes.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, lines 58-61, and
  `IsAffineOpen`, lines 250-252; the latter is the former on the open scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, lines 39-44,
  together with its composition, open immersion, and base-change instances.
- `Mathlib.AlgebraicGeometry.Limits`: scheme coproduct instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι`, lines 180-244, matching
  lem-weil-pbc-scheme-coproduct-family. The statement uses the equivalent
  general coproduct cofan universal property rather than a private construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicSpace.IsJointlySurjective`, whose full field-extension lifting
  definition and docstring were read.

The proof-only imports include the recorded
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` and
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus` modules,
`Mathlib.Topology.Compactness.Compact` (`isCompact_range`),
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (scheme-test
pullbacks), and `Mathlib.AlgebraicGeometry.Morphisms.Basic`
(`IsZariskiLocalAtSource.iff_of_iSup_eq_top`). The other proof dependencies
are already among the public imports: open-immersion base change,
etale composition/cancellation, and the finite coproduct spectrum formula
`sigmaSpec`/`ι_sigmaSpec`/its finite-index IsIso instance in Limits.lean,
lines 604-647. The theorem docstring carries all five accepted proof steps
and names the corresponding nodes. Nothing is proved in this delivery.

Edge cases checked before writing: empty X and empty W give `Fin 0`,
the initial scheme coproduct and `Spec 0`; no `Nonempty (Fin n)` or
nonzero-ring assumption excludes this. Empty base S is also allowed.
For nonempty X, joint surjectivity rules out an empty selected family.
For n = 1 the product formula is the singleton spectrum formula.
An infinite disjoint affine atlas of a point is permitted because W need
not be quasi-compact. Overlapping affine opens of a nonseparated atlas
are permitted: they are disjoint only in their scheme coproduct, never
assumed disjoint in W. No affine-intersection or quasi-separatedness
hypothesis is used. Characteristic and zero rings are unrestricted.

Searches actually run through msearch.py with group Q71 and this item:

- LeanFinder: `A quasi compact algebraic space admits a finite affine open
  refinement of any given etale surjective atlas`. Eight hits, headed by
  `AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact`;
  these concern scheme targets or pre-zero hypercovers, not arbitrary
  algebraic spaces with the given atlas. No exact match.
- Loogle: `AlgebraicGeometry.sigmaSpec, AlgebraicGeometry.IsAffine`.
  Successful search with zero hits.
- Mathlib grep, AlgebraicGeometry: `finite.*affine.*atlas|affine.*atlas|sigmaSpec`.
  Ten hits, including `sigmaSpec`, `ι_sigmaSpec`, the finite-index IsIso
  instance in Limits.lean and unrelated PointsPi lemmas. These provide
  the finite product formula but not the specified-atlas refinement.
- LeanSearch: `A quasi compact algebraic space has a finite affine open
  refinement of every etale atlas`. Eight hits, including the scheme
  finite-affine-open compactness criterion, the scheme hypercover
  refinement lemma, and `Scheme.OpenCover.affineRefinement`. None is
  the algebraic-space statement.

Local rg searches in lean/WeilConjectures and lean/Sheaf used the item id,
`finite_affine_subatlas|affine_etale_atlas`,
`finite.*[Aa]ffine|[Aa]ffine.*[Aa]tlas|IsQuasiCompact|[Qq]uasi[Cc]ompact`
on the algebraic-space modules, and
`finite.{0,35}affine|affine.{0,35}atlas|atlas.{0,35}affine` in the upstream
AlgebraicGeometry directory. Also searched both source trees, Mathlib and
`dag/lean_names_upstream.json` for the new declaration names; no clash.
No upstream declaration states this item. The existing
`exists_finite_affine_subatlas` was opened and read: it assumes an atlas
already given by disjoint affine components and compact target point space,
and does not give this node's arbitrary-atlas refinement and spectrum
formula. The nearby fppf refinement module has affine scheme tests of a
covering family and is also a different statement. The node
lem-sfb-qc-space-affine-etale-atlas was read: its hypothesis is point-space
compactness, its conclusion only the existence clause, and it currently
has no Lean record. No notion is redefined here.

Validation: scompile.py compiled this delivered module on the server both
as a sandbox file and under its actual library module name, cleanly.
Only the two expected postponed theorem proofs remain.

## Second reading by Q71

Author's separate rereading, not a claim of independent review: I reopened
the node statement and compared each binder and conjunct with the file.
The atlas-definition hypothesis hqc and the specified map's two predicates
are present. The finite opens really belong to the given W, the coproduct
is in schemes, and its injections and induced map commute over S. The
joint-surjectivity assertion is about precisely those open restrictions,
not a separately chosen family. The product formula is for arbitrary
chosen coordinate rings, and the zero-family case explicitly gives the
zero-ring spectrum. The last existence assertion has its own declaration
with the same hqc, rather than being lost in prose. I specifically checked
that no pairwise-disjointness condition was accidentally imposed on opens
inside W, and that no compactness, separation, nonempty-family or nonzero-ring
hypothesis entered. The empty-target condition is expressed using its
empty scheme atlas, an equivalent condition under hw and hs. No mismatch
was found and no statement correction was made. Independent review belongs
to the maintainer as specified in the assignment.
