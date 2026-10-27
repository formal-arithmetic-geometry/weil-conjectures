## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteDiagonalizableSubgroupParameter`
states `AlgebraicGeometry.exists_finiteDiagonalizableSubgroupParameter`, with
`sorry` as its only postponed proof. Its supporting definition
`AlgebraicGeometry.finiteDiagonalizableSubgroupParameters` is the set P_H(W)
explicitly introduced in the item's statement; it has real data and belongs to
this node, rather than introducing a separate independent notion or DAG node.
Both declarations have source and blueprint docstrings. The theorem docstring
carries all eight proof steps, including the node's proof dependencies.
No statement correction, dependency repair, or disputed statement is needed.

Hypothesis and clause correspondence:

- Any commutative ring A and its affine spectrum S: `(A : Type u) [CommRing A]`
  and `Spec (.of A)`. There is no field, nonzero, reduced, or Noetherian
  requirement. A common arbitrary universe holds the ring and finite group;
  test schemes are `Scheme.{u}`, so test universes are not below the base.
- The finite abelian group M: `(M : Type u) [AddCommGroup M] [Finite M]`.
  Neither positive cardinality assumptions nor invertibility of its order are
  added. The unit element already guarantees nonemptiness.
- G is a group scheme over S: `G : Grp (Over (Spec (.of A)))`. This is Mathlib's
  group object, including multiplication, unit and inverse and their diagrams.
  `G.X` is its underlying S-scheme and `G.X.hom` its structure map.
- Smooth, affine and finitely presented G: `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, and the full finite-presentation convention
  `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
  `[QuasiSeparated G.X.hom]`. Some follow from other hypotheses, but they
  spell out exactly the finite-presentation clause of the node.
- H = D_A(M) as a closed subgroup of G: the recorded `ringDiagonalizableGroup A M`
  and `(i : ringDiagonalizableGroup A M ⟶ G)` together with
  `[IsClosedImmersion i.hom.hom.left]`. The bundled hom is a group homomorphism;
  its underlying scheme map is a closed immersion. The supplied embedding is
  retained even though the represented set depends only on the abstract H.
- Every S-scheme W: `W : Over (Spec (.of A))`, with no finiteness or affineness
  restriction. The underlying G_W is `pullback G.X.hom W.hom`, and its group
  structure is `(Over.pullback W.hom).mapGrp.obj G`.
- A set of embedded closed subgroup schemes, not a set of arbitrary sources
  with embeddings: the parameter type is a subtype of
  `(pullback G.X.hom W.hom).IdealSheafData`. Membership means there exist
  `K : Grp (Over W.left)` and a group homomorphism
  `j : K ⟶ (Over.pullback W.hom).mapGrp.obj G` with
  `IsClosedImmersion j.hom.hom.left` and `j.hom.hom.left.ker = I`.
  A closed immersion is quasi-compact, so this kernel is its defining
  quasi-coherent ideal. Closed subschemes are uniquely encoded by these
  ideals, and the subgroup structure on a closed embedded subscheme is
  unique: its operations are determined by its monomorphism into G_W.
  Thus no extra parametrizations or chosen group structures enter the set.
- Existence of an fppf covering and abstract group isomorphisms: the membership
  predicate existentially quantifies `ι : Type (u + 1)`, schemes `U i`, and
  maps `f i : U i ⟶ W.left` with
  `Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage W.left`. This is exactly
  joint surjectivity, flatness and local finite presentation, by the recorded
  fppf-site dependency. The covering index universe includes families indexed
  by the chosen category's universe; larger coverings can always be reduced
  to this size by choosing a member above each point of W.
- The isomorphisms are
  `Nonempty ((Over.pullback (f i)).mapGrp.obj K ≅
  (Over.pullback (f i ≫ W.hom)).mapGrp.obj (ringDiagonalizableGroup A M))`.
  These are isomorphisms in the category of group objects over U_i. They do
  not compare j with the initial embedding i, and impose no conjugacy clause.
  The direct base change of H along `f i ≫ W.hom` is canonically the same
  group scheme as its successive base changes to W and U_i.
- The representing S-scheme Y_H: `∃ Y : Over (Spec (.of A))`.
  Its required properties are `IsQuasiAffineHom Y.hom`,
  `LocallyOfFinitePresentation Y.hom`, `QuasiCompact Y.hom`, and
  `QuasiSeparated Y.hom`, exactly quasi-affineness and finite presentation.
- The displayed bijections for all tests: `∃ e : ∀ W, (W ⟶ Y) ≃
  finiteDiagonalizableSubgroupParameters A M G W`.
- Pullback and naturality for every S-morphism `f : W' ⟶ W`: for every
  `x : W ⟶ Y`, `(e W' (f ≫ x)).val` equals `(e W x).val.comap` along
  `pullback.map` with components `(𝟙 G.X.left)`, `f.left`, and `(𝟙 S)`.
  Its commutativity proofs use the category identity laws and `Over.w f`.
  This is the canonical map G_W' → G_W, not an arbitrary comparison map.
  `IdealSheafData.comap` is the defining ideal of the scheme-theoretic inverse
  image. Equality of underlying ideals is equality in the subtype, whose
  extra membership information is a proposition. This pointwise naturality
  formulation is precisely naturality for the pullback functor; a second
  arbitrary functor or independent action is not assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, and `Spec.map` (the recorded scheme and spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions` is the existing convention record:
  finite presentation is local finite presentation plus quasi-compactness
  and quasi-separatedness; it supplies no additional private definition.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup` and its full Hopf-spectrum
  construction were read. This is the dependency's published D_A(M), not
  a copied group-algebra spectrum or a chosen isomorphic replacement.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (available through ideal functoriality).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.map`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `AlgebraicGeometry.Scheme.fppfPrecoverage` (the recorded covering notion).
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`, with its full affine-open signature.
- Existing supporting Mathlib constructions:
  `Scheme.IdealSheafData`, `Scheme.Hom.ker`, `IdealSheafData.comap`,
  `IdealSheafData.comapIso`, `Over.pullback` and `Functor.mapGrp`.
  These supply a literal embedded subgroup set and canonical base changes.

The module also imports the already stated proof dependencies privately:
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
`Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.RingTheory.Ideal.Operations`,
`Mathlib.AlgebraicGeometry.ResidueField`,
`Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient`,
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource`,
and `WeilConjectures.AlgebraicGeometry.Descent`.
The local-finite-presentation composition and fppf/fpqc representable-descent
matches are already supplied by the public imports. The proof-only nodes
`lem-sfb-finite-flat-group-hom-scheme`,
`lem-sfb-finite-locally-free-closed-embedding-locus`,
`lem-sfb-relative-diagonalizable-character-duality`, and
`lem-sfb-finite-locally-free-quasi-affine-reflection` currently have no usable
recorded module, so there is no corresponding proof import to add. They are
not required for elaborating this statement.

Edge cases checked before writing and again against the final signature:

- A zero ring is permitted. Its spectrum and every scheme over it are empty;
  there is one closed ideal/subgroup on the empty ambient scheme. An empty
  fppf family covers the empty test and its isomorphism condition is vacuous.
  No nonempty-index or nonempty-scheme instance excludes this case.
- The trivial additive group M is permitted. Its diagonalizable group is the
  identity group and the parameter set is the singleton identity subgroup.
- In characteristic p dividing |M|, such as M = Z/p over F_p, H may be
  nonreduced. Only the ambient G is smooth; no smoothness or reducedness
  requirement is placed on H or K, and no division by |M| occurs.
- Disconnected test schemes are permitted. Each test carries its own cover
  and arbitrary group-scheme isomorphisms; no globally constant label or
  fixed global trivialization is required.
- Different embeddings with the same closed image produce the same ideal;
  different closed images remain different parameters even if their source
  abstract groups are isomorphic. This is the distinction required by the
  node's explicit warning about abstract isomorphisms and embeddings.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder` with query "The functor of closed subgroup
  schemes fppf locally isomorphic to a finite diagonalizable group in a
  smooth affine group is represented by a quasi-affine finitely presented
  scheme": eight hits, concerning affine schemes/spaces, affine transition
  limits and finite morphisms; none states the parameter theorem.
- `msearch.py ... leansearch` with query "Representability of the functor of
  fppf forms of a finite diagonalizable closed subgroup scheme": eight hits
  including `Functor.IsRepresentable`, `Functor.IsRepresentedBy`, and
  `Scheme.LocalRepresentability.isRepresentable`; these are generic
  representability notions, not this subgroup functor or theorem.
- `msearch.py ... loogle` with query `"Grp", "Over"`: eight hits, including
  `Over.grpObjMkPullbackSnd`, `Scheme.GrpObjAsOverPullback`, and Hopf-spectrum
  group structures. These existing canonical base-change constructions are
  used through `Over.pullback` and `mapGrp`; no parameter theorem was found.
- `msearch.py ... grep` with query
  `diagonalizable|SubgroupScheme|closedSubgroup` in `AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the exact item id:
  no existing statement. Searches for group-scheme, closed-subgroup,
  `Grp (Over ...)`, fppf forms and subgroup parameters found group-scheme
  definitions over fields and related subgroup/quotient theorems, but no
  definition of this relative parameter set or statement. In particular
  upstream `IsClosedSubgroupScheme` is specialized to a field and is not a
  replacement for closed embeddings over arbitrary rings and test schemes.
- Exact-name searches for the two introduced names in Mathlib, the project,
  upstream sources and `dag/lean_names_upstream.json` found no collisions.
- Read the dependency DAG records and all recorded signatures/docstrings.
  The named compact-object example is withdrawn in the current checkout;
  its node now records the upstream `CategoryTheory.IsCompactObject`.
- Read Conrad's original online PDF, printed pp.69-70, including the
  embedding-locus quotient and identification with the abstract-form
  subgroup functor. No source change to the statement was necessary.

Validation: `scompile.py Q35 lem-sfb-finite-diagonalizable-subgroup-parameter`
compiled the delivered module separately, both sandbox and library module
checks, with no errors or non-sorry warnings. The initial elaboration pass
identified the actual smaller universe of ideal sheaves and the two bundled
hom projections; both were repaired without restricting any scheme test or
adding a mathematical assumption. The definition is `Type u`, as is the
existing ideal-sheaf set; existential group schemes and covers are only
propositional membership witnesses and do not enlarge its data universe.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
