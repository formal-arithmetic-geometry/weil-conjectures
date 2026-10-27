## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeUnion` states Stacks
Tag 0829 (`spaces-limits.tex`, `lemma-directed-colimit-finite-type`, statement and
proof, read at lines 2301–2329). Its only theorem is
`AlgebraicGeometry.AlgebraicSpace.finiteTypeQuasiCoherentSubmodules_colimit`, with
proof `sorry`. The two construction helpers have real data: the subtype of
subobjects satisfying Mathlib's quasi-coherence and finite-type predicates, and
the inclusion diagram obtained from the monotone subtype inclusion followed by
`Subobject.underlying`. These helpers express the indexing system already
introduced in the item's statement, rather than an independent new notion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Scheme` (the declaration and Hom signature read).
- An algebraic space over S: `(X : AlgebraicSpace S)`, from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`. This is the existing full subcategory
  of big-fppf sheaves with representable diagonal and a representable surjective
  etale atlas, not a scheme specialization. Its definitions `IsEtale`,
  `IsSurjective`, `EtaleSite`, `structureSheaf` and `Modules` were read.
- Quasi-compactness: `hqc` is existence of `T : Over S` and
  `a : yoneda.obj T ⟶ X.obj.obj` with `CompactSpace T.left ∧ IsEtale a ∧
  IsSurjective a`. This is exactly the representable surjective etale map from
  a quasi-compact scheme required by the node, with no extra atlas choice as
  data of X and no affine restriction on T.
- Absolute quasi-separatedness: `hqs : IsAbsolutelyQuasiSeparated X`, from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`. Its full
  definition quantifies over every pair of affine scheme maps to X and requires
  their fibre product point space to be compact; Stacks 0AHR(3) identifies this
  with the absolute diagonal criterion. Added the already landed definition node
  `def-sfb-space-absolute-quasi-separated` to `stmt_deps`, as permitted by brief
  section 5. This is the same hypothesis the item already states. In particular
  nothing is assumed about quasi-separatedness of S.
- An arbitrary quasi-coherent O_X-module: `(M : X.Modules)
  [M.IsQuasicoherent]`. `Modules` is the existing module sheaf category on the
  small etale site. The recorded module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` supplies the slice
  instances for the same Mathlib predicate used by its `QCoh` full subcategory.
  No finite-type or finite-presentation condition is put on M.
- Sigma(M): `finiteTypeQuasiCoherentSubmodules M` is the subtype of
  `Subobject M` with `(N : X.Modules).IsQuasicoherent ∧
  (N : X.Modules).IsFiniteType`. `Subobject` identifies isomorphic embedded
  representatives and has its actual inclusion partial order. Finite type is
  exactly Mathlib's site-local finite-generators predicate, whose full signature
  and docstring were read in `Sheaf/Generators.lean:142`.
- Universe containing the subobjects: the subtype lives in the inferred universe
  of `Subobject M`; it is not forced into the smaller scheme carrier universe.
  `universe u` is explicitly bound, and all schemes, rings and module sections
  use the existing framework at u. There is no independent small-index assumption
  excluding subobjects, nor a `HasColimit` hypothesis.
- Nonempty: `Nonempty (finiteTypeQuasiCoherentSubmodules M)`.
- Directed: `Directed (· ≤ ·) (fun N : finiteTypeQuasiCoherentSubmodules M ↦ N)`.
  This says every pair has a common upper bound in exactly the inclusion order.
- The diagram: `finiteTypeQuasiCoherentSubmoduleDiagram M` maps N to its module
  sheaf using `Subobject.underlying`; its maps are the actual inclusions supplied
  by the subobject order. This uses Mathlib's `Monotone.functor` and
  `Subobject.underlying`, not arbitrary chosen transition arrows.
- Canonical colimit map is an isomorphism: the last conjunct gives a cocone c,
  `h : c.pt = M`, `Nonempty (IsColimit c)`, and
  `c.ι.app N ≫ eqToHom h = N.val.arrow` for every N. After transporting along h,
  the vertex is M and every leg is precisely the submodule inclusion. This is
  exactly the universal-property form of the canonical comparison being an
  isomorphism. It proves colimit existence too and does not assert merely an
  abstract isomorphism with an unrelated cocone. `Cocone`, `IsColimit`, `colimit`
  and `colimit.desc` were read in Mathlib's `Limits/Cones.lean`,
  `Limits/IsLimit.lean` and `Limits/HasLimits.lean`, matching
  `def-weil-pbc-category-colimit`.

The proof docstring follows all four DAG proof steps, including the zero
submodule, finite sums/images, finite-presentation approximation, exact filtered
colimits, and the explicit inverse to the canonical comparison. Imports for
stated proof dependencies are
`Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFpDirectedApproximation` and
`WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`; their recorded
full signatures/docstrings were read. The point topology proof dependency is
already imported publicly through the absolute-quasi-separatedness module.
The kernels/colimits proof node currently has no usable recorded Lean module,
so there is no module for it to import. It is not needed for typing this statement.

Edge cases checked before writing: M = 0 (zero subobject is an index and its
inclusion colimit is zero), empty X (the same zero case, with empty atlas allowed),
zero generators (no positivity requirement), arbitrary non-Noetherian X and
arbitrary infinitely generated M (neither restricted). No nonempty-space,
Noetherian-base, separated-base, or finite-type-M hypothesis was introduced.
The indexing set is asserted nonempty, not assumed nonempty, and no finite
indexing set or missing empty-index special case is hidden.

Searches actually run for this item:

- `msearch.py ... leanfinder "Every quasi coherent module on a quasi compact quasi
  separated algebraic space is the directed union of its finite type quasi
  coherent submodules"`: 8 hits, including `SheafOfModules.IsFiniteType`,
  `LocalGeneratorsData.IsFiniteType`, `QuasicoherentData.IsFinitePresentation`
  and local-generator APIs. No theorem about exhaustion on an algebraic space.
- `msearch.py ... loogle '"Quasicoherent", "colimit"'`: 0 hits.
- `msearch.py ... grep 'AlgebraicSpace|[Ff]inite[Tt]ype.*[Ss]ubmodule|[Qq]uasicoherent.*[Cc]olimit'
  AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "A quasi coherent module on a qcqs algebraic space is
  the directed colimit of all finite type quasi coherent subobjects"`: 8 hits,
  mainly quasi-coherence constructors/presentations and
  `ModuleCat.directLimitIsColimit`. The latter is a colimit of ring modules, not
  this assertion about all finite-type quasi-coherent subobjects on X_et.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite-type submodules,
  quasi-coherent colimits and the item id: existing scheme-only extension and
  finite-type approximation lemmas, algebraic-space finite-presentation
  approximation and finite-type submodule extension, but no identical theorem.
  Read the source of both algebraic-space approximation and extension results.
- `rg` for all three proposed full-name suffixes in Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json`: no existing declarations found.

The example `CompactObject.lean` is currently withdrawn and contains no
declarations; its node record and the standing module/docstring conventions
were read instead. No statement correction, disputed statement, new DAG node,
or dependency-record repair is needed.

Validation: `scompile.py NA lem-sfb-space-qcoh-finite-type-union` compiled both
its sandbox probe and its final library module cleanly (1.7 seconds each), with
no errors or warnings. Early elaboration errors from namespace-based dot notation
and the monotone-functor constructor were repaired by explicit function calls;
the resulting signatures bind all variables and universes with autoImplicit off.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
