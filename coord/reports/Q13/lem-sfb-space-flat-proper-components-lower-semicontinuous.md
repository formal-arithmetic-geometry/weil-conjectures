## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatProperComponentsLowerSemicontinuous`
states `AlgebraicGeometry.AlgebraicSpace.geometricComponentCount_lowerSemicontinuous`.
Its sole theorem has proof `sorry`; no definitions or additional theorems are introduced.
The source is Stacks Project, More on Morphisms of Spaces, Tag 0E1D,
`literature/stacks-project/spaces-more-morphisms.tex`, lines 8349–8386. The source and
node agree; no statement correction or disputed statement is needed.

Clause-by-clause correspondence:

- A scheme target and an algebraic-space source are `T : Over S` and
  `X : AlgebraicSpace S`, for an arbitrary scheme `S : Scheme.{u}`.
  The named morphism is `f : X ⟶ schemeSpace T`. The scheme in the node is `T.left`.
  Using an arbitrary ambient base does not impose an additional mathematical
  hypothesis: one may take the ambient base to be the target and its structure
  morphism to be the identity, or take the absolute base. The statement also covers
  any already specified ambient scheme.
- Properness is `hf : MapIsProper f`; flatness is `hflat : MapIsFlat f`.
  These are the recorded chartwise/global space predicates, not their scheme analogues.
- Finite presentation is exactly the three specified constituents:
  `hlfp : MapIsLocallyOfFinitePresentation f`, `hqc : MapIsQuasiCompact f.hom.hom`,
  and `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  Quasi-separatedness is quasi-compactness of the relative diagonal. No finite-type,
  smoothness, reducedness, or Noetherian assumption is added.
- The chosen residue-field closures are the dependent family `Ω : T.left → Type u`,
  with the three explicitly bound families of instances `Field (Ω t)`,
  `Algebra (T.left.residueField t) (Ω t)`, and
  `IsAlgClosure (T.left.residueField t) (Ω t)`. Thus the statement holds for every
  choice, rather than asserting only the existence of a favourable choice.
- The geometric point map is literally
  `Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) (Ω t))) ≫
  T.left.fromSpecResidueField t`. `Over.homMk` equips it with its composite structure
  map to `S`; its compatibility proof is reflexivity. The fppf Yoneda functor maps
  this actual scheme map to a sheaf map to `schemeSpace T`.
- `Limits.pullback f.hom (...)` is the sheaf fibre product. Its underlying presheaf
  `.obj` is used in `Point`, whose topology is the recorded atlas topology. This
  is the full topological geometric fibre, not the set of Ω-valued sections.
- `ConnectedComponents` is Mathlib's quotient by equality of `connectedComponent`.
  Its elements correspond exactly to maximal nonempty connected subsets; an empty
  subset is never introduced as a component. `Finite (ConnectedComponents (...))`
  is the finiteness assertion, independently of the cardinality convention.
- `∃ n : T.left → ℕ` and `n t = Nat.card (ConnectedComponents (...))` specify the
  node's function, point by point. `Nat.card` is used only together with the explicit
  finiteness clause, so its infinite-type convention does not weaken the claim.
- The separate clause `IsEmpty (Point (...)) → n t = 0` records empty fibres.
- `∀ t, ∃ V : T.left.Opens, t ∈ V ∧ ∀ v, v ∈ V → n t ≤ n v` is exactly the stated
  lower-semicontinuity neighbourhood inequality, with its direction preserved.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, and the full-subcategory/sheaf representation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsProper`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, and `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (closure and the sheaf universal property).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  its imported `AlgebraicSpacePointClasses` supplies `Point` and its field-point relation.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField` (the former is the recorded residue-field declaration).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`, the exact notion of an
  algebraic closure in the dependency's `mathlib_match`. No private copy is defined.
- The two added, already-landed statement dependencies give constructions directly
  used in the signature: `def-trf-scheme-algebraic-space` owns `schemeSpace` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`; `def-sfb-proper-curve-moduli`
  owns `MapIsQuasiCompact` in `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
  Their node statements and actual source declarations were read. Only these two
  identifiers are appended to `stmt_deps`; no existing dependency or other field changes.
- Mathlib `ConnectedComponents` (`Topology.Connected.Clopen`) and `Nat.card`
  (`SetTheory.Cardinal.Finite`) provide the existing topological count.

The module imports all recorded proof dependencies with available modules, as ordinary
proof imports unless the same module is already a public statement import. The five
proof dependencies without Lean records or Mathlib matches are not imported:
`lem-sfb-space-proper-base-change`, `lem-sfb-space-proper-global-algebra-components`,
`lem-sfb-space-sepclosed-components-base-change`,
`lem-sfb-space-stein-finite-fibres-residue-fields`, and
`lem-sfb-space-scheme-fibre-topology`. None is needed to type the statement. Their
roles remain explicit in the eight-step proof docstring. The existing modules for
common extensions, flat/proper/fp locality, affine Stein factorization, integral-fibre
etale splitting, open subspaces, point/open calculus, chart tests and universal openness
are imported, together with the scheme-property Mathlib proof inputs.

Edge cases checked before writing:

- An empty target gives vacuous pointwise clauses and an empty-domain count function.
- An empty source or geometric fibre has an empty component quotient and count zero;
  the lower bound zero holds on the whole target.
- Nonempty connected fibres have one component, even when their structure is nonreduced.
  Nilpotents are not excluded by any binder or by the atlas topology.
- A split finite disjoint union counts its nonempty connected pieces, not its geometric
  rational points. Disconnected fibres persist nearby; the inequality is in the correct
  direction (special count is at most nearby count).
- Arbitrary characteristic is allowed, including purely inseparable extensions in
  positive characteristic. The field-algebra map is automatically injective.
- No local Noetherianity is imposed. All test fields and schemes use `u`, as required by
  the big-site convention; point classes live in `Type (u + 1)`. There is no independent
  smaller test-field universe and no equality of distinct universes imposed.

Searches for an existing statement (all performed with the prescribed tools):

- `msearch.py ... leanfinder "The number of geometric connected components of the fibres
  of a proper flat finitely presented algebraic space over a scheme is finite and lower
  semicontinuous"`: eight hits, including `IsFinite`, scheme finite-fibre finiteness,
  and `UniversallyOpen.of_flat`; no algebraic-space component-count theorem.
- `msearch.py ... loogle '"LowerSemicontinuous", "Scheme"'`: zero hits.
- `msearch.py ... grep 'component.*lowerSemi|lowerSemi.*component|geometricComponentCount'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Proper flat finitely presented algebraic spaces have lower
  semicontinuous numbers of geometric connected components"`: eight scheme/commutative
  algebra hits, none stating the item.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, for
  `geometricComponentCount|component.*lowerSemi|lowerSemi.*component` and the item id:
  the existing `Scheme.Hom.geometricComponentCount_lowerSemicontinuous` is only for
  schemes (`Sheaf.AlgebraicGeometry.FlatProperComponentCountLowerSemicontinuous`);
  read its full statement. It cannot express an arbitrary algebraic-space source.
  Other matches are scheme base-change/generic-constancy/locally-constant results.
  No match for the item id or the chosen fully qualified space declaration exists.
- Targeted `rg` of `AlgebraicSpace*`, `Space*`, and `Enlarged*` modules for geometric
  fibres, algebraic closures and connected components found no existing version of
  this statement. Read and reused the existing sheaf pullbacks and `schemeSpace`.

Validation: the initial single-file `scompile.py` run succeeded in sandbox and library
module modes (2.0 seconds each), without errors or warnings. Every variable and universe
is bound explicitly, and the file sets `autoImplicit false`. The final delivery dry run
and push perform the required final per-file compile and server preflight.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
