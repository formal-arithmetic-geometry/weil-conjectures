## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas` states exactly
lem-a1-space-finite-affine-subatlas in three named theorems, all with `sorry` proofs:
`AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_subatlas`,
`AlgebraicGeometry.AlgebraicSpace.compactSpace_points_of_surjective`, and
`AlgebraicGeometry.AlgebraicSpace.compactSpace_points_of_scheme_atlas`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/spaces-properties.tex`, lines 633–648,
Tag 03E4, lemma-quasi-compact-space, and lines 701–723, Tag 03FX,
lemma-cover-by-union-affines. The first argument is the finite-subcover construction
in 03E4 for the specified disjoint affine presentation of 03FX. The second argument
is precisely the continuous-surjection implication in the proof of 03E4.

Hypotheses and conclusions of the first theorem:

- The base scheme is `{S : Scheme.{u}}`, and the algebraic space over it is
  `(Z : AlgebraicSpace S)`. Its underlying point classes and their atlas topology
  are the existing `Point Z.obj.obj` and `pointTopologicalSpace`.
- Quasi-compactness of that point space is the explicit hypothesis
  `hZ : CompactSpace (Point Z.obj.obj)`. Mathlib's compactness has no Hausdorff
  requirement, so this is precisely open-cover quasi-compactness.
- The specified atlas scheme over S is `(U : Over S)`, and its natural
  transformation is `(p : yoneda.obj U ⟶ Z.obj.obj)`.
  `hp : IsEtale p` means representability with etale scheme base changes;
  `hs : IsSurjective p` means representability with surjective scheme base changes.
  Thus neither representability nor surjectivity is replaced by an arbitrary map
  or by a conclusion about an unspecified atlas.
- The given summands `U_d` are encoded by their open images
  `(V : D → U.left.Opens)`, with `{D : Type v}` arbitrary. Each open has the
  canonical restricted scheme structure `(V d).toScheme` and S-map
  `(V d).ι ≫ U.hom`. The condition `hV : ∀ d, IsAffineOpen (V d)` makes
  each such scheme affine. `hd : Pairwise (fun d e ↦ Disjoint (V d) (V e))`
  and `hc : (⨆ d, V d) = ⊤` state exactly that the summands are disjoint
  open subschemes covering U. This is the usual scheme disjoint-union topology
  expressly specified in the node. Conversely the summands of any given
  coproduct presentation identify canonically with these open subschemes;
  no component is required to be nonempty or connected. This representation
  does not replace the given atlas by a new or isomorphic target atlas.
- The conclusion quantifies `D₀ : Set D` and states `D₀.Finite`.
  The chosen open `W : U.left.Opens` satisfies
  `W = (⨆ d ∈ D₀, V d)`. Therefore its scheme is exactly the union of the
  selected disjoint affine summands, with the restricted structure sheaf.
  `W.ι` is its canonical open immersion into U, by Mathlib's existing instance.
- `CompactSpace W.toScheme` says that the selected scheme is quasi-compact.
- The two concluding clauses `IsEtale (...)` and `IsSurjective (...)` apply
  to the literal restriction of p: its source is
  `Over.mk (W.ι ≫ U.hom)`, its canonical map to U is
  `Over.homMk (U := Over.mk (W.ι ≫ U.hom)) (V := U) W.ι rfl`, and its
  presheaf map is `yoneda.map` of that inclusion, composed with p.
  These are precisely the representable surjective etale restricted atlas.

Hypotheses and conclusions of the independent theorem:

- `(B C : AlgebraicSpace S)` and `(f : B ⟶ C)` introduce the two arbitrary
  algebraic spaces and their morphism, independently of the first theorem.
- The point map is the existing `mapPoint f.hom.hom`, not an unconstrained
  function. `hf : Continuous (...)` is the stipulated continuity;
  `hs : Function.Surjective (...)` is the stipulated point surjectivity.
- `hB : CompactSpace (Point B.obj.obj)` is source quasi-compactness, and the
  conclusion `CompactSpace (Point C.obj.obj)` is target quasi-compactness.
  No representability or etaleness is added to this independent implication.

The final theorem explicitly states the node's “in particular”: for arbitrary
`Z`, `U`, and `p`, `hp : IsEtale p`, `hs : IsSurjective p`, and
`hU : CompactSpace U.left` imply `CompactSpace (Point Z.obj.obj)`.
The source hypothesis is on the scheme U, not on an unproved identification of
scheme points with presheaf point classes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (full signatures and docstrings read at lines 36–46, 73–75).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `IsSurjective`, and `IsRepresentableWith`.
  Their signatures and definitions were read in full. The latter two properties
  quantify over every scheme test and give actual representing pullback squares.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, with the existing point-class
  `Point` and `schemePointMap` declarations from its public import
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`; both modules read in full.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  whose signature and docstring were read at lines 34–39.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
  and its `IsOpenImmersion` instance (lines 43–57). These give actual restricted
  schemes, not merely open subsets with chosen structure.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen` (lines 250–252).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`
  (lines 40–52). Its docstring and entire quotient-map construction were read.
  The already landed definition node `def-sfb-proper-curve-moduli` explicitly
  includes induced point maps and records this declaration, so it was added to
  `stmt_deps` under the permission to add landed definition dependencies.
  No curve, properness, or other hypothesis from that module is imposed here.

Proof dependencies read: open-immersion base change is
`isOpenImmersion_stableUnderBaseChange` in Mathlib's OpenImmersion (lines 842–845);
etale open restriction is the instance at Etale lines 95–97;
affine compactness is `Scheme.compactSpace_of_isAffine` at AffineScheme 561–564,
and its other clause is `quasiSeparatedSpace_of_isAffine` at QuasiSeparated 167–168;
continuous image compactness is `isCompact_range` at Compact 974–975.
Their modules are imported. The proof dependency `lem-a1-space-point-open-calculus`
has neither a Lean record nor a Mathlib match on the read base, so it supplies no
module to import. Its entire statement was read; no declaration belonging to it
is required to type these statements. It is cited in the proof docstrings.
The downstream `AlgebraicSpaceEtaleOpenImage.points_compactSpace_iff` is weaker
than the specified-component assertion and is not used as a replacement or import.

Edge cases checked before writing:

- Empty Z: the empty finite subset is allowed. Its supremum is the bottom open,
  whose scheme is empty and compact; its atlas to empty Z is representable,
  etale, and surjective. No `Nonempty` assumption occurs anywhere.
- Empty index type: the covering equality forces U empty; surjectivity of the
  atlas forces the point space empty. The same empty selection applies.
- Empty affine summands (Spec of the zero ring) are permitted and can be omitted.
  Disjointness does not force connectedness or nonemptiness.
- Infinitely many components and a one-point target: only finite selection of
  image opens is used, and no finiteness of D or compactness of the original U
  is assumed.
- Empty B in the independent implication: surjectivity forces C's point space
  empty, so compactness remains correct. The empty atlas case also remains included.
- There is no separation, Noetherian, characteristic, or quasi-separatedness
  hypothesis on the spaces or atlas. No intersection of affine opens is assumed
  affine. The unused in-proof quasi-separatedness leaf imports no such assumption.
- Universe u is the existing scheme/site universe; point classes live in u+1.
  Index universe v is independent and unrestricted, because the given family is
  represented inside the existing scheme U. There is no existence claim for an
  oversized coproduct, and no change to the test-scheme or field universes.

Searches actually run (logged by msearch.py in searches.jsonl):

- LeanFinder query: “A quasicompact algebraic space admits a finite union of
  components of any disjoint affine etale atlas covering the space”. Eight
  results, all scheme-cover results: `QuasiCompactCover`,
  `ExistsHomHomCompEqCompAux.𝒰D`, `quasiCompactCover_iff`,
  `Scheme.quasiCompactCover`, `QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen`,
  `QuasiCompactCover.inst`, `instIsAffineXSchemeFiniteSubcover`, and
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`. None states finite
  component selection for an algebraic-space atlas. This read-only query was
  repeated after a provider interruption; both successful calls are logged.
- Loogle query: `"AlgebraicSpace", "CompactSpace"`; zero results.
- msearch grep query: `AlgebraicSpace|finite.*subatlas|quasi.?compact.*atlas`
  in Mathlib/AlgebraicGeometry; zero results.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf` and upstream-name records
  for the item id, subatlas, compact point/atlas declarations and the proposed
  declaration names: no exact existing declaration. The only related comparison
  is `AlgebraicSpaceEtaleOpenImage.points_compactSpace_iff`, which neither
  selects components of the prescribed atlas nor states the independent
  arbitrary-morphism implication. Direct rg located the existing `mapPoint`
  definition in ProperCurveModuli, which is reused here.
- Direct rg across Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json
  found no collision for any of the three proposed theorem names.

Validation: prescribed scompile.py compiled the sandbox probe and final library
module successfully on the server (2.0 s and 5.6 s respectively); no diagnostics.
All three theorem proofs are exactly `by sorry`; all variables and universes are
explicitly bound. There is no STATEMENT-DISPUTED finding.

## Second reading by N7

This is the author's separate second pass. The dispatched brief forbids starting
other agents; the maintainer supplies the independent review of the delivery.
Reading the node again against the complete module found no mismatch: hZ is on
point classes, U and p are the prescribed atlas, hV/hd/hc retain the stated
summands and their disjoint open coproduct topology, D₀ is a finite subset of the
original index type, W is exactly their union, its compactness and both restricted
atlas properties are explicit. The independent theorem has only the stipulated
continuity, surjectivity and source compactness, and the final theorem retains
scheme-source compactness. The empty index and empty target cases are admitted.
The point-map definition was found in an already landed module during this pass;
its owning node was added as a statement dependency rather than duplicating it.
No other node field or statement was changed.
