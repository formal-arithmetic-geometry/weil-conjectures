## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSpaceFiniteImageNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_closed_image_affine_neighbourhood`.
Its only postponed proof is this named theorem, whose docstring contains all six
steps of the node's accepted proof. `finiteImageBaseChangeMap` is a transparent,
fully constructed wrapper around Mathlib's `Limits.pullback.map`, used to display
both the geometric-fibre hypothesis and the neighbourhood factorization. It
introduces no new notion and chooses no data from an existence theorem.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-flat-proper-family-cannot-collapse-fibre` (Tag 0AEJ), lines 7930–7978,
especially (3)(a) and the finite closed subspace conclusion. The source permits
an arbitrary representative field; the node asks for an algebraic closure.
The restriction to a scheme base and the affine shrink are exactly those of the
node, and the finite convention is scheme-test representability, as specified
in the node's reference to Tag 03ZP. No node correction is needed.

Hypotheses, individually:

- `T : Scheme.{u}` is the arbitrary scheme base, using def-pc-scheme.
- `X Y : AlgebraicSpace T` are the algebraic spaces over that base. No scheme
  representability of X or Y is assumed. A scheme is represented by the existing
  `schemeSpace (Over.mk (𝟙 T))`; this is the actual Yoneda sheaf of T, not an
  independently chosen terminal object or a private algebraic-space definition.
- The binders `p`, `q`, and `h` are the three morphisms in the node. The equation
  `w : h ≫ q = p` states exactly `qh = p` in composition order.
- `hp : MapIsProper p` is properness in def-sfb-space-morphism-properties:
  separated, finite type, and universally closed on point spaces.
- `hq : MapIsSeparated q` is the representable closed diagonal condition.
- `hqlft : MapIsLocally (@LocallyOfFiniteType) q` is precisely the recorded
  chartwise locally finite type condition; no global finite type or properness
  of q is added.
- `t : T` is the chosen point. `Ω : Type u`, `[Field Ω]`,
  `[Algebra (T.residueField t) Ω]`, and `[IsAlgClosure (T.residueField t) Ω]`
  give any algebraic closure of its residue field in the test-scheme universe.
  This is the existing size convention, not an extra equality of universes.
- The geometric point is the actual composite
  `Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
  T.fromSpecResidueField t`, regarded as a morphism in `Over T`.
- `finiteImageBaseChangeMap p q h w` forms the two actual presheaf fibre products
  with this geometric point and their canonical map induced by h and the identity
  of the geometric point. `hfinite` asserts that its `pointImage` is a finite set
  of the recorded field-valued point classes. It is not the set of Ω-valued
  sections, which would encode a different finite-image condition.

Conclusion, clause by clause:

- `∃ V : T.Opens, t ∈ V ∧ IsAffineOpen V` is an affine open neighbourhood of t.
- `Z : Over T` supplies an actual scheme representing the requested subspace.
  This is allowed by the node's explicit conclusion that Z is an affine scheme;
  it assumes no representability of X or Y.
- `g : Z ⟶ Over.mk V.ι` makes Z a scheme over V, retaining its map to T as well.
- The target of `j` is exactly the presheaf fibre product of q and `V → T`;
  the source of `a` is exactly the corresponding fibre product of p and `V → T`.
  These are Y_V and X_V, respectively. They are the sheaf fibre products from
  lem-trf-space-fibre-products-etale-covers: limits of fppf sheaves have these
  underlying presheaf limits. Both are algebraic spaces by the recorded theorem.
- `IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) j` is the
  scheme-test closed immersion condition, exactly the node's closed subspace.
- `a ≫ j = finiteImageBaseChangeMap ...` is exactly `h_V = ja`, written in
  Lean's forward composition order with the equality reversed.
- `j ≫ pullback.snd ... = yoneda.map g` says j lies over V. The next equation
  `a ≫ yoneda.map g = pullback.snd ...` says a is a V-morphism. These equations
  retain the actual structural maps, rather than an arbitrary factorization of
  underlying sets or sheaves without its base compatibility.
- `IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) (yoneda.map g)` gives
  exactly the specified finite convention: scheme-representability with a finite
  projection after every scheme test. This is stronger data than simply saying
  the underlying point fibres are finite, as the node requires.
- `IsAffine Z.left` explicitly supplies the affine-scheme conclusion.
- `(g.left.appTop).hom.Finite` says that the coordinate-ring map from Γ(V, O_V)
  to Γ(Z, O_Z) is finite, i.e. the latter is a finite module over the former with
  its scalar action induced by this map. It is not an unrelated ring action.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  signatures and defining docstrings read at lines 36–46 and 73–75.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and their full defining docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsSeparated`, and `MapIsLocally`, read in full. The first two are the
  actual recorded definitions; no scheme-only properness substitutes for them.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, full signature and proof docstring read.
  The signature uses the actual sheaf pullback and its universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`, `Point`,
  and `PointRepresentative.map`; definitions and their docstrings read in full.
  `ProperCurveModuli.mapPoint` was also read to check point-image conventions.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  read at lines 41–46; `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`,
  read at lines 34–40, and the finite global-section map at lines 170–172.

Imports for the already stated proof dependencies include
`AlgebraicSpacePointOpenCalculus`, `SeparatedLocallyQuasiFiniteSpaceRepresentable`,
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`, and Mathlib's
`ZariskisMainTheorem` and `Morphisms.UniversallyInjective`. The source signatures
of `point_open_calculus` and `exists_scheme_of_separated_locally_quasi_finite`
were read, together with the recorded Mathlib matches of the other proof inputs.
The four proof prerequisites with no recorded Lean statement are not imported:
lem-sfb-space-proper-schematic-image,
lem-sfb-space-finite-fibre-quasifinite-criterion,
lem-sfb-space-quasifinite-locus-open, and lem-sfb-space-proper-base-change.
They are not needed to type this stage-2 statement and the accepted proof is
retained for their eventual use. The affine-basis Mathlib match is provided by
`Mathlib.AlgebraicGeometry.AffineScheme`, available through the proof imports.

The existing `schemeSpace` constructor is imported from
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` and was read at lines 65–80.
Its data is the actual representable fppf sheaf; its named algebraic-space proof
is already published. This is just the scheme-as-algebraic-space encoding of
our existing notions; no new mathematical definition or DAG node is introduced.

Edge cases checked: the empty geometric image is permitted by `.Finite` and
there is no nonempty source or nonzero coordinate-ring condition. The zero ring
therefore permits an empty finite image scheme. Empty T has no t, making the
pointed assertion vacuous, exactly as in the source. Arbitrary characteristic,
nonreduced and non-Noetherian bases are allowed. Neither X nor Y is required
connected, flat, reduced, or representable by a scheme. Ω is arbitrary subject
to being an algebraic closure of the selected residue field. The base field and
residue field use the same universe as the scheme tests, as in the recorded
algebraic-space framework; point classes themselves live in `Type (u + 1)`.

Searches actually run with msearch.py:

- LeanFinder: "A proper algebraic space mapping to a separated locally finite
  type space with finite geometric fibre image factors through a finite closed
  subspace near that fibre". Eight results: scheme properness, IsFinite,
  LocallyQuasiFinite, and LocallyOfFiniteType. No algebraic-space match.
- Loogle: `"IsProper", "IsFinite"`. Six results including
  `IsFinite.of_isProper_of_locallyQuasiFinite` and
  `IsFinite.iff_isProper_and_locallyQuasiFinite`, all for schemes.
- grep: `finite.*image|image.*finite|finite_imageι` in `AlgebraicGeometry`.
  Twenty-two hits, including the scheme-only
  `exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`.
  Read its complete signature and proof at ZariskisMainTheorem.lean:424–440:
  its X and Y are schemes, so it does not state the assigned theorem.
- LeanSearch: "A proper family mapping to a separated locally finite type
  algebraic space has finite closed image near a finite geometric fibre image".
  Eight results on scheme properness and topological proper maps; no match.

Direct rg searches in both `lean/WeilConjectures` and `lean/Sheaf` checked
`finite.*[Ii]mage|[Ii]mage.*finite`, then the more specific
`proper.*finite.*image|finite.*closed.*image|finite_imageι`, and the exact
node id. None states this algebraic-space theorem. The exact proposed names
`finiteImageBaseChangeMap|exists_finite_closed_image_affine_neighbourhood`
were searched in both trees, Mathlib, and dag/lean_names_upstream.json; no clash.
The node-id search in WeilConjectures also had no hit. There is no duplicate
notion; the only new definition is a named use of the existing canonical
pullback-map construction for this theorem's two base changes.

Validation: scompile.py compiled the file on the server in both sandbox mode
and its real module name, with no errors or warnings. The first attempt exposed
that unqualified `pullback` resolves to algebraic-space module pullback in this
namespace; the file now names `Limits.pullback` explicitly. No statement was
changed to address that name-resolution error. All binders and universes are
explicit and `autoImplicit` is disabled. No diagnostics remain in the module.
No statement dispute, dependency repair, or new node is needed.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
