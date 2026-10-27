## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothCoordinateBlowupCharts` states
`AlgebraicGeometry.SmoothCoordinateBlowup.smooth_coordinate_blowup_charts`.
The only postponed proof is that theorem, with the node's eight-step proof in its
docstring. No mathematics is proved in this delivery. The five preceding definitions
are explicit specializations/packaging of the very coordinate functions, ideals and
conclusions in this node; none chooses an unspecified object or introduces a separate
mathematical notion. All data are fully defined, with no postponed definition proofs.
The node changes only in `lean`; no corrected statement, new node, or dependency repair
is needed.

Clause-by-clause correspondence (names below are in `AlgebraicGeometry.SmoothCoordinateBlowup`):

- Any field F is `(F : Type u) [Field F]`; `n : ℕ` includes zero;
  `(V : Scheme.{u})` includes arbitrary schemes in the field's universe.
  `c : V ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of F))` with `[Smooth c]`
  is the smooth coordinate map. The structure morphism to F is its composite with
  `AffineSpace.over`; thus c is over F. There is no perfection, integrality,
  separatedness, finite-type, or quasi-compactness assumption on V.
- `coordinates c a = c.appTop (AffineSpace.coord (Spec (.of F)) (ULift.up a))`
  is precisely the pulled-back coordinate. `Fin n` uses indices 0 through n-1
  instead of 1 through n. `ULift` supplies Mathlib's required index universe without
  changing the finite coordinate set.
- Every subset A is a `Finset (Fin n)`. `intersection z A` is the ideal sheaf
  `ofIdealTop (Ideal.span (z '' (A : Set (Fin n))))`; its `subscheme` is the
  scheme-theoretic intersection, not its reduction. `CoordinateGeometry` quantifies
  over every A and asserts `Smooth (subschemeι ≫ p)`, `IsReduced subscheme`, and
  `IsRegularScheme subscheme`. The latter is the recorded predicate including local
  Noetherianity, not just stalkwise regularity.
- Pure codimension is asserted at every generic point η of every irreducible
  component Z of that subscheme: `ringKrullDim (V.presheaf.stalk (subschemeι η)) =
  (A.card : WithBot ℕ∞)`. This is codimension of the component in the regular ambient
  scheme. It is vacuous for the empty intersection and imposes the stated pure
  codimension on every component when nonempty. It adds no equidimensionality
  requirement on V itself.
- `IsIso (intersection z ∅).subschemeι` expresses `C_empty = V` over V, with the
  canonical inclusion, rather than requiring definitional equality of constructed
  scheme records.
- At each x, the explicit witness `hR : IsNoetherianRing (V.presheaf.stalk x)` allows
  use of the dependency's `IsLocalRing.IsRegularSystemOfParameters t`. Vanishing
  coordinates are exactly those whose global-section germs belong to the maximal
  ideal. `Function.Injective f` into `Fin t.length`, together with
  `t.get (f a) = germ (z a.val)`, states that each is a distinct member of the supplied
  parameter system. It neither orders the vanishing set nor silently identifies two
  coordinate labels.
- `∀ S T : Finset (Fin n), S.Nonempty → S ⊆ T → ...` is exactly the specified
  nonempty S contained in T. `boundary z A = equation (∏ a ∈ A, z a)` uses the actual
  product equation. The assertions `.IsInvertible` and `IsReduced ...subscheme`
  for T and S say B_T and D_S are reduced effective Cartier divisors, using the
  dependency's existing effective-Cartier predicate.
- `(intersection (coordinates c) S).blowup` and `.blowupMap` are the existing ordinary
  global blowup, not an arbitrary modification. The equality witness h identifies
  its center ideal with the comap of the coordinate ideal on affine space.
  `eqToHom (congrArg ...blowup h) ≫ I.blowupFlatBaseChange c` is therefore the
  canonical comparison, whose `IsIso` is explicitly asserted. The upstream canonical
  comparison has fiber factors in the opposite order from the DAG definition's
  display; this is harmless here because this item names a pullback without ordering
  its factors. No replacement by an arbitrary isomorphism is made.
- `W : S → Scheme`, `ι : ∀ j, W j ⟶ ...blowup`, the assertions
  `∀ j, IsOpenImmersion (ι j)` and `∀ x, ∃ (j : S) (w : W j), ι j w = x`
  express an open cover indexed by j in S, permitting empty W j. Each q j maps
  to affine n-space and is smooth, and the displayed equality of composites with
  `AffineSpace.over` makes it a map over F.
- The chart coordinates are `coordinates (q j)`. For `a = j.val ∨ a ∉ S` they
  equal the pullbacks of the original z_a. For `a ∈ S.erase j.val`, the equation
  `pullback(z_a) = coordinates(q j) j.val * coordinates(q j) a` states
  `z_a = z_j u_a`. Together with the chart parameter geometry these are the usual
  ratio coordinates, including their behavior where z_j vanishes.
- The exceptional ideal is the center ideal comapped along `ι j ≫ blowupMap`;
  its equality with `equation (coordinates (q j) j.val)` is the equation z_j=0.
- The reduced full inverse image is the radical of the comapped B_T ideal, then
  restricted to the chart. Its equality with `boundary (coordinates (q j)) T`
  is exactly `z_j * ∏_(S\\{j}) u_a * ∏_(T\\S) z_a`, since S is contained in T.
  This is equality of ideal sheaves and hence of scheme structures.
- The strict transform uses `AlgebraicGeometry.strictTransformMap` with the actual
  D_S inclusion, actual blowup map, and the complement of the actual center support.
  Its kernel ideal is the defining ideal of the schematic strict transform in
  the blowup (the composite is a closed immersion because D_S is closed).
  Comapping this ideal to the chart and equating it to
  `boundary (coordinates (q j)) (S.erase j.val)` states precisely the ratio-product
  equation. It uses schematic closure, not merely topological closure.
- `CoordinateGeometry ... (coordinates (q j))` repeats every intersection and
  parameter clause for the entire chart coordinate list. In particular it applies
  to every chosen subset of the displayed boundary factors, with pure codimension
  the number of those factors.
- `S.card = 1 → IsIso ...blowupMap ∧ IsEmpty (...strictTransform ...subschemeι)`
  states the singleton case, including the empty strict transform of D_S. The
  strict-transform object here is the recorded ideal-sheaf specialization of the
  same upstream schematic strict transform used for the equations.

Dependency declarations read and used:

- Mathlib `Field` (`Mathlib.Algebra.Field.Defs`), `Scheme` and its morphisms
  (`Mathlib.AlgebraicGeometry.Scheme`), `AffineSpace`, `AffineSpace.coord`,
  `AffineSpace.over` (`Mathlib.AlgebraicGeometry.AffineSpace`), `Smooth`
  (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`), `IsClosedImmersion`
  (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`), `IsReduced`
  (`Mathlib.AlgebraicGeometry.Properties`).
- `AlgebraicGeometry.IsRegularScheme`
  (`Sheaf.AlgebraicGeometry.IsRegularScheme`), defined by the existing locally
  Noetherian and stalk-regular predicates; `IsLocalRing.IsRegularSystemOfParameters`
  (`WeilConjectures.RingTheory.IsRegularSystemOfParameters`).
- `Scheme.IdealSheafData.IsInvertible`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`);
  `Scheme.IdealSheafData.blowup`, `blowupMap` (`WeilConjectures.Blowup.Gluing`);
  `AlgebraicGeometry.strictTransform`, `strictTransformMap`, and the ideal-sheaf
  `strictTransform` specialization (`WeilConjectures.Compactification.StrictTransform`).
- Mathlib `Scheme.IdealSheafData.subscheme`, `subschemeι`, `ofIdealTop`, `radical`,
  `comap` and `Scheme.Hom.ker` implement the closed equations, full inverse image,
  and reduction. The recorded scheme-reduction interface is the quotient by the
  nilradical; applied to a closed subscheme it is equivalently the quotient of the
  ambient structure sheaf by the radical of the defining ideal. This existing
  radical operation keeps the ambient ideal-sheaf equation visible.
- `Scheme.IdealSheafData.blowupFlatBaseChange`
  (`WeilConjectures.Blowup.FlatBaseChange`) is already supplied by the closed
  slopmaster2 audit of `def-nagata-blowup-flat-base-change-map`. No restatement.
  The module also supplies the audited theorem's `blowupFlatBaseChangeIso`.

All recorded modules of stated proof dependencies are imported: Proper/Smooth for
base change, the upstream affine-space smoothness instance, the upstream regularity
and regular-local-domain declarations, Mathlib Regular.Flat/Flat.Basic for
localization and tensor exactness, KrullDimension.Regular, LocalRing.Module,
RegularLocalQuotientKernelParameters, RegularLocalGeneratorsRegularSequence,
CoordinateSubspaceBlowupCharts, FlatBaseChange, and the schematic-image and
strict-transform interfaces. Imports needed only for the future proof are not public.

Edge cases checked before and after writing: n=0 leaves only A=empty and no nonempty
S; A=empty has zero ideal, gives V, and has codimension zero at every component's
generic point; empty V and empty W j are allowed; empty coordinate intersections
have no generic-point constraints; nonvanishing coordinates are omitted from the
parameter injection; the empty parameter list is allowed for dimension-zero stalks;
T=S leaves no unchanged boundary factors; a singleton S gives an isomorphism and
ratio product 1, hence the empty strict transform; disjoint components and arbitrary
imperfect fields are covered. Neither a global bound on smooth relative dimension
nor global quasi-compactness is used.

Searches for existing declarations:

- `msearch.py ... leanfinder` query `Smooth coordinate subspace blowup charts
  exceptional divisor strict transform regular parameters`: 8 hits, including
  `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth`, relative standard-smooth
  charts, and unrelated manifold charts. No matching coordinate blowup statement.
- `msearch.py ... loogle` query `AffineSpace, IdealSheafData.blowup`: 0 hits with
  unknown unqualified identifier `AffineSpace`; supplemented by the successful
  LeanFinder search and source searches below.
- `msearch.py ... grep` query `coordinate.*blowup|blowup.*coordinate` in
  `AlgebraicGeometry`: 0 Mathlib hits.
- `msearch.py ... leansearch` query `Smooth pullback of coordinate subspace blowup
  has smooth charts exceptional divisor and strict transform equations`: 8 hits,
  mostly manifold pullback facts and the smooth-relative-dimension base-change
  instance. None is the statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for coordinate/blowup combinations:
  found `CoordinateSubspaceBlowupCharts`, `ParameterBlowupCoordinateQuotients`,
  `PermissibleCoordinateChart`, and related normal-crossings modules. Read the
  coordinate-subspace declaration in full and imported it as the recorded proof
  dependency; it is over a ring with a reordered coordinate list, and does not state
  this node's arbitrary smooth pullback, boundary, and parameter assertions.
- `rg` for this item's id in `lean/WeilConjectures` returned no declaration.
  `rg` for the chosen namespace/theorem/helper names in both roots, Mathlib, and
  `dag/lean_names_upstream.json` returned no collision.

Sources inspected directly: Stacks `more-morphisms.tex`, displayed charts of
remark-relative-blowup (0H1H) and proof of lemma-blowup (0FUT), and ILO VIII
4.2.9 at printed p.121 (PDF text extracted in the sandbox). These agree with the
coordinate substitution used here. The example CompactObject module is withdrawn;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, whose current
header and docstring conventions were read instead.

Validation: the prescribed `scompile.py NF lem-sfb-smooth-coordinate-blowup-charts`
compiled both the sandbox probe and the actual library module cleanly (2.1s and
1.9s), with no unexpected warnings. `autoImplicit` is false and u is explicitly
bound. No `STATEMENT-DISPUTED` issue was found.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
