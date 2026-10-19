## Worker report

The delivery states `AlgebraicGeometry.nodal_curve_lci_criterion` in
`Sheaf.AlgebraicGeometry.NodalCurveLCICriterion`. The sole theorem has proof `by sorry`;
no new definition, dependency module, or statement correction is needed.

Read the full item, its eleven statement-dependency nodes and their recorded interfaces,
Curves Tag 0C4E (`lemma-nodal-lci`), the pointwise explanation in Tags 0C4D and 0C4C,
and the existing first-Fitting, pure-dimension, complete-intersection and geometric-fibre
modules. The source says precisely that a locally algebraic equidimensional curve is
at worst nodal iff it is LCI with unramified first-Fitting singular subscheme.

Hypotheses and clauses, matched individually:

- The field is `(k : Type u) [Field k]`, the scheme is `(C : Scheme.{u})`, and its given
  structure morphism is `(f : C ⟶ Spec (CommRingCat.of k))`.
- Local finite type is `[LocallyOfFiniteType f]`. No properness, quasi-compactness,
  separatedness, connectedness or nonemptiness hypothesis is imposed.
- Equidimensionality of dimension one is `(hC : C.IsPureDimension 1)`; the recorded
  definition quantifies over irreducible components, including the empty scheme vacuously.
- The left side quantifies over `x : C` with `x ∈ closedPoints C`. Its first disjunct is
  membership in `f.smoothLocus`, meaning smoothness at that point.
- Its second disjunct chooses `xbar` in the actual pullback of `f` along the canonical
  `Spec (AlgebraicClosure k) → Spec k`. The equation with `pullback.fst` says exactly
  that `xbar` lies over `x`.
- The completed local ring is `AdicCompletion (IsLocalRing.maximalIdeal A) A`, where
  `A` is the structure-sheaf stalk of that pullback at `xbar`. `Nonempty (Ahat ≃+* B)`
  expresses existence of a ring isomorphism, without imposing a coefficient-algebra
  compatibility absent from the statement. Here `B` is
  `MvPowerSeries (Fin 2) (AlgebraicClosure k)` modulo the ideal spanned by `X 0 * X 1`.
  Choosing Mathlib's algebraic closure realizes “an algebraic closure”; the nodal
  completion condition is invariant under its k-algebra isomorphisms.
- The equivalence is `↔`. The first conjunct on the right says every point belongs to
  an affine open `U` whose coordinate ring is a finite-type local complete intersection
  over k. This pointwise affine-neighbourhood formulation is an affine open cover,
  with no finiteness of the cover imposed.
- The scalar structure on that coordinate ring is explicitly the composite of
  `(Scheme.ΓSpecIso (.of k)).inv.hom` and `(f.appLE ⊤ U.1 ...).hom`, through `toAlgebra`.
  Both the finite-type witness `ft` and `Algebra.IsLocalCompleteIntersection` use that
  exact structure. It is not an arbitrary algebra structure. `ft` is an existential
  witness inside the conclusion because the recorded LCI predicate requires it as an
  instance; it adds no assumption on the input curve.
- The singular scheme is exactly the domain of `Scheme.firstFittingSingularSubscheme f`.
  Its structure map is `Scheme.firstFittingSingularSubscheme f ≫ f`. Its unramifiedness
  is exactly the recorded inline conjunction `LocallyOfFiniteType ... ∧
  IsOpenImmersion (pullback.diagonal ...)`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `Scheme.firstFittingSingularSubscheme`, defined as the inclusion for the uniquely
  characterized `Scheme.firstFittingIdealSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and `Scheme.Hom.smoothLocus`.
  The latter has the locally-finite-presentation instance inferred from local finite
  type over the Noetherian scheme `Spec k`.
- The unramified definition reuses `LocallyOfFiniteType`, `IsOpenImmersion` and
  `CategoryTheory.Limits.pullback.diagonal` exactly as its recorded inline interface.
- `Sheaf.RingTheory.CompleteIntersectionOverField`: `Algebra.IsLocalCompleteIntersection`,
  with its finite-type instance and its principal-open global-CI cover definition.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints` (definition `IsClosed {x}`).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded base-change
  convention uses `pullback f g` and `pullback.fst`; read its current published source
  with `scompile.py --source` because this source module is absent in the older checkout.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, with its
  canonical algebra and algebraic-closure instances.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and its
  commutative-ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.

Proof-dependency imports retained: `Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension`,
`Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion`,
`Sheaf.RingTheory.SmoothLocalCompleteIntersection`, and Mathlib's finite-type/Noetherian
modules for the Jacobson and LFT-to-LFP leaves. The dth-Fitting smooth-locus lemma and
pointwise nodal criterion have no recorded Lean declarations yet, so there are no
modules of those nodes to import. They are used only in the natural-language proof plan.
No import cycle is introduced.

Edge cases checked mathematically: the empty curve has both sides vacuous and empty
unramified singular scheme; a smooth affine line has unit first-Fitting ideal and empty
singular scheme; the node `uv=0` has first-Fitting ideal `(u,v)` and one reduced singular
point; a cusp is a hypersurface but its singular scheme is not unramified (also in
characteristics 2 and 3), so neither side holds; a double line fails the reduced geometric
node condition and the unramified singular-scheme condition. Characteristic two is
included since the node is `uv`, with no division by two. A nonsplit node over k is
included by base change to the algebraic closure. No global finite-type/finite-cover
assumption excludes infinite disjoint unions of curves.

Searches actually run with `msearch.py Q121 lem-trf-nodal-curve-lci-criterion`:

- LeanFinder: “A curve over a field has smooth or nodal closed points if and only if it
  is a local complete intersection and its first Fitting singular subscheme is unramified”:
  eight results, including Weierstrass minimality/nonsingularity, smooth loci and the
  etale-locus intersection theorem; none states this equivalence.
- Loogle: `"nodal"`: twelve Lagrange interpolation declarations only.
- Grep: `nodal|ordinary.double|fittingIdeal`, Mathlib `AlgebraicGeometry`: zero hits.
- LeanSearch: “A locally finite type equidimensional curve is nodal exactly when it is
  locally a complete intersection and the first Fitting singular subscheme is unramified”:
  eight generic finite-type/formally-unramified/smooth-locus hits, no equivalence.
- `rg` in `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `nodal|Nodal|nodal_curve_lci_criterion|lem-trf-nodal-curve-lci-criterion`: no existing
  theorem matching the item; related project definitions describe nodal geometric
  fibres or projective families and are not this closed-point equivalence.

There is no statement dispute or node fault. Compilation used only `scompile.py`, with
no global build, no modification of the shared repository, and no direct git command.

## Second reading by Q121

Self-review by the dispatched worker; no other agent was started, as the brief requires.
I reopened the node and the final signature. The field, morphism, local finite type and
pure dimension hypotheses are all present. Closedness restricts exactly the points on
the left; the two alternatives are local smoothness and existence of the geometric
nodal ring completion over the same point. The conclusion retains the actual
first-Fitting subscheme, the affine LCI cover, and both parts of the unramified predicate.
The first draft's unconstrained chart algebra structure was caught and replaced with
exactly the structure induced by f. Helper definitions used during elaboration were
removed; the final file introduces only the theorem. The final docstring follows all
three DAG proof steps, including the field-stalk argument that forces a singular point
to equal its closed specialization. No hypothesis, conclusion clause, statement text,
or dependency field is changed.
