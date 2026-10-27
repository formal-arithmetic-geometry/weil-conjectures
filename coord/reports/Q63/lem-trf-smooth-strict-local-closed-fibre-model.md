## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothStrictLocalClosedFibreModel` states
`AlgebraicGeometry.Scheme.smooth_strict_local_closed_fibre_model`, with one `sorry`.
It constructs only the node's named W, κ, Z and extended ideal, using existing pullbacks,
quotients, geometric strict local rings and the canonical functorial map. These helper
names are listed in `lean.declarations`; no independent notion or dependency repair is needed.
Every universe is explicit (`u`); `autoImplicit` is false.

Hypotheses and clauses, in statement order:

- Schemes V,S and the smooth morphism f are `{V S : Scheme.{u}} (f : V ⟶ S) [Smooth f]`.
- The arbitrary algebraically closed geometric field and point are
  `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)`.
  The base point is exactly `v ≫ f`, and A,B are the existing
  `strictHenselizationRing (v ≫ f)` and `strictHenselizationRing v`.
- The canonical map φ is `(Spec.preimage (strictHenselizationMap f v)).hom`.
  This is the uniquely pointed functorial morphism, not an arbitrary ring map.
- Locality of A is supplied in the conclusion, not assumed. The equality of the kernel
  of `strictHenselizationPointEvaluation (v ≫ f)` with `IsLocalRing.maximalIdeal A`
  identifies the constructed quotient κ with exactly A/m_A. `IsField` records that it
  is a field. This kernel-based construction avoids both a choice of local structure
  in definitions and an extra mathematical hypothesis. There is no change of the node.
- The embedding κ→Ω is exactly `RingHom.kerLift` of canonical evaluation. Its injectivity
  is the existing `RingHom.kerLift_injective`. Its composite with the quotient is
  evaluation by the definition of kerLift, so `Spec.map` gives the specified closed
  geometric point of Spec A, retaining its full residue embedding.
- `smoothStrictLocalBase f v` is exactly W, the pullback of f and the recorded structural
  map. `smoothStrictLocalClosedFibre f v` is exactly Z, the pullback of W→Spec A along
  Spec of the quotient A→κ. These are full scheme fibre products.
- `zbar` in the conclusion supplies the geometric point of Z. Its composite with both
  first projections is v, and its composite with the second projection is Spec of the
  above κ→Ω embedding. Thus its image in W is exactly the pair (v,a). Its underlying
  point z is `zbar (IsLocalRing.closedPoint Ω)` throughout the conclusion.
- `Smooth (pullback.snd ... ...)` states Z smooth over κ.
  `IsClosedImmersion (pullback.fst ... ...)` states the specified Z→W closed immersion.
- For every ring D and open immersion `j : Spec D ⟶ W`, the statement gives an isomorphism
  from the inverse image `pullback i j` to `Spec (D ⧸ Ideal.map α m_A)`.
  Here α is precisely `Spec.preimage (j ≫ p)`, with p:W→Spec A. Its displayed equation
  over Spec D identifies the projection with Spec of the quotient map. This covers
  every affine open, not only a chart at z, and retains the nonreduced ideal.
- `eW` identifies the strict local ring at the lifted point of W with B. Its structural
  square over V and its evaluation equation make this the canonical pointed comparison.
  Its A-action equation identifies the induced map A→H_W with φ after eW.
- `eQ` gives B/m_A B ≃ O^sh_(Z,zbar), with the extended ideal constructed by `Ideal.map φ`.
  The equation for `eQ.toRingHom.comp (Ideal.Quotient.mk ...)` identifies the quotient
  map with the functorial map of Z→W composed with the inverse of eW. An abstract ring
  isomorphism alone would not suffice; this equation is included.
- `IsRegularLocalRing` is asserted both for the ordinary stalk at z and for the geometric
  strict local ring. Its Mathlib definition extends `IsLocalRing` and `IsNoetherianRing`,
  hence includes all the node's Noetherian and regular-local assertions.
- The concluding `Algebra` on κ(z)→Ω is constrained to be exactly the residue homomorphism
  of zbar, through `descResidueField (stalkClosedPointTo zbar)`.
  The literal `IsLocalRing.ResidueField` of the stalk is used to make its canonical
  algebra instances visible; this is exactly `Scheme.residueField`'s underlying field.
- `separableClosure` with that algebra is exactly the separable closure inside Ω required
  by the statement. Its stalk algebra is required to factor through the residue field
  by `IsScalarTower`. No arbitrary separably closed extension is substituted.
- `P : Algebra.StrictHenselizationPresentationIn.{u,u} R K H_Z` equips the geometric
  strict local ring with the defining universal pointed-etale colimit presentation of
  the algebraic strict henselization of R=O_(Z,z). This supplies the second isomorphism:
  `P.identification` is the specified algebra isomorphism from the colimit model to H_Z;
  its inverse gives H_Z ≅ R^sh. No separate noncanonical R^sh is selected. The structural
  equation `Spec(algebraMap R H_Z) ≫ Z.fromSpecStalk z = strictHenselizationStructuralMap zbar`
  fixes its ordinary local-ring map; the final subtype/evaluation equation fixes its
  pointing in Ω and hence the canonical comparison.
- There is no regularity, Noetherianity, separatedness or quasi-compactness assumption
  on S. All local and algebra structures needed by the conclusion are existential
  output data; no hypotheses have been added for them.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` for the inline
  geometric-point convention.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`.
- `Sheaf.Paper.StrictHenselizationFunctoriality`: `strictHenselizationFunctoriality`;
  its existing canonical packaging in
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`: `Scheme.strictHenselizationMap`.
  Its `existsUnique` characterization is why the displayed maps are canonical.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` and its `residueMap`, including the actual
  pointed-etale diagram, cocone, universal property and algebra identification.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the scheme convention, whose ring clauses
  use Mathlib `IsRegularLocalRing` (`Mathlib.RingTheory.RegularLocalRing.Defs`).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`; the local quotient is literally `IsLocalRing.ResidueField`.

All recorded proof modules that have declarations are imported, including the affine
strict-local comparison, closed-immersion cartesian comparison, affine pullback formula,
smooth-over-field regularity, and the upstream Noetherianity and regularity statements.
The proof-only node `lem-trf-smooth-strict-local-base-model` has no Lean record on the read
base, so has no module to import. It is not needed to type the statement. Its intended use
is recorded in the theorem's six-step proof docstring. The theorem
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine` uses `HasRingHomProperty.Spec_iff` from the
explicitly imported `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`.

Source reading: Stacks `algebra.tex` lemma-quotient-strict-henselization (05WS),
`etale-cohomology.tex` lemma-describe-etale-local-ring (04HX), `morphisms.tex`
lemma-base-change-smooth (01VB), `algebra.tex` lemma-characterize-smooth-over-field
(00TT), and `more-algebra.tex` lemma-henselization-regular (06LN), with its 06LJ dependency.
The quotient theorem allows a general ideal; no reduction or finiteness assumption on
m_A is introduced. The regularity argument is entirely over the closed-fibre field.

Edge cases checked: a geometric point rules out empty V and S automatically, without
an added nonemptiness hypothesis. Relative dimension zero is included. Nonperfect
positive-characteristic fields and geometric Ω larger than the separable closure remain
allowed. Singular, non-Noetherian and nonregular bases remain allowed. Arbitrary affine
opens include the empty one (D the zero ring), so the affine-model assertion must allow
its zero quotient and empty spectrum; it does. The extended ideal is not assumed radical
or finitely generated. The geometric point makes its extension in B proper. The kernel
model does not replace the residue field by Ω or discard the purely inseparable part
of the geometric embedding. All scheme and ring objects share the arbitrary universe u;
the algebraic presentation uses the recorded `In.{u,u}` common-universe specialization.

Searches actually run through the prescribed wrapper:

- leanfinder: `Smooth morphism closed fibre of strict henselization is strict henselization
  of fibre regular local ring` (twice): eight smooth-chart/locus hits, including
  `RingHom.Smooth.locally_isStandardSmooth` and `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth`;
  no strict-henselization closed-fibre comparison.
- loogle: `strictHenselization, Smooth, IsRegularLocalRing`: zero hits; unknown identifier
  `strictHenselization` in that service.
- grep: `strictHenselization.*quotient|smooth.*strict.*local|closed.*fibre.*regular`,
  Mathlib `RingTheory`: zero hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the item's id, strict/smooth/fibre
  terms and the proposed declaration names: the only exact item-id hit is the consumer
  docstring in `AffineCoordinateStrictLocalModel.lean`; no existing statement. Broader
  hits include smooth strict-local field models and closed-immersion cartesian comparison,
  whose full signatures were inspected and do not state this node.
- Direct grep of the item id in `lean/WeilConjectures`: no hit.
- `scompile.py --source Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` confirmed
  the current published canonical interface agrees with the local source.

No statement correction, new DAG node, dependency repair, or mathematical dispute.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
