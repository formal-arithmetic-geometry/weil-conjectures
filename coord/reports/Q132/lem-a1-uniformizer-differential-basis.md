## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.UniformizerDifferentialBasis` states
`AlgebraicGeometry.uniformizer_differential_basis`, with `sorry` as its entire proof.
No definitions or other theorems are added. The node is unchanged except for its `lean` record.
There is no statement dispute, statement correction, new node, or dependency repair.

Source checked: Stacks Project, `curves.tex`, Tag 0C1E,
`lemma-uniformizer-works`, statement and complete proof (lines 2411–2430).
That lemma works locally in relative dimension one; this DAG node states its integral-curve
specialization. The recorded six-step proof explains why the curve hypotheses give the required
local dimension, why the stalk is a DVR, and why the rank-one differential module is generated
by the particular differential. The module docstring includes all six steps and their nodes.

Hypothesis and conclusion correspondence:

- A field `k`: `(k : Type u) [Field k]`. The universe `u` is explicitly declared.
- A scheme over `k`: `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`. The explicit structure
  morphism is the argument expected by the recorded curve declaration.
- Separated, integral, finite type, and dimension exactly one: `[IsIntegralCurve f]`, from
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`. Its `IsVariety` parent has
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, and `IsIntegral X`.
  Its dimension field is `topologicalKrullDim X = 1`. This is equivalent to the local-ring
  dimension convention by the recorded `Scheme.dim_eq_topologicalKrullDim`, imported for
  the proof. No projectivity, properness, algebraic closedness, perfectness, or rationality
  hypothesis is imposed.
- Smooth over `k`: `[Smooth f]` using the recorded Mathlib class.
- A closed point: `(x : X) (hx : IsClosed ({x} : Set X))`.
- The residue field is the actual stalk quotient: `X.residueField x`, the recorded
  `AlgebraicGeometry.Scheme.residueField` definition in `Mathlib.AlgebraicGeometry.ResidueField`.
- Finiteness of the residue extension: `(hfinite : (f.residueFieldAlgebraMap x).Finite)`.
  `RingHom.Finite` means module-finiteness for precisely the algebra induced by this map;
  for fields this is finite extension degree. It is not finiteness of the underlying set.
- Separability: `hsep : @Algebra.IsSeparable k (X.residueField x) _ _
  (f.residueFieldAlgebraMap x).toAlgebra`, the recorded algebraic-separability class from
  `Mathlib.FieldTheory.Separable`.
- The scalar map is canonical in both hypotheses: `Scheme.Hom.residueFieldAlgebraMap` from
  `WeilConjectures.ZetaSeries`, defined by the base-field map to its own residue field,
  `Spec.residueFieldIso`, and `f.residueFieldMap x`. It is not an arbitrary field embedding.
- `A = O_{X,x}` is literally `X.presheaf.stalk x` throughout.
- The DVR assertion is the first conjunct `IsDiscreteValuationRing (X.presheaf.stalk x)`.
  The domain instance is supplied by integrality, not assumed as an extra hypothesis.
  The recorded class is used from `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- Every uniformizer: `∀ t : X.presheaf.stalk x, IsLocalRing.maximalIdeal
  (X.presheaf.stalk x) = Ideal.span {t} → ...`. This is exactly the node's definition
  `m = tA`. No particular choice of generator is fixed.
- The module and derivation are the recorded `KaehlerDifferential` and
  `KaehlerDifferential.D` from `Mathlib.RingTheory.Kaehler.Basic`; the latter's output
  type is the former. The explicit algebra argument is the composite
  `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra`.
  Thus `k → A` is the structure morphism followed by passage to the germ, with no
  unconstrained scalar action, helper definition, local instance, or statement-level let.
  Its composite with the residue map agrees with the canonical residue-field embedding
  by naturality of the germ and residue-field maps.
- Free of rank one with basis `dt`, equivalently the specified isomorphism:
  `Function.Bijective (fun a : X.presheaf.stalk x ↦ a • @KaehlerDifferential.D ... t)`.
  Multiplication by the fixed vector `dt` is A-linear, so its bijectivity is exactly
  the A-module isomorphism `A → Ω[A/k]`, `a ↦ a dt`. It asserts both spanning and
  linear independence; no arbitrary basis or mere rank condition replaces `dt`.

All six statement dependencies use their recorded declarations without replacement. The
DVR dependency is a Mathlib leaf and uses its `mathlib_match`. The recorded curve source
was absent in the older source checkout, so its current source was read through
`scompile.py --source WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective` and
compared with the shared source. The full signatures and docstrings were read for all
statement dependencies.

Proof dependencies are imported as ordinary imports: `Scheme.dim` and
`Scheme.dim_eq_topologicalKrullDim` (`Sheaf.AlgebraicGeometry.Dimension`),
`topologicalKrullDimAt` (`WeilConjectures.Mathlib.Topology.KrullDimension`), the
scheme sobriety/generalization results (`Mathlib.AlgebraicGeometry.Properties`),
`HasRingHomProperty.Spec_iff` (`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`),
the affine-stalk localization interfaces (`Mathlib.AlgebraicGeometry.AffineScheme`),
`Algebra.smooth_over_field_regular_local` (`Sheaf.RingTheory.SmoothOverFieldRegularLocal`),
`IsRegularLocalRing.isDiscreteValuationRing`
(`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`),
`smooth_differentials_free_rank_fibre_dimension`
(`Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`),
`KaehlerDifferential.isLocalizedModule_map` (`Mathlib.RingTheory.Etale.Kaehler`),
`Algebra.separable_residue_cotangent_injective`
(`WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective`),
`Algebra.IsSeparableExtension` (`WeilConjectures.FieldTheory.SeparableExtension`), and
`IsTranscendenceBasis` (`Mathlib.RingTheory.AlgebraicIndependent.Defs`). Smooth restriction
is already in the publicly imported Mathlib smooth-morphism module. Current server sources
were read with `scompile.py --source` for the cotangent-injectivity and separability modules
missing in the older checkouts.

Edge cases checked before writing:

- The empty scheme and dimension-zero schemes cannot satisfy `IsIntegralCurve f`; no
  exceptional conclusion about a zero stalk or empty point set is asserted.
- The generic point of an integral curve is not closed; the closed-point binder excludes
  its field stalk, which would not be a DVR under the recorded convention.
- At the rational origin on `A¹_k`, any `t = uT` with unit `u` has differential coefficient
  `u mod (T)` nonzero, exactly as required by the statement.
- Nonrational finite separable points are included: for a separable irreducible polynomial
  `P`, `P'(T)` is a unit in the localization at `(P)`, and `dP` generates.
- Characteristic is unrestricted. Over `F_p(a)`, the inseparable point `(T^p-a)` has
  zero differential of its uniformizer; `hsep` excludes precisely this counterexample.
- A zero or unit element cannot generate the nonzero maximal ideal of a DVR. The
  uniformizer implication does not accidentally include these elements.
- No finite-type condition on the local ring is added; the stalk need only be essentially
  of finite type. The signature uses its actual canonical algebra structure.

Searches for an existing statement (all made for this item):

- `msearch.py ... leanfinder "At a separable closed point of a smooth curve the differential
  of every uniformizer is a basis of Kahler differentials"`: eight hits, including
  `Algebra.IsStandardSmooth.free_kaehlerDifferential`,
  `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`, and presentation-basis
  declarations. None asserts this smooth-curve statement for every uniformizer.
- `msearch.py ... loogle "KaehlerDifferential, IsDiscreteValuationRing"`: zero hits.
- `msearch.py ... grep "uniformi[sz]er.*(differential|Kaehler)|differential.*uniformi[sz]er|basis.*Kaehler"`:
  thirteen hits on general smooth presentations, cotangent bases, and polynomial
  differentials; no matching statement.
- `rg` of the upstream `WeilConjectures` and shared `lean/Sheaf` for uniformizer/differential
  combinations and the proposed declaration name: no matching declaration. The only
  relevant shared occurrence is the proof docstring of `Curve/FiniteMapAffineLine.lean`,
  which cites this node and does not state it.
- Search of upstream `WeilConjectures` for the exact node id, and of
  `dag/lean_names_upstream.json`: no existing attachment.

Validation: `scompile.py Q132 lem-a1-uniformizer-differential-basis <module>` succeeded for
both its sandbox and library-module checks (2.8 seconds each), with no compiler warning
or error. Every line is at most 100 characters. No auto-bound variables or universes,
local notation, local instances, hollow definitions, or auxiliary postponed theorems occur.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
