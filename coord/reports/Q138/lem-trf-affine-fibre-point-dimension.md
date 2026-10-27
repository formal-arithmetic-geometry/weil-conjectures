## Worker report

Module: `Sheaf.AlgebraicGeometry.AffineFibrePointDimension`.
Declaration: `AlgebraicGeometry.affine_fibre_point_dimension`, with proof `sorry`.
No new definition, dependency repair, or statement correction is needed. The original
node statement is preserved. Its seven proof steps are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- The schemes, morphism, and point are `X S : Scheme.{u}`, `f : X ⟶ S`, and `x : X`.
  The image point `s` is written directly as `f x` throughout.
- The affine neighbourhoods `W = Spec A` and `V = Spec R` are the open immersions
  `iW : Spec (CommRingCat.of A) ⟶ X` and `iV : Spec (CommRingCat.of R) ⟶ S`.
  Their ranges are precisely the underlying open subsets W and V; no affine
  coordinate ring is replaced by unrelated data. The rings are arbitrary commutative
  rings in the scheme universe, with `Algebra R A` specifying the coordinate map φ.
- The condition that the coordinate map is induced by f, including `f(W) ⊆ V`, is
  `hφ : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV = iW ≫ f`.
  This is the commutative square expressing the restriction of f to the chosen charts.
  Every pair of affine neighbourhoods in the node has exactly this square.
- Finite presentation is `[Algebra.FinitePresentation R A]`.
- The corresponding primes are `q : PrimeSpectrum A` and `p : PrimeSpectrum R`;
  their identifications with the specified points are `hx : iW q = x` and
  `hs : iV p = f x`. Their contraction relation is
  `hp : p.asIdeal = q.asIdeal.comap (algebraMap R A)`.
- The field k is Mathlib's `p.asIdeal.ResidueField`, the residue field of
  `Localization.AtPrime p.asIdeal`. Its canonical identification with κ(s) is `e`,
  with `e.hom` explicitly identified with the residue-field map of the base chart,
  the equality transport `S.residueFieldCongr hs`, and `Scheme.Spec.residueFieldIso`.
  This fixes the identification, rather than quantifying an arbitrary field isomorphism.
- The fibre algebra F is Mathlib's `p.asIdeal.Fiber A`, definitionally
  `p.asIdeal.ResidueField ⊗[R] A`. Its k-algebra structure is the standard left factor.
- The evaluation homomorphism is `ψ`, whose value on every pure tensor is explicitly
  `Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) hp l *
  algebraMap A q.asIdeal.ResidueField a`. The first factor is exactly the field
  homomorphism induced by φ. Pure tensors generate F, so this equation determines ψ.
- The prime Q is `Q : PrimeSpectrum (p.asIdeal.Fiber A)` with
  `Q.asIdeal = RingHom.ker ψ`. Its contraction under `a ↦ 1 ⊗ a` is the displayed
  equality with `q.asIdeal`, using `Algebra.TensorProduct.includeRight`.
- The canonical chart map is `j : Spec (CommRingCat.of F) ⟶ f.fiber (f x)`.
  The theorem states `IsOpenImmersion j`. Both projection equations specify j:
  the first is `Spec.map includeRight ≫ iW`, and the second is Spec of the
  composite from κ(s) through `e.hom` to k and then into F. Since the target is
  the pullback defining the scheme fibre, these two equations uniquely specify j.
  Thus the existential formulation asserts the existence and properties of the
  canonical morphism, not properties of an unconstrained substitute.
- Its image is exactly the inverse image of W:
  `Set.range j = (f.fiberι (f x)) ⁻¹' Set.range iW`.
- The identification of the point above x is `j Q = f.asFiber x`.
  Mathlib's `asFiber` uses `f.fiberHomeo`, giving the unique fibre point over x.
- Finite type over k uses the recorded ring-map predicate:
  `RingHom.FiniteType (algebraMap p.asIdeal.ResidueField F)`.
- Equality of dimensions is
  `topologicalKrullDimAt Q = topologicalKrullDimAt (f.asFiber x)`.
  Finiteness and nonnegativity are `∃ d : ℕ, topologicalKrullDimAt Q =
  (d : WithBot ℕ∞)`. Together these assert the same finite natural value on both sides.
- The final universal quantification is over every `n m : ℕ` and
  `P : Algebra.Presentation R A (Fin n) (Fin m)`. The conclusion supplies a
  k-algebra equivalence from the polynomial quotient by the span of the coefficientwise
  images of `P.relation` to F. The equation on every `MvPolynomial.X a` sends the
  variable class to `1 ⊗ₜ[R] P.val a`. This is exactly the induced presentation,
  including its generator identifications, for any finite presentation of A.

Dependency declarations used, with sources read in full at their declarations:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (with the standard k-algebra map).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.mk`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`; `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`:
  `Ideal.Fiber`. These supply the localization, fields and tensor fibre, without copies.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`, `Scheme.Spec.residueFieldIso`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, `asFiber`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt` and
  proof dependency `IsOpen.topologicalKrullDimAt_eq`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`;
  `Mathlib.Algebra.MvPolynomial.Eval`: evaluation underlying presentations;
  `Mathlib.RingTheory.Extension.Presentation.Basic`: `Algebra.Presentation`,
  `Algebra.Presentation.baseChange` (the recorded presentation-base-change dependency).
- Proof imports: `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`
  (`spec_field_point_residue_field` and its affine-open/map variants),
  `WeilConjectures.RingTheory.DimensionAtPointComponents` (`dimension_at_point_components`),
  `Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`,
  `Scheme.pullback_map_isOpenImmersion`), `Mathlib.RingTheory.TensorProduct.Maps`
  (`Algebra.TensorProduct.productMap`), and `Mathlib.Topology.KrullDimension`
  (`IsHomeomorph.topologicalKrullDim_eq`). The residue-field naturality dependency
  is `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` in ResidueField;
  tensor inclusions and their universal-property uniqueness are in TensorProduct.Basic.
  The modules for statement and proof dependencies are imported directly or through
  their public dependency imports; all project proof modules are imported plainly.

Edge cases checked before writing:

- Empty schemes or empty chart spectra admit no chosen x/q with hx, so no impossible
  nonempty hypothesis has been silently assumed. For the actual marked chart, q
  ensures it is nonempty and the evaluation prime ensures F is nonzero.
- Zero rings are allowed by the commutative-ring binders; they cannot possess the
  specified prime q or p. No extra domain, Noetherian, or field assumption is added.
- No flatness, smoothness, or perfectness is imposed. Tensor base change of a
  presentation works even when R → k is not flat.
- `n = 0`, `m = 0`, and redundant generators/relations are included by `Fin n`,
  `Fin m`; the empty relation span is the zero ideal. The variable equation is
  vacuous for n = 0, with the k-algebra condition fixing the coefficients.
- Arbitrary characteristic and arbitrary primes, including generic/nonclosed primes,
  are included. Point dimension is the neighbourhood dimension `topologicalKrullDimAt`,
  not the dimension of the local ring. The natural-number witness allows dimension 0.
- The single explicit universe u is the universe of the schemes and their chart rings;
  it can be instantiated at any size. There is no quantified test category/algebra in
  a smaller independent universe. `autoImplicit` is disabled.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query: “An affine open chart in a scheme fibre is the
  spectrum of the residue field tensor algebra with point given by kernel of evaluation
  and finite dimension at that point”. Eight hits, headed by `fiberOverSpecResidueField`,
  `fiberToSpecResidueField`, and `fiberToSpecResidueField_apply`. These only provide
  individual fibre constructions, not the combined chart, kernel, dimension and
  arbitrary-presentation statement.
- `msearch.py ... loogle`, query: `AlgebraicGeometry.Scheme.Hom.fiber,
  topologicalKrullDimAt`. Zero hits; the service reports `topologicalKrullDimAt` unknown
  because that definition is in the project, not Mathlib.
- `msearch.py ... grep`, query `affine.*fiber|fiber.*[Dd]imension|
  fiberOverSpecResidueField`, Mathlib subdirectory `AlgebraicGeometry`: six hits in
  Fiber.lean and Morphisms/QuasiFinite.lean, providing the underlying fibre interfaces.
- `rg -n 'affine.*[Ff]ibre|affine.*[Ff]iber|affine_fibre_point|
  lem-trf-affine-fibre-point-dimension' lean/WeilConjectures lean/Sheaf` finds related
  affine/fibre statements and a consumer docstring, but no theorem with these clauses.
  `grep -rn 'lem-trf-affine-fibre-point-dimension' lean/WeilConjectures` gives no hits.
  Exact-name search for `affine_fibre_point_dimension` in both Lean roots and
  `dag/lean_names_upstream.json` gives no hits.

Sources checked: Schemes Tags 01JQ and 01JR and Morphisms Tag 01V9, with Algebra's
base-change presentation formula after 05G4 and point-dimension lemma 00OT, read from
`literature/stacks-project/`. No statement dispute or node fault found.

Validation: required `scompile.py` compiled the sandbox and library module cleanly.
The initial probe exposed a reversed composition in the base projection; this was
corrected to the ring map κ(s) → k → F before the clean compile.

## Second reading by Q138

This dispatcher assignment prohibits starting another agent and delegates independent
review to the maintainer. This section records the worker's own second clause check;
it does not claim an independent reader. Re-read the original node and the complete
module: the affine opens are encoded by open immersions with hφ, the primes by hx/hs/hp,
canonical maps by the residue identification and both projections/pure-tensor formula,
and every conclusion by the conjunctions listed above. Checked especially the direction
of e and contravariance of Spec: `e.hom` goes from κ(s) to k and is followed by the
left tensor inclusion. Checked that the presentation equivalence is over k and sends
each variable to its prescribed tensor. No clause was removed or corrected in the node.
