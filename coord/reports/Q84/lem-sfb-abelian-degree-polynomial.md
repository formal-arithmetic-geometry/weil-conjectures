## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.DegreePolynomial` states
`AlgebraicGeometry.IsAbelianVariety.exists_degree_polynomial`, with its one proof
left `sorry`. No new definition, dependency module, or statement correction is needed.
The only node field changed is `lean`. The source read was Milne, Abelian Varieties,
Chapter I, the degree convention before Theorem 10.9 (printed p.46), Remark 10.11
and Proposition 10.13 with its proof (printed pp.47–48). The theorem docstring carries
all seven proof steps of the accepted node, including the common-denominator argument,
two-sided cube recurrence, uniform line-degree bound and homogeneous coefficient comparison.

Hypotheses and objects, clause by clause:

- A field k is `{k : Type u} [Field k]`, with an explicitly bound universe `u`.
- The k-abelian variety is `A : Over (Spec (.of k))`, `[GrpObj A]`,
  `[IsAbelianVariety A]`. This is precisely the recorded group-scheme and
  abelian-variety interface, with no algebraic-closure or characteristic hypothesis.
- Its positive dimension g is `hg : 0 < IsAbelianVariety.dim A`.
  The recorded `IsAbelianVariety.topologicalKrullDim_eq` identifies this natural number
  with its topological Krull dimension; consequently the degree is `2 * IsAbelianVariety.dim A`.
- E is `Additive (Grp.mk A ⟶ Grp.mk A)`. The existing category `Grp` bundles
  precisely the k-morphisms with `IsMonHom`; it is not the set of all scheme maps.
  `a.toMul.hom.hom` is the underlying k-group-scheme endomorphism. Mathlib's
  `Grp.Hom.hom_mul` identifies multiplication on this Hom with pointwise
  multiplication in A. `Additive` therefore gives pointwise addition, as requested.
  The `CommGroup` needed here follows from the existing commutative group-object
  structure on `Grp.mk A` and `IsAbelianVariety.isCommMonObj A`; no extra hypothesis
  or choice of an unrelated additive group has been introduced.
- E^0 is represented by `ℚ ⊗[ℤ] E`. The canonical symmetry
  `TensorProduct.comm ℤ E ℚ` identifies the node's `E ⊗[ℤ] ℚ` with this same
  rationalization, sending `a ⊗ 1` to `1 ⊗ a`. Putting ℚ first exposes Mathlib's
  existing rational scalar action. This is a canonical change of presentation,
  without a restriction on E and without an alternative definition.
- The convention for d is stated as the first conjunct: for every a,
  `IsIsogeny a.toMul.hom.hom → d a = (isogenyDegree a.toMul.hom.hom : ℚ)` and
  `¬ IsIsogeny a.toMul.hom.hom → d a = 0`. These two implications determine d
  pointwise. Existentially bundling this uniquely prescribed function with d0
  avoids introducing a second global degree definition. It does not assume an
  arbitrary degree function or change the required convention.
- The well-defined rational extension is one function
  `d0 : ℚ ⊗[ℤ] E → ℚ`, quantified before every subspace and basis.
- Agreement on integral endomorphisms is the next conjunct
  `∀ a, d0 (1 ⊗ₜ[ℤ] a) = d a`.
- The full denominator rule is the third conjunct: for every v, every natural n
  with `0 < n`, and every a with `n • v = 1 ⊗ₜ[ℤ] a`,
  `d0 v = ((n : ℚ) ^ (2 * IsAbelianVariety.dim A))⁻¹ * d a`.
  Positive integers are represented by their equivalent positive naturals.
  Here n-smul is multiplication by n in the rational vector space.
- An arbitrary finite rational subspace is
  `V : Submodule ℚ (ℚ ⊗[ℤ] E)` with `[FiniteDimensional ℚ V]`.
  Every ordered basis is quantified as `(r : ℕ) (e : Module.Basis (Fin r) ℚ V)`.
  `Fin r` is the ordered list of r basis positions, with 0-based indexing.
- The polynomial is `P : MvPolynomial (Fin r) ℚ`, with
  `P.IsHomogeneous (2 * IsAbelianVariety.dim A)`. The recorded Mathlib notion
  says every monomial in the support has this total degree, so it allows P = 0.
  We deliberately do not assert a nonzero leading term or `P.totalDegree = 2g`.
- Polynomial evaluation for all coordinates is
  `∀ x : Fin r → ℚ, d0 (V.subtype (∑ i : Fin r, x i • e i)) = MvPolynomial.eval x P`.
  The subtype inclusion puts the actual linear combination in E^0.
- The node's explicit zero-value clause is included in the same polynomial witness:
  `MvPolynomial.eval (0 : Fin r → ℚ) P = 0`.
- Finally for every a that is an isogeny, the last conjunct gives
  `d0 (1 ⊗ₜ[ℤ] a) = (isogenyDegree a.toMul.hom.hom : ℚ)` and
  `0 < isogenyDegree a.toMul.hom.hom`. The degree is already ℕ by the recorded
  kernel-order definition, so its positivity gives precisely a positive integer.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, the nontrivial commutative field class.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, `IsAbelianVariety.dim` and
  `IsAbelianVariety.topologicalKrullDim_eq`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic`:
  `IsAbelianVariety.isCommMonObj`, and the recorded
  `IsAbelianVariety.geometricallyIntegral` and `IsAbelianVariety.irreducibleSpace`.
- `Mathlib.CategoryTheory.Monoidal.Grp` and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj`, `Grp`, `Grp.mk`,
  `Grp.homMk`, `Grp.Hom.hom_mul`, the internal commutative group structure on
  `Grp.mk A` and `CategoryTheory.Hom.commGroup`. These implement def-sc-group-scheme.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsIsogeny` (surjectivity, `IsMonHom`, finite kernel), `isogenyDegree`
  (natural finrank of the kernel's coordinate algebra).
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`:
  `TensorProduct`, `TensorProduct.tmul`, its module action, universal map `lift`.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`, i.e.
  `Module.Finite`. `Module.Basis` is Mathlib's existing basis of the submodule.
- `Mathlib.Algebra.MvPolynomial.Basic`, `.Eval` and
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial`, `aeval`,
  `algHom_ext`, `eval`, `IsHomogeneous`. These are the recorded polynomial ring
  with its evaluation and the usual homogeneous-support convention.

All presently recorded proof dependencies are imported as plain, non-public imports
unless already public for the statement: `AbelianVariety.Projective`
(`IsAbelianVariety.exists_isAmple`), `Modules.VeryAmple` (`IsAmple.tensorObj`),
`AbelianVariety.Basic` (geometric integrality), `IntersectionNumber`
(`Scheme.Modules.intersectionNumber`, `selfIntersectionNumber`), `Modules.Ample`
(`Scheme.Hom.degree`, `degree_pos_of_isAmple_of_nonempty`),
`TopIntersectionPullback` (`Scheme.Modules.selfIntersectionNumber_tensorPullback`),
`AbelianVariety.Isogeny` (`IsIsogeny.isFinite`, `IsIsogeny.flat`, `IsIsogeny.finrank_eq`),
`AbelianVariety.Cube` (`nonempty_iso_overPullback_npow_id`, `nonempty_iso_cube`),
`Mathlib.RingTheory.Localization.BaseChange` (`IsLocalization.tensorProduct_isLocalizedModule`),
and `Modules.Invertible` (`Scheme.Modules.IsInvertible`).
The still-unstated proof nodes `lem-sfb-equal-dimension-isogeny-criterion`,
`lem-sfb-top-intersection-multilinear` and `lem-sfb-bounded-line-polynomial-interpolation`
have no Lean module recorded on the base, so there is no module to import for them.
They are proof dependencies only; no missing statement object is assumed or redefined.

Edge cases checked before writing:

- Positive dimension excludes the zero-dimensional abelian variety, just as the node does.
  No unrelated nonemptiness or characteristic assumption is added.
- V = 0 and r = 0 are included. The empty sum is zero; a positive-degree homogeneous
  polynomial with no variables is the zero polynomial. `MvPolynomial.isHomogeneous_zero`
  confirms that the exact convention permits it.
- A subspace consisting of nonisogenies may have zero polynomial. Homogeneity is stated
  using `IsHomogeneous`, never exact total degree or nonzeroness.
- At the zero endomorphism the first clause prescribes d = 0 (g > 0); the denominator
  clause still covers a = 0 and arbitrary positive denominators.
- n = 1 gives the integral-value clause; n = 0 is intentionally excluded. The
  denominator formula is universally quantified over all representations, so their
  independence is asserted without assuming E torsion-free or finitely generated.
- The identity is an isogeny of degree 1. In positive characteristic, inseparable
  isogenies remain covered because `isogenyDegree` counts kernel scheme order,
  not the number of geometric kernel points.
- Any base field and universe u are allowed. E lives in the Hom universe of schemes
  over k; the rational tensor remains at that universe. Finite bases use `Fin r`.

Searches actually run on 2026-10-24:

- msearch LeanFinder: “The degree of an abelian variety endomorphism extends to a
  homogeneous polynomial on finite rational subspaces of its rational endomorphism
  algebra”. Eight hits, all elliptic division-polynomial degree results, beginning
  `WeierstrassCurve.natDegree_Φ`, `natDegree_Φ_le`, `natDegree_preΨ'`; no exact theorem.
- msearch Loogle: `"IsAbelianVariety", "degree"`. Zero hits.
- msearch Mathlib grep, AlgebraicGeometry:
  `degree.*endomorph|endomorph.*degree|degreePolynomial`. Zero hits.
- msearch LeanSearch: “Isogeny degree on rational endomorphisms of an abelian variety
  is a homogeneous polynomial of degree twice its dimension”. Eight hits, including
  `MvPolynomial.IsHomogeneous`, `LinearMap.toMvPolynomial_isHomogeneous`, homogeneous
  components and characteristic-polynomial homogeneity; none states the degree theorem.
  `MvPolynomial.IsHomogeneous` was used after reading its actual definition.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `degreePolynomial|degree_polynomial|degree.*endomorph|endomorph.*degree` found only
  unrelated derived/linear and elliptic material, no degree-polynomial theorem for AVs.
- Node-id search in both source roots and name search in `dag/lean_names_upstream.json`
  found no existing statement for this item. The instructed compact-object example
  currently contains only a withdrawal notice, so the active module-mode conventions
  in brief-stage2 §4 were followed.
- API searches in the group-object modules found `Grp.Hom.hom_mul` and
  `CategoryTheory.Hom.commGroup`; these avoided introducing any helper definition.

Validation: `scompile.py Q84 lem-sfb-abelian-degree-polynomial` compiled the delivered
file in both sandbox and library module modes against the live published build, cleanly
(2.5 s and 2.3 s). Only this module was compiled. No tests or proofs were added.
No disputed statement or node fault was found. The rationalization symmetry and the
existential packaging of the uniquely prescribed d are equivalent presentations of
exactly the node's objects and clauses, not a statement correction.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
