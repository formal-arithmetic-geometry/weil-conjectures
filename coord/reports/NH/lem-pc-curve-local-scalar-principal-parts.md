## Worker report

The module `Sheaf.AlgebraicGeometry.CurveLocalScalarPrincipalParts` states
`AlgebraicGeometry.CurveLocalScalar.principal_parts`, with its sole proof `sorry`.
Its two public abbreviations `projection` and `Points` are real definitions of the projection
and the actual subtype of points above x. These helpers belong to this node's own notion;
there is no new independent notion, dependency module, statement correction or disputed claim.
The ten proof steps, their sources and their dependency IDs are in the theorem docstring.

Hypotheses and objects, checked against the complete node statement:

- The two fields and extension are `(k K : Type u) [Field k] [Field K] [Algebra k K]`.
  The common arbitrary universe accommodates the scheme and both fields, including fields
  originally presented in different universes by choosing their common ambient universe.
- The scheme over k is `C` with `[C.Over (Spec (.of k))]`. Smoothness, projectivity,
  integrality and dimension one are precisely `IsSmoothProjectiveCurve (C ↘ Spec (.of k))`;
  geometric connectedness is `GeometricallyConnected` of that same structure map. No
  geometric-integrality hypothesis has been substituted for geometric connectedness.
- `C.baseChangeField k K` is literally the canonical scheme fibre product, with `projection`
  the existing `pullback.fst`. The point x has hypothesis `hx : IsClosed ({x} : Set C)`.
  `Points k K C x` is exactly the subtype where this projection equals x, without a prior
  closedness restriction on its members.
- F and L are the existing `Scheme.functionField` (the generic stalk, as the integral clause
  of def-sc-function-field specifies). The k-algebra on F is a parameter together with
  `Scheme.IsFunctionFieldAlgebra k C`; this fixes its structure map on every scalar.
  After obtaining integrality of the base change, the theorem universally quantifies over
  the analogous compatible K-algebra on L. These are canonical structure identifications,
  not additional mathematical assumptions: the existing `Scheme.functionFieldAlgebra` and
  `isFunctionFieldAlgebra_functionFieldAlgebra` always provide them.
- O and O_y are the existing `Scheme.localSubalgebra`, identified with the actual stalks
  by the existing `Scheme.stalkEquivLocalSubalgebra`. Its residue-field comparison
  `Scheme.residueFieldLocalSubalgebraEquiv` identifies the residue fields used here with
  `Scheme.residueField` and respects the base field. No new local-ring definition is made.
  Scalar tensors are written `K ⊗[k] -`; applying Mathlib's canonical tensor commutor
  identifies them with the node's `- ⊗[k] K`, including on each pure tensor.

Conclusion, clause by clause:

- `IsIntegral C ∧ ∃ (_ : IsIntegral (C.baseChangeField k K)), ...` asserts both integrality
  clauses, with the base-change integral instance made available before forming L.
- `IsDiscreteValuationRing` is asserted for O, O_y and their actual stalk presentations.
  `FiniteDimensional k (IsLocalRing.ResidueField O)` and its K analogue for every O_y
  give the two residue-field finiteness clauses using the canonical comparisons above.
- `Finite (Points ...) ∧ Nonempty (Points ...)` asserts finiteness and nonemptiness;
  `∀ y, IsClosed ({y.1} : Set ...)` asserts closedness in the whole base-change curve.
- `eS` identifies this exact point subtype with the prime spectrum of the unreduced
  `K ⊗[k] IsLocalRing.ResidueField O`. For each y, the ring homomorphism `r y` is fixed
  by equality in L with the image of O under rho. The map `s y` on residue tensors is
  specified by `c ⊗ residue(a) ↦ c * residue(r y a)`. Finally
  `(eS y).asIdeal = RingHom.ker (s y)` fixes the canonical point correspondence, rather
  than asserting only the existence of a bijection between finite sets.
- The ring homomorphism `rho : F →+* L` is fixed by the commuting diagram of the actual
  generic-point morphisms and the scalar projection. The K-algebra map `i` satisfies
  `i (c ⊗ f) = c • rho f`; `Function.Injective i` is precisely injectivity of V → L.
- `j (c ⊗ a) = i (c ⊗ (a : F))` fixes the map on O's scalar extension. The equalities
  `A = j.range`, `V = i.range` identify A and V as subalgebras inside L. The equivalence
  `jA : K ⊗[k] O ≃ₐ[K] A`, fixed by `(jA z : L) = j z`, also asserts the required
  injectivity of the map on A. `B = ⨅ y, Scheme.localSubalgebra K ... y.1` is the actual
  intersection inside L. `A ≤ V`, `A ≤ B` record the inclusions, and `V ⊓ B = A` the
  intersection equality.
- Uniformizers are exactly `maximalIdeal O = Ideal.span {t}`. There is no restriction on
  the choice of uniformizer. For every such t, the two denominator formulas quantify over
  every v in V and every f in L, with arbitrary natural exponent m. They state respectively
  `v * j(1 ⊗ t)^m ∈ A` and `f * j(1 ⊗ t)^m ∈ B`, hence exactly V=A[1/t] and L=B[1/t]
  inside L; the reverse inclusions follow from A⊆V and the nonzero parameter in the fields.
- For every n with `1 ≤ n`, the three K-algebra equivalences e0, e1 and e2 have exactly
  the four quotient algebras of the node as source and target. The representatives tA, tB
  and ty are fixed by jA and the inclusion maps ab and bo. Those inclusion maps are in turn
  fixed by their equality as elements of L. The formula for e0 on `c ⊗ mk a` fixes the
  tensor/quotient map; e1 on `mk a` fixes the inclusion A→B; e2 on `mk b` at every y fixes
  the product of local quotient maps. Four `FiniteDimensional K` assertions state the
  finiteness of all four displayed algebras. Each quotient is `Ideal.span {parameter^n}`;
  there is no radical, reduced quotient or reduced fibre in the statement.
- `eVA` is the K-linear equivalence V/A→L/B. Its source uses the comap of A's submodule
  along V's inclusion into L, so it is literally V modulo the included A. The representative
  equation `eVA (mk v) = mk (v : L)` fixes the inclusion-induced map.
- `eLB` is the K-linear equivalence L/B→the dependent direct sum of L/O_y, using `Π₀`.
  For every f and y its value is `mk f`, specifying the diagonal-induced map. The actual
  direct sum is used even though the point subtype is proved finite.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsSmoothProjectiveCurve` and its inherited `IsIntegralCurve`/`IsVariety`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and `.Connected`:
  `GeometricallyIntegral` (read the recorded dependency) and `GeometricallyConnected`
  (the clause needed here), both the existing base-change predicates.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `Field` on k and K.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded convention uses
  `Limits.pullback`, `pullback.fst` and `pullback.snd`; `Scheme.baseChangeField` from
  `WeilConjectures.AlgebraicGeometry.BaseChangeField` supplies this exact specialization.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: read
  `Scheme.functionFieldOfComponents` and its documentation; its explicitly documented
  integral-scheme clause uses Mathlib `Scheme.functionField`, as this statement does.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `irreducible_iff_uniformizer`; the maximal-ideal generator formulation is used literally.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`; their canonical local-subalgebra comparison is the existing
  `Scheme.residueFieldLocalSubalgebraEquiv` in
  `WeilConjectures.AlgebraicGeometry.Curve.AdelicLocal`.
- The additional existing local-subalgebra, compatible-field and generic-point APIs are
  `Scheme.localSubalgebra`, `Scheme.stalkEquivLocalSubalgebra`,
  `Scheme.IsFunctionFieldAlgebra`, `Scheme.functionFieldAlgebra`, and
  `Scheme.fromSpecFunctionField`, imported through the AdelicLocal module. All are reused.
- Available modules of the proof dependencies are imported non-publicly: properness,
  relative dimension, closed-point fields and dimensions, regular local rings, affine
  stalks and fibre products, finite algebra spectra, the product of localizations, and
  localization/tensor comparison. Proofs remain postponed throughout this delivery.

Searches actually run:

- msearch leanfinder, `Scalar extension of principal parts at closed points of a smooth curve
  and semilocal rings`: eight hits, including WeierstrassCurve.Affine.FunctionField,
  WeierstrassCurve.reduction, and Algebra.smoothLocus; no exact theorem.
- msearch loogle, `IsLocalization, TensorProduct`: twelve hits, including
  IsLocalization.tensorRight, .tensor, .algebraTensorEquiv and .moduleTensorEquiv;
  these are ingredients, not the curve/principal-parts statement.
- msearch grep, `principalParts|principal_parts|semilocal`: eleven Mathlib hits, mostly
  LocalProperties/Semilocal and Localization/Finiteness; no exact theorem.
- msearch leansearch, `canonical algebra structure on the stalk of a scheme over Spec of a
  field`: eight hits including StructureSheaf.stalkAlgebra, stalkFunctionFieldAlgebra and
  TopCat.Presheaf.algebra_section_stalk; these led to reading the canonical stalk APIs.
- rg over WeilConjectures and Sheaf for `principalParts|principal_parts|semilocal`,
  `stalkFunctionField|functionFieldAlgebra`, then `localSubalgebra|IsFunctionFieldAlgebra`:
  found the existing AdelicStructureSheaf/AdelicLocal/ResidueSequence definitions and
  TateResidue.principalParts. Those notions are reused; no existing scalar-extension
  theorem matches this node. The literal node-ID search in WeilConjectures found nothing.
- DAG search for localSubalgebra/IsFunctionFieldAlgebra found only the vector-bundle
  principal-parts consumer; blueprint_refs search `local subalgebra` gave zero matches.
  No new definition node was needed.

Edge cases checked before writing: K=k gives the single original point and the usual
local principal-parts quotient. For k=F_p(s), x defined by z^p-s, and K adjoining s^(1/p),
the fibre is K[ε]/(ε^p), and t has valuation p above x; all ideal quotients in this statement
retain that nilpotence. A transcendental K is allowed; A is never assumed semilocal.
The point set is proved nonempty, not assumed a priori. The zero principal part and all
n≥1 are included; n=0 has no claim because the node explicitly requires n≥1.
No algebraic-closedness, separability, finite extension or characteristic restriction is added.

Validation: the complete module compiled through scompile.py in both sandbox and intended
library-module modes in 10.1 and 9.1 seconds, with no errors or warnings. Only the allowed
sorry proof remains. Final delivery preflight and compile are recorded by deliver2.py.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
