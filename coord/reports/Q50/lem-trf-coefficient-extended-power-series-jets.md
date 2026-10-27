## Worker report

The module `Sheaf.RingTheory.CoefficientExtendedPowerSeriesJets` states
`MvPowerSeries.CoefficientExtendedJets.coefficient_extended_power_series_jets`.
Its proof is exactly `sorry`. All other declarations have real data and spell out
objects or maps belonging to this comparison; there are no postponed helper proofs,
new nodes, dependency repairs, or changes to the natural-language statement.

Hypotheses and objects, clause by clause:

- `K : Type u`, `L : Type v`, `[Field K]`, `[Field L]`, `[Algebra K L]`
  specify arbitrary fields and the specified coefficient inclusion. A unital map
  from a field to a field is injective; no extra finiteness, algebraicity, or
  characteristic assumption is imposed. The universes are independent.
- `e s : ℕ` include zero. `MvPowerSeries (Fin e) K` is `R`; the variables of
  `L[[X,T]]` are labelled by `Fin e ⊕ Fin s`, canonically the same finite set
  as `Fin (e+s)`, preserving which variables are `X` and which are `T`.
- `I : Ideal (MvPowerSeries (Fin e) K)` is arbitrary, subject exactly to `hI`,
  the inequality with `Ideal.span (Set.range MvPowerSeries.X)`.
- `sourceRing` is `C = R/I`; `targetRing` is `D`, quotienting by the algebraic
  ideal image under `coefficientMap`. That map is Mathlib's coefficient `map`
  followed by `rename Sum.inl`. `quotientMap` is the actual induced `j`, built
  with `Ideal.quotientMap` and its standard `Ideal.le_comap_map` certificate.
- `sourceIdeal` and `targetIdeal` are the images of the corresponding variable
  ideals, hence exactly `a` and `b`. `sourceJet m` and `targetJet N` quotient
  by their powers. In particular the source zero jet is the quotient by `a^0`.
- `β : Fin s →₀ ℕ` is the exponent vector; `β.degree` is its sum of entries.
  `coefficients N` is the dependent direct sum over `{β // β.degree < N}` of
  `L ⊗[K] sourceJet (N - β.degree)`.
- The existential family `φ N hN` for every `N` with `0 < N` is an `L`-linear
  equivalence from `targetJet N` to that direct sum, with precisely the
  orientation and cutoff of the node.
- The first conjunct evaluates `φ` on every series representative `F` as
  `coefficientVector N F`. That vector sums over the finite support of
  `MvPowerSeries.truncTotal N F`. Each total exponent is split by the standard
  `Finsupp.comapDomain.addMonoidHom` into `xExponent` and `tExponent`; its scalar
  coefficient is tensored with the class of its `X` monomial. Grouping terms
  with a common `T` exponent is addition inside that direct-sum component.
  Thus this is coefficient extraction modulo `I + (X)^(N-|β|)`, without
  choosing an infinite expansion into tensors. The conditional outside the
  truncated `T` cutoff is zero.
- The second conjunct specifies the inverse on every homogeneous coefficient
  generator `coefficientTerm`: `l ⊗ [c]` in summand `β` maps to the jet class
  of `l • (j(c) * tMonomial β)`. Here `tMonomial` is the quotient class of the
  series monomial with exponent `Finsupp.mapDomain Sum.inr β`. This also fixes
  the map on arbitrary classes of `C`, rather than just on base scalars.
- The third conjunct applies the actual jet quotient reduction from `N+1`
  to `N`. On a generator of degree below `N`, it returns `coefficientTerm N`
  with the same representative, which is precisely reduction of its
  coefficient to `C/a^(N-|β|)`. When its degree equals `N`, it returns zero.
  These generators span the direct sum, so the formula specifies the full
  transition map, including deletion of the top `T` degree.
- The fourth conjunct specifies multiplication on every pair of coefficient
  generators. It multiplies `l*m` and `c*d`, adds `β+γ`, and returns zero
  when the sum has degree at least `N`. By bilinearity and finite support this
  is exactly the coefficient convolution formula on all elements. The formula
  takes place in the actual ring `D/b^N`, so it also asserts descent through
  all quotient relations.
- Finally `ψ` is an `L`-algebra equivalence from the polynomial ring over
  `L ⊗[K] gr_a C` to `gr_b D`. `gradedBaseAlgebra` supplies the ordinary
  degree-zero scalar action by composing `Ideal.associatedGradedRingHom`
  with `algebraMap`. `gradedCoefficients` and `gradedTensor` specify this
  action explicitly in the tensor's module argument; this prevents Lean from
  using an unrelated restriction-of-scalars instance. They do not introduce
  a new associated graded ring or a different tensor product.
- For every `d`, `c : a^d`, `β`, and `l`, the final formula gives a
  representative `y : b^(d+|β|)` with underlying value exactly
  `l • (j(c.val) * T^β)` and equates its homogeneous class with the image
  of the polynomial monomial whose coefficient is `l ⊗ [c]` in degree `d`.
  The specified degree proves gradedness for the grading with `T` degree one.
  Taking `β=0` uses `MvPolynomial.monomial 0 = MvPolynomial.C` and `T^0=1`,
  giving precisely the actual map `j` on the constant-polynomial part.
  No choice of a free algebra map, or of an arbitrary graded identification,
  occurs in the conclusion.

Dependency declarations read and used:

- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`; addition and Cauchy multiplication,
  `C`, `X`, `monomial`, `map`, and the coefficient algebra structure. The
  additional `Rename` and `Trunc` modules supply `rename` and `truncTotal`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, and `LinearMap.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  The statement uses their tensor product and pure tensors. The public
  `Mathlib.RingTheory.TensorProduct.Basic` import supplies the standard
  coefficient algebra tensor structure as well.
- `def-weil-pbc-direct-sum-modules`: `DirectSum`, `DirectSum.of`,
  `DirectSum.lof`, and `DirectSum.component` in
  `Mathlib.Algebra.DirectSum.Basic` and `.Module`. The direct sum and its
  canonical inclusions appear explicitly in the signatures.
- `def-weil-pbc-associated-graded-ring`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`, their actual
  commutative ring instances, `Ideal.associatedGradedRingHom`, and
  `Ideal.associatedGradedAlgebra` in
  `WeilConjectures.RingTheory.AssociatedGradedRing`. Read the full module.
  Its ring structure is also the recorded proof dependency
  `lem-weil-pbc-associated-graded-ring-structure`; there is only one import.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `MvPolynomial.aeval`, and `MvPolynomial.algHom_ext` in
  `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`. The polynomial ring
  and its monomials appear explicitly in the comparison.
- Proof imports are `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`
  (`power_series_mem_combined_ideal_pow_iff`),
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
  (`lTensor_exact`, `rTensor_exact`),
  `Mathlib.RingTheory.Flat.Basic` (`Module.Flat.lTensor_exact`,
  `Module.Flat.rTensor_exact`, `Module.Flat.of_free`), and
  `Mathlib.LinearAlgebra.Basis.VectorSpace` (`Module.Free.of_divisionRing`).
  No proof dependency module was omitted for an import cycle.

Source reading: the whole node's nine-step proof was read, together with the
recorded dependencies and their declaration interfaces. The actual local Stacks
Algebra statements `lemma-tensor-product-exact` (Tag 00DF) and `lemma-flat`
(Tag 00HD) were read. They provide the exactness inputs, not the jet comparison
itself. The current blueprint's ancestor `lem-trf-local-term-locality` was read;
this is a supporting algebra lemma, not that unit's own statement.

Edge cases checked mathematically before writing and again against the signature:
`e=0` forces `I=0` and yields truncated `L[[T]]`; `s=0` leaves only exponent
zero and gives ordinary scalar extension of finite jets; `e=s=0` gives `K`
and `L` in degree zero. `I=0`, `N=1`, degree `d=0`, and `β=0` are included.
The reduction boundary `|β|=N` is deleted explicitly. Characteristic is unrestricted.
No finite-dimensionality assumption on `L/K` occurs; tensors are formed only with
finite jets and all coefficient-vector sums are finite. No unbound universes or
variables, file-local notation, local instances, arbitrary equivalence hypotheses,
or hollow data are present. No STATEMENT-DISPUTED issue was found.

Searches (all before creating the comparison; no exact existing statement found):

- `msearch.py leanfinder`, query “finite jets and associated graded algebra of
  power series quotients after coefficient field extension and adding variables”:
  eight hits on Weierstrass quotient equivalences and substitution, none giving
  arbitrary extended-ideal finite jets or the graded comparison.
- `msearch.py loogle`, query `MvPowerSeries, TensorProduct, associatedGraded`:
  zero hits; the external index reports `associatedGraded` unknown. Therefore
  this was supplemented by direct reading/searching the project's graded API.
- `msearch.py grep`, query `truncTotal|associatedGraded|rename` in
  `RingTheory/MvPowerSeries`: 22 hits, giving the standard rename and total
  truncation interfaces used here, but no comparison theorem.
- `msearch.py leansearch`, query “An L linear isomorphism between finite jets
  of L[[X,T]] modulo an ideal extended from K[[X]] and a direct sum of tensor
  products of finite jets, compatible with reduction and multiplication”:
  eight hits, on tensor/direct-sum distribution, tensor quotient equivalences,
  and finite-product completion; none states this node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `coefficient.*[Jj]et|[Jj]et.*[Cc]oefficient|extendedPowerSeries|CoefficientExtended`:
  only related tangent-cone and geometric jet statements; read
  `SmoothLocalTangentConeExtension.lean`, whose statement is about essentially
  smooth local maps, not these formal series quotients. Searching the exact
  item id in `lean/WeilConjectures` found no match.
- `rg` for `associatedGraded.*[Aa]lgebra|[Aa]lgebra.*associatedGraded` and
  related graded-class names found only the quotient/residue-field scalar
  interfaces and their users. A general coefficient field action was absent;
  the helper composes the existing degree-zero homomorphism, without copying
  the graded ring definition. The explicit tensor abbreviation avoids its
  existing module action being selected by instance inference.
- Final collision searches for `coefficient_extended_power_series_jets`,
  `CoefficientExtendedJets`, and `gradedBaseAlgebra` across Mathlib, both project
  roots, and `dag/lean_names_upstream.json` found no existing declarations.

Validation: every compile used `scompile.py` with its normal 60-second per-file
limit. The first compile identified the module-instance mismatch for the graded
algebra tensor; the explicit `gradedCoefficients`/`gradedTensor` arguments repaired
it. The corrected sandbox and library-mode compiles both passed, without warnings.

Dry run: `deliver2.py Q50 lem-trf-coefficient-extended-power-series-jets --no-push`
printed OK: the packet passed the server preflight and per-file compiles.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
