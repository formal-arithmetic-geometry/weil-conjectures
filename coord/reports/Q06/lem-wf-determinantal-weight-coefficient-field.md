## Worker report

The module `Sheaf.Paper.DeterminantalWeightCoefficientField` states
`AlgebraicGeometry.WeilGroup.isPunctuallyPure_det_coefficientExtension`, with `sorry`.
The auxiliary `representedDegreeDatumOfMatrix` is a real construction: it packages the
existing degree homomorphism, its surjectivity, and the chosen degree-one lift from `W`
with the given matrix representation. It introduces no independent choice or theorem.
The node's natural statement and proof are unchanged. There are no new nodes and no
dependency repairs. The already landed `def-sbc-normal-dominant-galois` was added to
`stmt_deps` to use its actual normal-scheme predicate instead of defining one again.

Source checked: the current main-20261015 blueprint node in sk-d-real-detweights and
that unit's section. The statement agrees with the master statement in the DAG. The
four proof steps in the DAG are included in the theorem docstring.

Hypothesis and conclusion correspondence:

- The finite ground field k0 is `{K : Type u} [Field K] [Finite K]`. The source's prime
  ell is `(l : Nat) [Fact l.Prime]`; `_hl : l ≠ ringChar K` is ell different from the
  characteristic, inherited from sk-d-real-setup.
- The curve and its structure map are `{X : Scheme.{u}}` and
  `{p : X ⟶ Spec (.of K)}` with `[IsConnectedCurve p]`, so it is separated, of finite
  type, nonempty and of dimension one. `_hNormal : IsNormalScheme X` is normality.
  Geometric connectedness is already a field of `W : WeilGroup p`; it is not replaced
  by connectedness alone. The field is `W.geometricallyConnected`.
- The fixed algebraic closure is the upstream `PadicAlgCl l`, and
  `(iota : PadicAlgCl l ≃+* ℂ)` is exactly the fixed field isomorphism of the source.
- `E E' : IntermediateField (Padic l) (PadicAlgCl l)` together with the two
  `FiniteDimensional (Padic l)` instances are actual finite coefficient extensions
  inside this same closure. `hEE' : E ≤ E'` is the given inclusion. The subtype
  embeddings and `IntermediateField.inclusion hEE'` agree literally in the closure;
  unrelated embeddings are not allowed.
- `{r : Nat}` and `ρ : W.carrier →* Matrix.GeneralLinearGroup (Fin r) E` are the
  E-model in a basis of the rank-r representation. A basis exists for every model in
  the source, so using its coordinates restricts neither the representation nor its
  rank. Reading over E' is precisely the representation obtained by composing ρ with
  `Matrix.GeneralLinearGroup.map (IntermediateField.inclusion hEE').toRingHom`.
  The standard identification E' tensor_E E^r = E'^r is the basis identification in
  step 1 of the node proof, not an additional base-change assumption.
- `_hIrreducible` applies Mathlib `Representation.IsIrreducible` to the closure-valued
  representation obtained using `Matrix.GeneralLinearGroup.toRepresentation` and
  `map E.subtype`. This asserts irreducibility over the closure, as required of the
  original Weil sheaf, rather than merely irreducibility of the E-model.
- `_hLisse` asserts continuity of every matrix coefficient on `W.geometric`, after
  its given inclusion in `PadicAlgCl l` with its l-adic topology. This is the definition
  in sk-d-real-weil in the chosen basis. Continuity in one basis is equivalent to
  continuity in every basis, since a change of basis takes finite linear combinations
  of these coefficients (compare upstream `isLisse_iff_exists_basis`). It imposes no
  continuity requirement on the full Weil group and no Frobenius-stable lattice.
- `a : Real` is the weight; it can be any real number. `hPure` is the hypothesis
  `∀ x, ‖iota (E.subtype (determinant Frobenius scalar))‖ = q_x^(a/2)`.
  The determinant is the recorded `RepresentedDegreeDatum.det`, not a replacement
  character or a new determinant definition. Its rank-one matrix has the scalar as
  its (0,0) entry, by `det_rep` and `coe_detGL_apply`.
- The conclusion is the identical norm equality for the E'-model's determinant at
  every `x : X.finitePoints`, with the same `iota`, `a` and `X.pointNorm x.val`.
  `pointNorm` is definitionally `Nat.card (X.residueField x.val)`. On a finite-type
  scheme over a finite field these points are exactly the closed points; the existing
  Weil-group interface indexes local Frobenius by precisely these points.

The rank-one specialization of punctual purity is written out, rather than introducing
another predicate. For multiplication by a scalar d on a line, d is its sole eigenvalue:
a nonzero eigenvector v gives (d-alpha)v = 0, hence alpha = d, and every nonzero v is
a d-eigenvector. Thus the norm equality is exactly all-eigenvalue purity, in both
directions, without a semisimplicity assumption. The recorded common-stage
`SfIsPunctuallyPureOfWeight` has the same defining norm equality but takes an object of
the sheaf heart; this lemma instead uses the finite coefficient representation that the
source explicitly supplies. No unrelated sheaf object, realization equivalence, or
arbitrary comparison map is added as a hypothesis. The recorded weight module is
imported, and its literal defining equality is specialized to the actual determinant
line; no second purity definition is made.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Functoriality`:
  `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.det` and `det_rep`. Its current
  source was fetched with `scompile.py --source` because the old checkout lacks it.
  Also read `Matrix.GeneralLinearGroup.detGL`, `coe_detGL_apply`, and its polynomial
  realization in the dependency module `GeneralLinearGroup.Regular` from that source
  service. The determinant is the existing 1x1 matrix representation.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic`:
  `AlgebraicGeometry.WeilGroup`, `geometric`, `IsLisse` and `isLisse_iff_exists_basis`.
  The datum construction uses its degree data; the hypothesis states its matrix
  continuity condition directly, avoiding a restriction of the scheme universe to the
  universe of the small coefficient vector space.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its imported
  `CoefficientExtension`): the finite coefficient extension notion is the existing
  `Algebra (Padic l)` with `FiniteDimensional`, realized here as intermediate fields.
  The integer rings, uniformizers and finite-level quotients are not needed in this
  scalar-extension statement.
- `Sheaf.Paper.AdicPunctualWeights`:
  `WeilConjectures.SfPunctualEigenvalue` and `SfIsPunctuallyPureOfWeight` were read in
  full. The latter's defining all-closed-points norm equality is used literally in the
  rank-one specialization, as explained above.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`.
- Mathlib's `IntermediateField.inclusion`, `Matrix.GeneralLinearGroup.map` and
  `Representation.IsIrreducible`; upstream `Matrix.GeneralLinearGroup.toRepresentation`.

Edge cases checked: E'=E is allowed by the non-strict inclusion; rank one gives precisely
the original Frobenius eigenvalue; rank zero is excluded by the original irreducibility
condition (its representation has no nontrivial invariant-space lattice); the empty
scheme is excluded by the curve/geometric-connectedness hypotheses. The construction
and determinant calculation work for non-diagonalizable Frobenius, repeated eigenvalues,
and a Frobenius matrix whose eigenvalues are outside E. Negative and nonintegral weights
are included; no positivity, rationality or integrality is imposed on a. No equality of
scheme and coefficient universes is imposed: the scheme has arbitrary universe u and
coefficients are actual subfields of the fixed small closure.

Searches performed before writing:

- `msearch.py leanfinder`: “Punctual purity of determinant of Weil representation
  unchanged under extension of finite l-adic coefficient field”. Hits included
  `IsBaseChange.det_endHom`, `LinearEquiv.det_baseChange`, and
  `LinearMap.det_baseChange`; none is the Weil-representation assertion.
- `msearch.py loogle`: `LinearMap.det_baseChange, LinearEquiv.det_baseChange`:
  zero hits for the joint pattern.
- `msearch.py leansearch`: “The weight of the determinant of a Weil sheaf is unchanged
  by coefficient field extension”. Hits were determinant/base-change and basis-change
  identities; no full statement.
- `msearch.py grep` on Mathlib/LinearAlgebra:
  `det_baseChange|determinantal.*coefficient|coefficient.*determinantal|def det`:
  determinant constructions and determinant base-change identities only.
- `rg` over upstream WeilConjectures and project lean/Sheaf for coefficient-field
  determinant purity, determinant scalar extension, and the proposed declaration names;
  no existing theorem or conflicting helper name. `grep -rn` for the node id over
  upstream WeilConjectures found no declaration. The upstream names index was consulted
  via `tools/lean_names_upstream.py show`. Read the determinant, exterior power, scalar
  representation, irreducibility, coefficient-extension and weight APIs found in these
  searches. Reused the existing determinant instead of creating a new determinant node.

No STATEMENT-DISPUTED flag or source correction is needed.

Validation: the prescribed `scompile.py` compiled the module cleanly on the server,
including its actual library module name. The only proof is the requested `sorry`.
The first compile found that the intermediate-field `subtype` is already a RingHom;
removing the unnecessary `.toRingHom` corrected the type error.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
