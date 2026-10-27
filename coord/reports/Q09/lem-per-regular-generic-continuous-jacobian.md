## Worker report

The item module is `Sheaf.RingTheory.RegularGenericContinuousJacobian`, with main
statement `AlgebraicGeometry.exists_continuousJacobian_powerSplitting`. Its proof
is `sorry`. The missing prerequisite `def-per-completed-polynomial-conormal` is
supplied in `Sheaf.RingTheory.CompletedPolynomialConormal`. No existing live Lean
statement of the item was found. The item's natural-language statement is unchanged;
its only non-lean change is adding this prerequisite to `stmt_deps`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A characteristic-zero field k is `(k : Type u) [Field k] [CharZero k]`.
- The integer r >= 0 is `(r : ℕ)`, including zero.
- The polynomial ring k[t,x_1,...,x_r] is written as
  `MvPolynomial (Fin r) (Polynomial k)`: the canonical iterated polynomial
  presentation, with `Polynomial.X` the distinguished coefficient variable t.
  The polynomial universal property identifies this with the joint-variable
  presentation without any extra hypothesis on k.
- P is `rigPolynomialCompletion (Ideal.span {(Polynomial.X : Polynomial k)}) r`.
  Unfolding the abbreviation gives exactly `AdicCompletion` of that polynomial
  ring along the extension of the ideal (t). Thus this is completion only along
  t, not along the variables x_i.
- J is the arbitrary binder `J : Ideal P`, and B is literally `P ⧸ J` everywhere
  in the signature. No reducedness, flatness, completeness of B, or condition
  that t be a non-zero-divisor is added.
- The regular Noetherian generic fibre assumption is
  `[IsRegularRing (Localization.Away (algebraMap (Polynomial k) B Polynomial.X))]`.
  `IsRegularRing` extends `IsNoetherianRing`; `Localization.Away` inverts the
  submonoid of powers of the image of t in B. In particular it does not localize
  the wrong ring or assume the image is nonzero.
- `J.Cotangent` is Mathlib's J/J^2, with its canonical B-module structure.
- The specified delta is `rigJacobianDifferential (Ideal.span {Polynomial.X}) r J`.
  It is B-linear and its unique characterization is
  `δ (J.toCotangent f) i = Ideal.Quotient.mk J (rigPartialDerivative I r i f.val)`.
  The derivative is the uniquely specified A-derivation on P extending
  `MvPolynomial.pderiv i`, preserving `(IP)^n` for every n. Inverse-limit
  polynomial approximations are precisely how this continuous extension is
  characterized and constructed in its proof plan; no arbitrary derivative is
  used as a hypothesis.
- The finite direct sum B^{oplus r} is the finite coordinate module `Fin r → B`.
  Finite product and finite direct sum coincide here, including r=0.
- The conclusion binds `∃ (c : ℕ) (h : (Fin r → B) →ₗ[B] J.Cotangent)` and states
  `h.comp delta = (algebraMap (Polynomial k) B Polynomial.X)^c • LinearMap.id`.
  This is equality of B-linear endomorphisms of J/J^2. It is the specified
  left splitting up to the power, including c=0.
- There is no condition or conclusion on the cokernel of delta.

Recorded dependencies read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`, with `MvPolynomial.aeval` and `MvPolynomial.algHom_ext`
  (the latter in Basic, aeval in Eval). Their definitions/signatures and the
  polynomial universal property were read; the actual polynomial and
  differentiation types are reused, not copied.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; ring/algebra structures and structural maps are from
  `Mathlib.RingTheory.AdicCompletion.Algebra`. The compatible-sequence
  definition and `algebraMap` implementation were read.
- `def-weil-regular-scheme`: public import
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, whose recorded declaration and
  full docstring were read. The ring clause needed here is the same node's
  Mathlib match `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`; its extension of Noetherianity
  and regularity at each prime were read. No scheme notion is substituted for
  ring regularity.
- The added prerequisite `def-per-completed-polynomial-conormal` supplies
  `AlgebraicGeometry.rigPolynomialCompletion`, `rigPartialDerivative` and
  `rigJacobianDifferential` from `Sheaf.RingTheory.CompletedPolynomialConormal`.
- Proof imports (non-public) are the already stated dependencies:
  `Mathlib.Algebra.Module.LocalizedModule.Basic` (`LocalizedModule.Away`),
  `Mathlib.LinearAlgebra.Matrix.Adjugate` (`Matrix.adjugate_mul`),
  `Mathlib.RingTheory.RegularLocalRing.Polynomial`
  (`MvPolynomial.isRegularRing_of_isRegularRing`), and
  `WeilConjectures.RingTheory.AdicCompletionNoetherian`
  (`AdicCompletion.isNoetherianRing`). Their signatures and source were read.
  The two affinoid proof dependencies have no Lean records or Mathlib matches,
  so there is no module to import for them; they are explicitly named in the
  seven-step theorem proof docstring, not used as statement assumptions.

Source check: read Temkin's PDF at the node's URL, Proposition 3.3.1 proof and
Proposition 3.3.2 (printed pp.19--21), and the full condition (3) plus the
adjugate/minor argument in `literature/stacks-project/restricted.tex`,
`lemma-equivalent-with-artin-smooth` (Tag 0GAJ). The source yields a power
splitting, not torsion of the cokernel. The definition module follows the same
file's equation (NL) and Tag 0AJU. The source has no missing condition forcing
t to be a non-zero-divisor on B.

Edge cases checked before writing:

- r=0: `Fin 0 → B` is the zero coordinate module; the statement says a power
  of t kills J/J^2, without imposing nonemptiness of the variable set.
- J=0: the conormal module is zero and the conclusion admits c=0, h=0.
- J=top: B and its localization are the zero ring; regularity of this ring is
  the Noetherian/vacuous-at-primes convention. Both modules in the conclusion
  are zero and the statement is meaningful.
- B[1/t]=0, including t nilpotent in B: a power of t vanishes; choose that
  exponent and h=0. No integral-domain or injective-localization hypothesis
  excludes these cases.
- Example J=(t*x) with r=1 illustrates why t-torsion in B is permitted:
  differentiating the equation gives t. Sending the single coordinate basis
  vector to the equation class yields h delta = t id; cancellation of t
  is not built into the signature.
- c=0 is permitted, and the scalar is t^0=1, so the equation is an actual
  splitting in this case.
- In the general prerequisite, I=0 and I=top both have meaningful completions;
  the unique derivative specification includes these cases. No independent
  test-object universe can make a premise vacuous; all rings stay in the
  arbitrary universe u.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Regular generic fibre of an adically completed
  polynomial quotient has a continuous conormal differential splitting up to
  a power of the parameter"`: OK, 8 hits, including Weierstrass division
  results and `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`.
  None deduces this continuous power splitting from regularity of the generic
  affinoid fibre.
- `msearch.py ... loogle '"FormallySmooth", "split"'`: OK, 4 hits:
  `Algebra.FormallySmooth.of_split`, `iff_split_surjection`,
  `Algebra.Extension.formallySmooth_iff_split_injection`, and
  `Algebra.FormallySmooth.iff_split_injection`. These concern ordinary formal
  smoothness, not the hypothesis here, and are not the item.
- `msearch.py ... grep 'continuous.*[Jj]acobian|rigJacobianDifferential|affinoid'
  RingTheory`: OK, 0 hits.
- `msearch.py ... leansearch "Continuous conormal differential on the adic
  completion of a multivariable polynomial ring"`: OK, 8 hits, including
  `AdicCompletion`, its ring and module structures, and completeness lemmas;
  no completed-polynomial conormal differential.
- `rg -n 'regular-generic-continuous-jacobian|continuous Jacobian|continuous.*Jacobian'
  literature/blueprint/latest dag/nodes/sec-deligne-laumon-a1 lean/Sheaf lean/WeilConjectures`:
  found the item, its affinoid children, its algebraization citer and related
  but different formal-power-series presentation statements; no existing item.
- `rg -n 'AdicCompletion.*[Dd]eriv|[Dd]eriv.*AdicCompletion|rigPartialDerivative|rigJacobianDifferential'
  lean/WeilConjectures lean/Sheaf`: found upstream
  `Derivation.exists_completion_and_unique_localization` in
  `WeilConjectures.RingTheory.Derivation.CompletionAndLocalization`. Read its
  full signature/docstring: it concerns integer derivations, uses a shifted
  ideal filtration, and does not supply the completed-polynomial conormal map.
  The implementation of its coordinatewise completion construction is private.
  It does not duplicate the additional canonical interface stated here.
- `rg -n 'lem-per-regular-generic-continuous-jacobian' lean/WeilConjectures`:
  no matches. `rg -n 'rigPolynomialCompletion|rigJacobianDifferential' lean`
  found no live declaration. DAG search found the existing definition node
  `def-per-completed-polynomial-conormal`; thus no new notion node is created.
- `scompile.py --source Sheaf.RingTheory.CompletedPolynomialConormal`:
  "Module source unavailable". Its existing DAG `lean_removed` record says
  the module was deleted as dead and the declaration survives nowhere. This
  confirms a genuinely missing prerequisite, rather than a stale local copy.

Validation: all delivered files were compiled separately by `scompile.py`, in
prerequisite order, against the live published library. Both sandbox and library
mode checks passed with no unexpected warning (about 3 seconds for the
prerequisite, 7 seconds for the item). `autoImplicit` is false. No diagnostic
commands remain. Only the three named theorem proofs are `sorry`:
`existsUnique_rigPartialDerivative`, `existsUnique_rigJacobianDifferential`, and
`exists_continuousJacobian_powerSplitting`. The first two state exactly the
existence/uniqueness and well-definedness properties of the matching definition
node, with step-by-step proof docstrings. Definitions choose only data uniquely
determined by these characterizations. No independent data is selected from a
bare existence theorem.

No STATEMENT-DISPUTED flag or statement correction is needed.

## Dependency modules

`def-per-completed-polynomial-conormal`: the recorded module had been deleted,
its `lean` is null, and its `lean_removed` field states why. The live server
source lookup confirmed its absence. Under the human instruction to supply
missing genuine DAG prerequisites in this delivery, its node is copied with only
`lean` changed, and the item cites it. The module constructs P using Mathlib
`MvPolynomial` and `AdicCompletion`. It states unique existence of the continuous
A-partial derivations with their polynomial values and all ideal-power estimates,
then defines the canonical derivative by that unique characterization. It states
unique existence of the induced P/J-linear conormal map with the exact formula on
every class, and defines it from that unique characterization. This quotient
linearity is the usual Leibniz consequence of the original A-linear map and gives
the original map, not an additional map or assumption. The node's mathematical
statement and every field except `lean` are unchanged. Every declaration bears
this definition node's blueprint identifier.

## Second reading by Q09

I reopened both node copies and both finished modules for a separate reading;
this is a second pass by the assigned worker, not a claim that an independent
agent was started (the dispatcher explicitly prohibits that). Independent
maintainer review remains the review of the delivery.

The field/characteristic binders, arbitrary nonnegative r, principal t-adic
completion, arbitrary ideal, actual quotient, and localization at the actual
coefficient variable match the item in order. IsRegularRing includes the stated
Noetherianity; no condition on B or on t was inserted. The output h has scalar
ring B and source the finite r-coordinate module, while its target is J/J^2.
The direction is h after delta, and the scalar is precisely t^c, not a general
nonzero scalar or a power killing only the kernel. There is no cokernel clause.

For the dependency I checked the derivative's extension formula and its estimate
for every n (including n=0), the finite r indexing, the same quotient J.Cotangent,
and the formula for every representative and every coordinate. Both choices have
unique-existence specifications; the maps cannot depend on an arbitrary lift.
The bundled B-linearity also supplies the dependency's A-linearity. All source
places and the seven proof steps are present in docstrings. No mismatch requiring
a source-based correction was found. The missing prerequisite was supplied in
full rather than copying an arbitrary map into the main theorem's hypotheses.
