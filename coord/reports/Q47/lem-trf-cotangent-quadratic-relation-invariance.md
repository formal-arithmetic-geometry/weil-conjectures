## Worker report

Stage 2 only: two modules, seven real helper definitions/instances and eight theorem
statements with `sorry`. The item's mathematical statement, proof, proof dependencies,
source and status are unchanged. Its statement dependencies gain the new definition
node `def-trf-quadratic-cotangent-relations`.

`Sheaf.RingTheory.QuadraticCotangentRelations` defines the coordinate interfaces;
`Sheaf.RingTheory.CotangentQuadraticRelationInvariance` states all parts of the item.
There is no coefficient-field embedding hypothesis on either abstract local ring.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A,A' commutative local rings, with residue fields k,k' | Independent `Type u`, `Type v`, `[CommRing A]`, `[CommRing A']`, `[IsLocalRing A]`, `[IsLocalRing A']`; `IsLocalRing.ResidueField A` and `ResidueField A'`. |
| Finite-dimensional cotangent spaces and specified finite bases | Mathlib `IsLocalRing.CotangentSpace A`; `Module.Basis (Fin d) (ResidueField A) (CotangentSpace A)` and the analogous `b'` indexed by `Fin d'`. Specifying these bases includes exactly the finite-dimensional hypothesis. An isomorphism subsequently forces equal dimensions; equality is not an extra hypothesis. |
| Homogeneous quadratic expressions W_x | Mathlib `MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2`. Monomials of total degree two include both squares and cross terms, in every characteristic. |
| Target m²/m³ with residue action | `quadraticCotangentTarget A` abbreviates the standard Mathlib quotient `(m^2) / (m • top)` on the module m². Its public instance is precisely Mathlib's quotient-residue action. `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m 2` identifies this with the ideal m²/m³ inside A/m³. |
| Arbitrary lifts of coefficients and basis vectors define mu | `quadraticLiftEvaluation` is the finite support sum of lifted coefficients times lifted monomials. `IsQuadraticCotangentMultiplication A d b μ` quantifies over every coefficient section and every family of lifts of b, and requires equality in A/m³ under the preceding injective inclusion. `quadraticCotangentMultiplication_existsUnique` states unique existence of the residue-linear μ with this characterization. Sections are arbitrary functions, not ring maps. |
| K_x = ker mu | Mathlib `LinearMap.ker μ`; no separate definition or arbitrary substitute for the kernel. |
| Ring isomorphism induces sigma and cotangent bijection | `quadraticCotangentRelations_transport` takes only `φ : A ≃+* A'`. Sigma is exactly Mathlib `IsLocalRing.ResidueField.mapEquiv φ`. It produces an additive equivalence τ, with explicit sigma-semilinearity and equality on every compatible pair of maximal-ideal lifts. |
| Semilinear kernel bijection obtained by coefficient change and substitution | The same theorem produces T on homogeneous quadratics, explicitly states its sigma-semilinearity, and fixes its value by `quadraticLinearSubstitution` using the entries `b'.repr (τ (b i)) j`. It states `μ' (T q) = 0 ↔ μ q = 0` and produces a semilinear additive equivalence κ of the actual kernels, with `(κ q).val = T q.val`. Thus κ cannot be an unrelated bijection. Explicit semilinearity plus additive equivalence is the full semilinear-bijection assertion. |
| Binary polar matrix ((2a,b),(b,2c)) | `MvPolynomial.binaryPolarMatrix` reads the three coefficients; `binaryPolarMatrix_quadratic` states the exact four-entry matrix on `a X₀² + b X₀X₁ + c X₁²`. |
| X = P X' after sigma; B' = P^T sigma(B) P | `quadraticLinearSubstitution σ.toRingHom P` applies sigma to coefficients and sends source variable i to the linear form given by row i of P. `binaryPolarMatrix_substitution` asserts exactly `Pᵀ * (binaryPolarMatrix q.val).map σ * P`. |
| det B' = (det P)^2 sigma(det B) | Second conjunct of `binaryPolarMatrix_substitution`, with Mathlib `Matrix.det`. The formula is asserted for arbitrary P; invertibility is used only for the invariance application. |
| Existence of an invertible-polar relation is invariant, also in char 2 | `nondegenerateQuadraticCotangentRelation_iff` gives the iff of existentials over `LinearMap.ker μ` and `LinearMap.ker μ'`, requiring `IsUnit` of their polar determinants. Over the residue fields this is exactly matrix invertibility. It has no characteristic restriction and no linearity-over-a-coefficient-field assumption on φ. |
| Field F, e ≥ 0, S = F[[z]], p = variables, H contained in p² | `formalQuotient_quadraticCotangent` takes `[Field F]`, `e : ℕ`, `H : Ideal (MvPowerSeries (Fin e) F)` and `hH : H ≤ (Ideal.span (Set.range MvPowerSeries.X)) ^ 2`. |
| A = S/H is local with residue F; variable classes form cotangent basis of dimension e | The theorem gives `Nonempty (IsLocalRing (S ⧸ H))`, then for every such local structure gives a residue ring equivalence ρ normalized on F, a `Module.Basis (Fin e) F (CotangentSpace (S ⧸ H))`, equality of its vectors with the variable classes under `toCotangent`, and `Module.finrank F ... = e`. The universal class binder following existence simply makes the local structure available to elaborate the subsequent types; it is not an assumption of locality. |
| Formal K_z is the quadratic multiplication kernel | The same theorem gives an F-linear μ to the actual m²/m³, specifies its value by evaluation in the quotient modulo m³, and equates its kernel with `formalQuadraticKernel F e H`. The latter is the explicit submodule of homogeneous polynomials whose series lie in p³+H. The residue identification identifies F-linearity here with residue-linearity; no extra choice of map is assumed. |
| H = (f), K_z = F f₂ | `formalPrincipal_quadraticKernel` takes f ∈ p² and states equality with `Submodule.span F {f₂}`. Here f₂ is `MvPolynomial.homogeneousComponent 2 (MvPowerSeries.truncTotal 3 f)`, with Mathlib's own membership certificate for the homogeneous submodule. Its coefficients are precisely the degree-two coefficients of f. |
| f₂ = 0 gives zero kernel | Second conjunct of `formalPrincipal_quadraticKernel` uses `MvPowerSeries.homogeneousComponent 2 f = 0` and gives kernel `= ⊥`. This is the same degree-two part as the polynomial in the first conjunct. |
| Nonzero homogeneous binary Q gives the one-dimensional span of Q | `formalBinary_quadraticKernel` takes `Q : homogeneousSubmodule (Fin 2) F 2`, `hQ : Q ≠ 0`, and gives equality with `Submodule.span F {Q}` and `Module.finrank F ... = 1` for the kernel of the quotient by `Q.val.toMvPowerSeries`. |

The eight postponed theorems each carry the owning DAG id and a complete natural-language
proof of their corresponding part of this node. No proof is supplied in this delivery.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`,
  `MvPolynomial.toMvPowerSeries`, `MvPolynomial.coeToMvPowerSeries.algHom` (the recorded
  power-series definition).
- `Mathlib.LinearAlgebra.Matrix.Defs`: `Matrix`, `Matrix.of`; and
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`, whose docstring and
  `det_apply` give the node's Leibniz determinant convention.
- `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`:
  `power_series_mem_combined_ideal_pow_iff`, read with its full proof docstring and
  signature, and imported as a proof dependency.
- `Mathlib.RingTheory.MvPowerSeries.Inverse`: `MvPowerSeries.isUnit_iff_constantCoeff`
  and its local-ring instance, the recorded match for the other proof dependency;
  imported as a proof dependency.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent`, `Ideal.toCotangent`,
  `IsLocalRing.CotangentSpace`, with their existing residue-module structures.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`:
  `IsLocalRing.ResidueField.mapEquiv`, the canonical residue isomorphism.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`; its full signature and docstring
  identify the standard quotient with the actual ideal of A/m³.
- `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `homogeneousSubmodule`,
  `homogeneousComponent`, `homogeneousComponent_mem`; and
  `Mathlib.RingTheory.MvPowerSeries.Trunc`: `truncTotal`.
- The new node also records the existing polynomial/quotient notions:
  `def-weil-pbc-mv-polynomial-ring` (`MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`), `def-weil-pbc-quotient-module`
  (`Submodule.Quotient.module`, `Submodule.mkQ`, `Submodule.mkQ_surjective`,
  `Submodule.ker_mkQ`) and `def-weil-pbc-algebra-hom-quotient`
  (`AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, ideal multiplication
  and powers). Their recorded signatures and the corresponding source definitions
  were read. No dependency record needed repair.

Edge cases checked before statement writing:

- d=0 (and d'=0): the homogeneous quadratic space and map are zero; no nonempty index
  assumption appears. Local rings need not be Noetherian and can have zero cotangent
  space without being fields; m=m² then also gives m²=m³.
- e=0: S=F and p=0, so H=0 and f=0. The variable basis is empty, and the formal
  multiplication and relation spaces are zero.
- f=0 and f₂=0: the span in the principal formula is bottom. Higher-order f can be
  nonzero while f₂=0; the statement still gives zero degree-two relations.
- Characteristic two: B has zero diagonal and determinant -b²; cross coefficients
  are retained. Neither construction nor theorem divides by two.
- Degenerate nonzero Q, including a square, still has a one-dimensional relation
  space; the final theorem imposes no determinant/nondegeneracy hypothesis.
- Mixed characteristic abstract local rings are allowed: coefficient sections are
  functions, so the definitions never demand an embedding of the residue field.
- A and A' may have different type universes; the formal quotient uses exactly F's
  universe. No equality between unrelated universes is imposed.
- T uses rows of P as the substituted linear forms, giving the required transpose
  placement Pᵀ B P rather than the opposite convention.

Searches actually run (the exact machine results are copied into the new node's
`mathlib_searches` from this item's `searches.jsonl`):

1. `msearch.py ... leanfinder "quadratic cotangent relations local ring isomorphism homogeneous degree two principal power series hypersurface"`: 8 hits, including algebra-presentation cotangent equivalences and Weierstrass preparation; no match.
2. `msearch.py ... loogle "Ideal.Cotangent, RingEquiv"`: 0 hits.
3. `msearch.py ... grep "quadratic.*cotangent|cotangent.*quadratic|quadraticRelation|quadratic_relation"`: 0 Mathlib hits.
4. `msearch.py ... leansearch "The kernel of multiplication from homogeneous quadratics on the cotangent space of a local ring is invariant under ring isomorphisms"`: 8 hits, including `RingHom.ker` and Kähler-differential cotangent ideals; none defines this notion.
5. `msearch.py ... grep "IsQuadraticMultiplication|quadraticLiftEvaluation|formalQuadraticKernel|binaryPolarMatrix"`: 0 hits.
6. `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for quadratic/cotangent combinations and the helper names: no matching construction.
   The two `smoothAtPrime_quotient_of_quadratic_relations` occurrences concern a
   different Popescu-presentation result. The existing formal-Jacobian theorem's
   proof mentions this invariant but does not state or define it.
7. DAG text search for quadratic/cotangent combinations found the item and its
   consumers, not a definition of these coordinate objects; focused searches for
   the new id and helper names found none. `tools/blueprint_refs.py search
   'quadratic cotangent'` returned 0 blueprint nodes. `ancestor` returned
   `lem-trf-local-term-locality`, as recorded in the new node.
8. Direct reads/searches of Mathlib found the existing cotangent, torsion quotient,
   homogeneous polynomial, evaluation, power-series coefficient and determinant APIs;
   these were reused, rather than copied.

Source check: read `literature/stacks-project/curves.tex` at the nondegeneracy definition,
Tag 0C49 and its proof, and the current blueprint ancestor in
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
The item expands the local algebra implicit in the source; its statement requires no
correction. No STATEMENT-DISPUTED fault remains.

Validation: both modules compiled, separately and in dependency order, through the
prescribed `scompile.py`, with no errors or warnings other than the permitted sorry
warnings. The compiler exposed two interface details during drafting: the residue
module on the standard degree-two quotient needed an explicit public instance reusing
Mathlib, and the semilinear-equivalence notation required inverse-ring-hom instances.
The final statement instead spells out semilinearity on additive equivalences. This
changes neither the objects nor the mathematical claim.

## New nodes

`def-trf-quadratic-cotangent-relations` defines the coordinate quadratic multiplication
characterization, its standard quotient target/residue action, arbitrary-lift evaluation,
coefficient-and-linear substitution, binary polar matrix and the formal quadratic kernel.
The source is Tag 0C49's degree-two map and polar-matrix definition; the explicit formal
kernel is its quotient calculation in implication (3) to (1). Existing Mathlib already
supplies the cotangent, homogeneous polynomial and quotient objects, but none of the
logged searches found this characterization or these connecting constructions. The
new module uses those Mathlib objects and contains no postponed theorem or sorry data.
Its target alias and residue action are the same standard quotient construction as in
Mathlib, made nameable here, rather than a new model or an additional module structure.
All seven declarations are recorded in `lean.declarations`. The item's added dependency
reaches the new node, whose chapter, unit and blueprint ancestor match the item.

## Second reading by Q47

Author's second pass, not an independent-agent review: the dispatcher explicitly forbids
starting another agent; the maintainer supplies the independent review after delivery.
I reread the node, both modules, the new definition node and the source against the
clause table above. The first draft's semilinear equivalence notation did not elaborate;
the final additive-equivalence statements include the full semilinearity equations
for τ, T and κ. The first draft also left the degree-two residue module implicit;
the final public instance is Mathlib's existing quotient module, with no proof hole.
The lift predicate specifies values after an injective inclusion, and the existence
statement is unique, so its use as the canonical multiplication map does not assume
an arbitrary function. The formal-quotient statement fixes μ by actual polynomial
evaluation modulo m³ and equates its kernel to the explicit p³+H kernel. The principal
formula uses the full homogeneous degree-two part, not a selected nonzero coefficient.
The binary formula and final nonzero-Q assertion include degenerate and characteristic-two
cases. Only the item's `lean` and its allowed new `stmt_deps` entry changed.
