## Worker report

The module `Sheaf.RingTheory.CompletedEtaleJacobianTorsion` states
`AlgebraicGeometry.exists_completedEtaleJacobianTorsion`, with `sorry` as its only proof.
It defines no new notion. I read the current item, its six proof steps, every statement
node dependency and its recorded declaration/signature/docstring, the stage-2 brief,
the stage document, section H of delivery-errors, and the CompactObject example.

The previous blocked message confused a stage-1 merge with a stage-2 statement: Q47's
review is the split of this lemma, and the current node has no `lean` or `reviewed_lean`.
The retained sandbox had only dispatcher briefs, so this packet supplies the missing
stage-2 statement rather than re-delivering Q47's split. It retains Q47's statement,
proof and proof dependencies unchanged. The only added statement dependency is the
already landed `def-per-completed-polynomial-conormal` from Q93.

The source is Stacks restricted.tex, equation (NL), Tags 0AJP, 0AJU(3), 0ALQ(1), and
0GAF; completeness is algebra.tex, Tag 00MA(3). I read the actual local source of
(NL), 0ALQ and 0GAF, including the comparison identifying the ordinary and completed
conormal differentials. These assert the same finite-algebra special case as the node.

Clause-by-clause correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- An arbitrary ideal I and completeness of A: `(I : Ideal A) [IsAdicComplete I A]`.
  This is the recorded Mathlib notion of bijectivity of the canonical completion map.
- A commutative A-algebra E finite as A-module:
  `(E : Type u) [CommRing E] [Algebra A E] [Module.Finite A E]`.
- Étaleness over Spec A minus V(I): `het` applies `Etale` to the restriction of
  `Spec.map (CommRingCat.ofHom (algebraMap A E))` to the open complement of
  `PrimeSpectrum.zeroLocus (I : Set A)`. It assumes precisely that restriction is
  étale, with no étaleness assumption on points over V(I).
- E is I-adically complete: the first conclusion is `IsAdicComplete I E`.
  Using A's ideal on the A-module E is the usual IE-adic ring completeness.
- E/IE is finite type over A/I: the next conclusion is `RingHom.FiniteType` of
  `Ideal.quotientMap (I.map (algebraMap A E)) (algebraMap A E) Ideal.le_comap_map`.
  This explicitly uses the canonical quotient ring map, with no chosen algebra
  structure or additional assumption.
- There exists r >= 0: `∃ (r : ℕ)` includes r = 0.
- P is the I-adic completion of A[x_1,...,x_r]: `rigPolynomialCompletion I r`
  is the already recorded completion at the extended ideal IQ of
  `MvPolynomial (Fin r) A`. The IQ-adic filtration on Q equals the I-adic
  filtration on the A-module Q; this is exactly P in the source.
- The surjective A-algebra map P → E: `f : rigPolynomialCompletion I r →ₐ[A] E`
  and `Function.Surjective f`.
- Its kernel J: `RingHom.ker f.toRingHom` throughout, so no arbitrary kernel ideal
  or unconstrained presentation is introduced.
- The continuous-derivative conormal map δ: the recorded
  `rigJacobianDifferential r I (RingHom.ker f.toRingHom)`, whose domain is Mathlib's
  `J.Cotangent = J/J²`. Its coordinates are the continuous partial derivatives
  reduced modulo J; these are exactly the Q93 definitions, not new local copies.
  The displayed codomain is `Fin r → P/J`. The canonical algebra equivalence
  `Ideal.quotientKerAlgEquivOfSurjective hf : P/ker f ≃ₐ[A] E` identifies it with
  E^r, the finite direct sum in the node. Transport along this equivalence gives
  precisely the node's E-linear map. The recorded interface exposes its underlying
  A-linear map, which suffices for the kernel and cokernel annihilation statements;
  no choice of map is quantified and no different differential is substituted.
- There exists one c >= 0: `∃ c : ℕ` precedes both annihilation clauses.
- I^c kills ker δ: `I ^ c • δ.ker ≤ ⊥` in the A-submodule lattice.
- I^c kills coker δ: `I ^ c • (⊤ : Submodule A (codomain ⧸ δ.range)) ≤ ⊥`.
  These quotient/range modules are the underlying A-modules of the same kernel
  and cokernel over E, via the canonical quotient equivalence. Vanishing of their
  I^c action is unchanged on forgetting the E-module structure.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` (through Algebra):
  `AdicCompletion`, `IsAdicComplete`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, and its evaluation
  `MvPolynomial.aeval`/extensionality `MvPolynomial.algHom_ext` supply the recorded
  polynomial notion used by the existing completed-ring definition.
- `Sheaf.RingTheory.CompletedPolynomialConormal`:
  `AlgebraicGeometry.rigPolynomialCompletion`, `rigPartialDerivative`,
  `rigJacobianRawDifferential`, `rigJacobianDifferential`. I read this entire
  landed module and its node record, including the unique filtration-preserving
  derivative characterization and the named well-definedness obligation.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent`.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.quotientMap`,
  `Ideal.quotientKerAlgEquivOfSurjective` (the latter explains the canonical
  identification in the docstring/report).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.

The plain proof imports follow the existing proof dependencies. They include the
upstream conormal criterion, finite-module completeness, and principal-localization
naive-cotangent modules and the corresponding Mathlib localization, finite-presentation,
Kähler-basis, Noetherian, and open-immersion modules. The sole currently unstated proof
input, `lem-per-polynomial-conormal-completion`, has no module to import; it is named
with its exact role in step 6 of the proof docstring. It is not needed to type the
statement and no replacement theorem is introduced for it.

Edge cases checked before writing:

- I = 0: the complement is empty and the étale hypothesis is vacuous; c = 1
  annihilates all kernel/cokernel modules. This does not assert E is étale:
  E = k[x]/(x²) is allowed. Completion at zero is the identity.
- I nilpotent: the complement is again empty, and a positive nilpotence exponent
  kills the two modules.
- I = A: completeness forces A to be the zero ring, so E is also zero. Nothing
  excludes the empty affine spectra or the zero algebra.
- r = 0: `Fin 0 → P/J` is the zero free module. J need not vanish, and its
  conormal kernel is still constrained by the stated torsion bound.
- c = 0 is permitted and means the two modules vanish; no positivity restriction
  on c or r is imposed.
- E = 0 and f with J = P: the same kernel/cokernel types remain meaningful.
- Universes are explicitly bound. The scheme restriction uses the project's
  common `Scheme.{u}` convention, as the recorded Spec/Etale APIs require; there
  is no quantification over a smaller universe of test algebras or test schemes.

Searches actually run with `msearch.py Q64 lem-per-completed-etale-jacobian-torsion`:

1. LeanFinder: "finite algebra over an adically complete Noetherian ring etale
   outside an ideal has completed Jacobian conormal differential with kernel and
   cokernel killed by a power of the ideal". Eight hits concerned étale loci,
   square-zero lifting, formal smoothness and ordinary cotangent support; none
   states this completed torsion assertion.
2. Loogle: "AdicCompletion, MvPolynomial.pderiv". Zero hits.
3. Grep in Mathlib/RingTheory: "AdicCompletion.*(deriv|Deriv)|completed.*[Cc]onormal".
   Zero hits.
4. LeanSearch: "A finite algebra over an adically complete Noetherian ring etale
   outside an ideal has a completed polynomial presentation with conormal kernel
   and cokernel annihilated by a power of that ideal". Eight hits on étale finite
   presentation, ordinary standard-étale presentations and formally smooth
   lifting into completions; none states the item.
5. `rg` in WeilConjectures and lean/Sheaf for completed Jacobian/conormal/derivative
   patterns and the exact item ID. The upstream Jacobian hits concern Jacobians
   of curves, not completed polynomial conormal maps. The side project contains
   the reusable `CompletedPolynomialConormal` definition and the downstream
   `RigEtaleJacobianAlgebraization` theorem, which assumes torsion and concludes
   algebraization. Neither already states this item's existence of torsion.
   `ElkikFiniteEtaleAwayCompletion` cites this item only in its proof docstring.
   Other completed-Jacobian modules concern completed local rings over fields
   and differential cokernels, not this arbitrary-base finite-algebra theorem.

No new node, dependency module, statement correction or statement dispute is involved.
The node's statement and proof are retained. The only statement-dependency addition
cites the existing landed conormal construction actually used by the Lean signature.

Validation: `scompile.py Q64 lem-per-completed-etale-jacobian-torsion
<CompletedEtaleJacobianTorsion.lean>` compiled the sandbox and library forms in 3.5 s
per file, with no errors or warnings. No Lake/global build, source checkout edit,
shared repository mutation or direct git command was performed. Delivery/preflight
validation is performed through the prescribed `deliver2.py` wrapper below.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
