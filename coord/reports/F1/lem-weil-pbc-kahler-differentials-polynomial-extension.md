## Worker report

The module `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension` states
`KaehlerDifferential.exists_polynomial_extension_equiv`, with one `sorry` proof and no
new definitions. The node is unchanged except for its `lean` record. No dependency
module or new node is needed.

The source was read in the locally available Stacks checkout at
`/home/ubuntu/c1-stacks-review/algebra.tex`: lines 34057–34076
(`lemma-exact-sequence-differentials`, Tag 00RS), 34213–34232
(`lemma-differentials-base-change`, Tag 00RV), and 34310–34340
(`lemma-differentials-polynomial-ring`, Tag 00RX). These respectively give the exact
sequence, base-change comparison, and variable-differential basis used in the node's
six-step proof. The motivating polynomial-extension relative-dimension passage was
also read in `smoothing.tex`, lines 1568–1576. The module docstring records every
proof step and the DAG lemmas used there. Those proof dependencies are not assumed
as extra hypotheses.

Hypotheses and clauses, in the order of the node:

- A homomorphism of commutative rings `R → A` is represented by
  `(R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]`.
  An arbitrary ring homomorphism determines this algebra structure; its structure
  map is `algebraMap R A`. The two ring universes are independent and explicit.
- The nonnegative integer `e` is `(e : ℕ)`, including zero.
- The polynomial algebra `B = A[z₁,…,zₑ]` is `MvPolynomial (Fin e) A`.
  Reindexing the variables from 1,…,e to `Fin e` changes no object. Its `A`-algebra
  structure is constants, and its inferred `R`-algebra structure is the composite
  `R → A → B`: `MvPolynomial.algebraMap_apply` reads
  `algebraMap R B r = MvPolynomial.C (algebraMap R A r)`.
- `B ⊗_A Ω_{A/R}` is `MvPolynomial (Fin e) A ⊗[A] KaehlerDifferential R A`.
  `Bᵉ` is `Fin e → MvPolynomial (Fin e) A`. The binary direct sum is their product;
  for two modules, product and direct sum are the same module.
- The specified `B`-linear map is an isomorphism: the first conjunct asserts
  existence of a `≃ₗ[MvPolynomial (Fin e) A]` from that product to
  `KaehlerDifferential R (MvPolynomial (Fin e) A)`.
- Its formula is imposed for EVERY tensor-module element `x` and EVERY coefficient
  vector `b`: `E (x,b) = mapBaseChange R A B x + ∑ j, b j • D R B (MvPolynomial.X j)`.
  The first summand is the existing canonical map, not an arbitrary isomorphism.
  `mapBaseChange_tmul` and `map_D` give precisely
  `mapBaseChange R A B (b ⊗ₜ D R A α) = b • D R B (MvPolynomial.C α)`;
  thus the imposed formula is exactly the one stated on pure differential tensors
  in the node. Those tensors generate the first summand.
- The rank consequence is the second conjunct:
  `∀ d : ℕ, Nonempty (Module.Basis (Fin d) A (KaehlerDifferential R A)) →`
  `Nonempty (Module.Basis (Fin (d+e)) B (KaehlerDifferential R B))`.
  Existence of a basis of d elements expresses finite freeness of rank d directly;
  the conclusion expresses finite freeness of rank d+e. There is no field,
  domain, finite-type, smoothness or nontriviality assumption.

Dependency declarations read and used:

- `def-weil-pbc-kahler-differentials` is a Mathlib leaf, whose `mathlib_match` is
  `KaehlerDifferential` in `Mathlib.RingTheory.Kaehler.Basic`. Read its full
  definition/docstring at lines 145–155, `KaehlerDifferential.D` at 197–210,
  and `KaehlerDifferential.linearMapEquivDerivation` at 323–332. The last declaration
  verifies that the concrete cotangent-module implementation has the universal
  property in the dependency node. The module uses `KaehlerDifferential`, `D`,
  and `mapBaseChange` (full signature/docstring read at 715–728).
- `def-weil-pbc-mv-polynomial-ring` is a Mathlib leaf with declarations
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`. Read the
  definition/docstring at Basic lines 79–83, the full `algHom_ext` signature/docstring
  at 431–439, and `aeval`/`aeval_X`/`aeval_unique` at Eval lines 589–623.
  The polynomial carrier, constants and variables used by this statement come from
  `Mathlib.Algebra.MvPolynomial.Basic`; evaluation and uniqueness are not needed
  in this signature, so there is no unused Eval import.
- `Mathlib.LinearAlgebra.Basis.Defs` supplies `Module.Basis` for the rank clause.
  `KaehlerDifferential.mapBaseChange` supplies the canonical linear map with its
  scalar-extension structure. No private copies of either notion are introduced.

Edge cases checked before writing: for `e=0`, the coefficient vector is the zero
module and the finite sum is empty, so the canonical decomposition is just scalar
extension along `A → A[∅] ≅ A`. For `d=0`, a zero differential module gives the
variable-differential basis of length e. For `A=R`, the first summand vanishes,
recovering Tag 00RX. For the zero ring A, all modules here are zero and bases
indexed by any finite set exist; using bases rather than a numerical finrank
identity preserves that case. The statement makes no characteristic restriction,
and does not assume that `R → A` is injective or surjective.

Searches actually run through `/home/ubuntu/weil-launcher/msearch.py`, group F1,
item `lem-weil-pbc-kahler-differentials-polynomial-extension`:

- LeanSearch: `Kähler differentials polynomial algebra over an algebra direct sum
  base changed differentials`. Result: service unavailable, Internal Server Error;
  this is unavailable, not evidence of no match.
- LeanFinder: `Kähler differentials of A[z] over R decompose as B tensor Omega A
  over R plus free module`. Eight hits: `Algebra.Generators.toKaehler_tmul_D`,
  `instFreeMvPolynomialKaehlerDifferential`, cotangent-space basis formulas,
  `Algebra.Generators.H1Cotangent.δAux`, `KaehlerDifferential.D_apply`, and
  `KaehlerDifferential.mvPolynomialEquiv`. None states the extension decomposition.
- Loogle: `KaehlerDifferential.mapBaseChange`. Ten hits, including its tensor formula,
  range/exactness, a surjectivity theorem requiring a surjective algebra map,
  and the formally étale comparison. None states this polynomial-extension map
  is an isomorphism with the additional variable summand.
- Mathlib grep: `mvPolynomial.*Equiv|polynomial.*Equiv|mapBaseChange` in
  `RingTheory/Kaehler`. Fifteen hits. Read `Kaehler/Polynomial.lean` lines 27–82:
  `mvPolynomialEquiv` and `mvPolynomialBasis` concern Ω_{R[z]/R}, not Ω_{A[z]/R}.
  `mapBaseChange` and exactness alone do not give the node's statement.
- Project/source `rg`: `kahler|Kaehler|Kähler` and
  `lem-weil-pbc-kahler-differentials-polynomial-extension|polynomial.*extension|mvPolynomial.*Equiv`
  in `WeilConjectures` and repository `lean/Sheaf`; found related differential
  constructions and proof citations, but no existing declaration for this node.
- `tools/lean_names_upstream.py show lem-weil-pbc-kahler-differentials-polynomial-extension`
  and a search for the id in `dag/lean_names_upstream.json`: no attachment.
- Exact-name search `poly.*extension.*equiv|exists_polynomial_extension_equiv`
  in Mathlib, WeilConjectures and repository `lean/Sheaf`: no collision.

Validation: server single-file compilation with `scompile.py` succeeded (exit 0,
1.4 seconds), with no errors or warnings. Every variable/universe is explicit and
`autoImplicit` is disabled. There is no disputed statement or node correction.

## Second reading by F1

I independently read the node, the delivered module, both statement-dependency
nodes and their Mathlib declarations, and the Stacks source. The statement is
correct as written. No mismatch was found; no Lean or node field was changed.

The node's objects, hypotheses and conclusions, matched in order:

1. Arbitrary commutative rings and a ring map `R → A`: the binders
   `(R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]`.
   Verdict: exact. A ring map to a commutative ring supplies this algebra
   structure, with no injectivity, finiteness or nontriviality requirement.
2. Nonnegative integer `e`: `(e : ℕ)`. Verdict: exact, including zero.
3. `B = A[z₁,…,zₑ]` with the composite `R`-algebra structure:
   `MvPolynomial (Fin e) A`. Verdict: exact. `Fin e` merely reindexes the
   variables. I read `MvPolynomial.algebraMap_eq` and `algebraMap_apply`
   (Basic.lean:111–123): constants give `A → B`, and the `R` map is
   `r ↦ C (algebraMap R A r)` as required.
4. The two summands and target: `B ⊗[A] KaehlerDifferential R A`, `Fin e → B`,
   and `KaehlerDifferential R B`. Verdict: exact. The product of two modules
   is their binary direct sum; a finite function module is precisely `Bᵉ`.
5. The specified map is a `B`-linear isomorphism: the first conjunct is
   `∃ E : (...) ≃ₗ[B] KaehlerDifferential R B` together with its formula for
   every `x` and `b`. Verdict: exact, not merely existence of an unrelated
   isomorphism. Reading `mapBaseChange` (Basic.lean:719), its tensor formula,
   and `map_D` gives
   `mapBaseChange R A B (c ⊗ₜ D R A α) = c • D R B (C α)`.
   Thus `E (x,b) = mapBaseChange ... x + ∑ j, b j • D R B (X j)` renders
   exactly the node's pure-tensor formula. Differential generators span
   Ω, as witnessed by `tensorProductTo_surjective` and the universal
   property; linearity fixes the formula on all tensors. Quantifying over
   all `x` therefore introduces no stronger requirement.
6. Free of rank `d` implies free of rank `d+e`: the second conjunct is
   `∀ d : ℕ, Nonempty (Module.Basis (Fin d) A (KaehlerDifferential R A)) →`
   `Nonempty (Module.Basis (Fin (d + e)) B (KaehlerDifferential R B))`.
   Verdict: exact finite free rank assertion. The node's proof uses a
   finite list `ω₁,…,ω_d`; no numerical rank or invariant-basis-number
   assumption is imposed. This clause uses the same `R`, `A`, and `e`.

Source and dependency check: Stacks Algebra's Differentials section starts
with arbitrary ring maps, without additional standing hypotheses. I read
its derivation definition, differential construction and universal property
(algebra.tex:33780–33885), and the full statements and proofs of 00RS
(34057–34076), 00RV (34213–34232), and 00RX (34310–34340). They support the
node's exact-sequence, base-change, and polynomial-basis argument; none
requires a field, Noetherian ring, characteristic restriction or smoothness.
The motivating passage in smoothing.tex:1568–1576 is a use of the result,
not an additional hypothesis of this algebraic statement.

For `def-weil-pbc-kahler-differentials` I opened `KaehlerDifferential`, `D`,
and `linearMapEquivDerivation` in Mathlib.RingTheory.Kaehler.Basic. The
cotangent implementation has exactly the node's universal derivation
property; its full signature allows arbitrary module universes and the
usual restricted scalar structure. For `def-weil-pbc-mv-polynomial-ring`
I opened `MvPolynomial`, `algHom_ext`, and Eval.lean's `aeval`, `aeval_X`,
and `aeval_unique`. The monoid algebra is the required finitely supported
polynomial ring with its evaluation universal property. Both dependency
records are usable Mathlib leaves. No dependency module or new definition
node is present or needed, and no notion is privately redefined.

Edge cases: `e = 0` gives the empty function module and empty sum, so only
the constant-algebra scalar-extension comparison remains. `d = 0` asserts
the variable-differential basis when Ω_{A/R} is zero. `A = R` recovers the
ordinary polynomial-ring basis lemma. The zero ring `A` is allowed; all
its modules here are zero and a basis indexed by any finite set is allowed,
so the implication remains valid. No characteristic is excluded and no
map is required to be injective. Independent universes `u` and `v` cover
arbitrary ring carriers; the finite index type introduces no universe
restriction. Empty schemes do not occur in this ring statement.

Independent searches run through msearch.py with this group and item:

- LeanSearch: `The module of differentials of an algebra with finitely many
  indeterminates adjoined is the sum of the extended coefficient differentials
  and the free variable differentials`. Service unavailable (Internal Server
  Error); this is not evidence of absence.
- LeanFinder: `differentials of adjoining indeterminates to an R-algebra split
  into scalar extension and coordinate derivatives`. Eight hits, principally
  `mvPolynomialBasis_repr_*`, `polynomial_D_apply`, `polynomialEquiv_comp_D`,
  and submersive-presentation differential maps. None states this decomposition.
- Loogle: `KaehlerDifferential, _ ≃ₗ[_] _`. Twelve hits, including
  `quotKerTotalEquiv`, `linearMapEquivDerivation`, `polynomialEquiv`, and
  `mvPolynomialEquiv`. I opened the polynomial equivalence and basis signatures:
  their base ring is the coefficient ring, so they cover Ω_{A[z]/A}, not
  the requested Ω_{A[z]/R}. They do not replace this statement.
- Mathlib `rg` for `direct.sum|prod|equiv|Equiv` in Kaehler/Polynomial.lean
  and TensorProduct.lean. I also opened `tensorKaehlerEquiv`: its target is
  Ω_{B/S} for a pushout, rather than the direct-sum decomposition over `R`.
- `rg` for `KaehlerDifferential.*(MvPolynomial|Polynomial)`,
  `differential.*polynomial`, and `exists_polynomial_extension_equiv` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository
  `lean/Sheaf`. Related projective-space and symmetric-algebra differential
  material exists, but no existing declaration of the node or name collision.

Conventions and documentation: the module and declaration docstrings name
the source and blueprint id. All six proof steps are present in order,
including the injectivity argument via `R[z]` and the finite-rank consequence,
with the same cited DAG nodes. The only theorem has proof `by sorry`; there
are no new definitions or proved auxiliaries. The namespace, file path,
explicit universes, imports and line widths follow the contract.

Validation: scompile.py on the absolute sandbox module path succeeded in
1.4 seconds, exit 0, with no warnings or errors. My initial invocation used
a relative path from the read-only repository and failed before compilation
with FileNotFoundError; the absolute-path rerun corrected that invocation.
I checked by eye that every variable and universe is bound, and checked the
node's `lean.statement` against the signature verbatim. The original module
and node are retained unchanged; this independent review and search record
are the only additions.
