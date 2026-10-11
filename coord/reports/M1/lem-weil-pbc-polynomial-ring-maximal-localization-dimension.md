## Worker report

The module states that for a field `k`, a natural number `n`, and a maximal ideal
`M` of `MvPolynomial (Fin n) k`, the localization at `M` has Krull dimension
`n`.  The declaration is
`MvPolynomial.ringKrullDim_localizationAtMaximal` in
`lean/Sheaf/RingTheory/PolynomialRingMaximalLocalizationDimension.lean`.

The Lean rendering of each part of the node statement is as follows.  The field
is the binder `{k : Type u} [Field k]`; the integer `n ≥ 0` is `(n : ℕ)`; the
polynomial ring `k[x_1,\ldots,x_n]` is `MvPolynomial (Fin n) k`; and the maximal
ideal is `(M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal]`.  The localization
`P_M` is `Localization.AtPrime M`, and its Krull dimension is Mathlib's
`ringKrullDim`; the conclusion is the equality
`ringKrullDim (Localization.AtPrime M) = (n : WithBot ℕ∞)`.

The dependency declarations used in the statement are Mathlib's
`MvPolynomial` (module `Mathlib.Algebra.MvPolynomial.Basic`),
`Localization.AtPrime` (module `Mathlib.RingTheory.Localization.AtPrime.Basic`),
and `ringKrullDim` (module `Mathlib.RingTheory.KrullDimension.Basic`).  Their
DAG records are respectively `def-weil-pbc-mv-polynomial-ring`,
`def-weil-pbc-localization-at-prime`, and `def-weil-pbc-krull-dimension-ring`.
The import `Mathlib.RingTheory.KrullDimension.Polynomial` supplies these
transitively and is the only import needed by the module.

Edge cases checked: `n = 0` gives `MvPolynomial (Fin 0) k` and the conclusion
`ringKrullDim ... = 0`; the binder permits every natural `n`; maximal ideals are
prime via Mathlib's instance, so `Localization.AtPrime M` is defined.  No
nonempty-variable or algebraic-closedness assumption is added, and the zero
polynomial-ring case is included at `n = 0`.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
"localization at maximal ideal polynomial ring Krull dimension n" returned only
general localization and height declarations, with no exact local-dimension
statement.  The recorded node searches also used LeanSearch for "height of a
maximal ideal of a polynomial ring in n variables over a field equals n",
LeanFinder for "every maximal ideal of MvPolynomial (Fin n) k ... localization
at a maximal ideal has Krull dimension n", Loogle for
`Ideal.height, MvPolynomial`, and grep over Mathlib's Krull-dimension files and
`WeilConjectures`; these found global polynomial-ring dimension and localization-
height lemmas but no exact statement.  `rg` over the project found no existing
`ringKrullDim_localizationAtMaximal` declaration.  The source repository's
`MvPolynomial.height_eq_of_isMaximal` gives height `n`, which is a different
statement and does not duplicate this localization-dimension theorem.

## Second reading by M1

Read the sandbox node, its six proof steps, the Lean module, and all three
statement-dependency nodes and their recorded Mathlib declarations. The local
repository lacks the untracked Stacks checkout; I read the available Stacks
`algebra.tex` at `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 27648–27713
and 35833–35848, and verified `00OP,algebra-lemma-dim-affine-space` and
`00S9,algebra-definition-lci-field` in that checkout's `tags/tags`. The section
is explicitly about polynomial rings over fields. Tag 00OP's second assertion
is exactly this node; its generator and regular-local assertions are separate
assertions of the source and are not conclusions of this node.

Object, hypothesis, and conclusion checklist (all pass):

- Field k: `{k : Type u} [Field k]`; arbitrary universe u and arbitrary field,
  with no algebraic-closedness, perfection, or characteristic assumption.
- Nonnegative integer n: `(n : ℕ)`; precisely the nonnegative integers.
- P = k[x₁,…,xₙ]: `MvPolynomial (Fin n) k`. The dependency
  `def-weil-pbc-mv-polynomial-ring` records Mathlib `MvPolynomial`, whose
  Basic.lean:82 definition is `AddMonoidAlgebra k (Fin n →₀ ℕ)`; relabelling
  1,…,n by Fin n does not change the polynomial ring.
- Maximal ideal M of P: `(M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal]`.
  This quantifies over every maximal ideal, including non-rational closed
  points. No extra primeness hypothesis is imposed: Mathlib's
  `Ideal.IsMaximal.isPrime'` supplies it (Ideal/Maximal.lean:169).
- Localization P_M: `Localization.AtPrime M`, exactly the recorded declaration
  of `def-weil-pbc-localization-at-prime`. Its AtPrime/Basic.lean:57 definition
  is `Localization M.primeCompl`, the fractions at P minus M. The dependency's
  residue-field and fibre clauses are not needed for this signature.
- Krull dimension: `ringKrullDim`, exactly the recorded declaration of
  `def-weil-pbc-krull-dimension-ring`. Basic.lean:30 defines it as
  `Order.krullDim (PrimeSpectrum R)`; Order/KrullDimension.lean:78 takes the
  supremum of strict-chain lengths, with bottom and infinity included.
- Sole conclusion dim P_M = n: `ringKrullDim (Localization.AtPrime M) =
  (n : WithBot ℕ∞)`. The cast is the finite integer in the dimension codomain.
  Binders have the node's order k, n, M; no clause is omitted or added.

Edge cases: n = 0 is admitted, and Fin 0 is empty, so the polynomial ring is
k and its unique maximal ideal is zero; its localization is a field of
dimension zero. This is a zero-variable polynomial ring, not the zero ring
(the worker report's phrase “zero polynomial-ring case” should be read this
way). A field is nontrivial, so zero rings and empty spectra are outside the
node's hypotheses, not excluded by additional Lean assumptions. All
characteristics and all universes of fields are admitted; the finite index
set in Type 0 causes no universe restriction on k. Empty schemes and zero
modules do not occur in the node. All variables and the universe u are bound.

Independent searches, with different semantic wording from the worker:

- LeanFinder via msearch: “dimension of local ring at closed point of affine n
  space over arbitrary field”; eight hits, on presentation dimension,
  cotangent spaces, standard smoothness, and rank at stalks, no exact match.
- Loogle via msearch: `ringKrullDim, Localization.AtPrime, MvPolynomial`;
  zero hits.
- LeanSearch via msearch: “Krull dimension localization maximal multivariate
  polynomial ring field number of variables”; service returned Internal
  Server Error, recorded as unavailable, not evidence of absence. The node
  already records successful LeanSearch searches for this statement.
- rg over Mathlib's KrullDimension directory and Ideal/Height.lean, the entire
  source `WeilConjectures`, and the project's `lean/Sheaf`, using
  `height_eq_of_isMaximal`, `ringKrullDim.*[Ll]ocal`, `local.*ringKrullDim`,
  and `localizationAtMaximal`. Opened the source's
  `MvPolynomial.height_eq_of_isMaximal` at
  WeilConjectures/Mathlib/RingTheory/KrullDimension/Polynomial.lean:104:
  its conclusion is M.height = n, not this localization-dimension statement.
  Opened Mathlib `IsLocalization.AtPrime.ringKrullDim_eq_height` at
  Ideal/Height.lean:418: it is a general dimension-height bridge and does not
  assert height n. Opened the project's finite-type-domain dimension modules:
  they give common dimension or transcendence degree, not this exact value
  for polynomial rings. None is an exact existing declaration for this node.

No new nodes, dependency modules, or statement corrections are needed.
The signature and the node's `lean.statement` are unchanged and verbatim
identical. The sole theorem still has proof `by sorry`; there are no
hollow definitions or proofs added. The import supplies and is used by the
polynomial ring, localization, and dimension in the signature.

Mismatches repaired: the declaration docstring had a malformed duplicate
blueprint/source citation and only a compressed outline of the proof. I
replaced it with a clean citation and the six numbered node proof steps,
including their dependency identifiers, residue-field tower, coefficient-map
kernel induction, strict prime chain, and both dimension bounds. Removed the
unused `open scoped BigOperators`. The mathematical statement was right and
was not rewritten.

Validation: scompile.py compiled the repaired 59-line module on the server
with exit code 0 and no warnings. An initial docstring trailing-blank-line
warning was repaired before the clean compilation.
