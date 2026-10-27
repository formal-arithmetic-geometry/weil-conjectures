## Worker report

The module `Sheaf.RingTheory.PrincipalAdicHomomorphismLift` states
`AlgebraicGeometry.exists_principal_adic_homomorphism_lift` with `sorry`.
The source read was restricted.tex, equation (NL), lines 260–285, and
Tag 0AK7, lemma-get-morphism-principal, lines 1075–1130. The explicit
nullhomotopy is exactly the specialization in the node; no Ext assumption
has been introduced. The full seven-step DAG proof is in the theorem docstring.

Hypotheses and clauses, read against the node:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- The element and finite number of variables: `(a : A) (q : ℕ)`, with variables
  indexed by `Fin q`; no positivity condition on q.
- The completed polynomial quotient R: `rigPolynomialCompletion A
  (Ideal.span {a}) q ⧸ L`, with L an arbitrary ideal. The abbreviation uses
  `AdicCompletion` of `MvPolynomial (Fin q) A` along the extended ideal.
- Completeness of R: `IsAdicComplete (Ideal.span {a}) R`, the A-module form
  equivalent to completeness along its extended ideal in R.
- The canonical continuous-derivative conormal differential: the landed
  `rigJacobianDifferential (Ideal.span {a}) q L`, using Mathlib `L.Cotangent`
  for L/L² and finite tuples for the finite direct sum R^q.
- The nonnegative exponent h and R-linear map H are `(h : ℕ)` and the
  explicitly quotient-linear `H : (Fin q → R) →ₗ[R] L.Cotangent`.
- The identity delta H = a^h id is `hδH`; the identity H delta = a^h id is
  `hHδ`. Both are pointwise identities using the image of a in R and its h-th power.
  Equality at every element is exactly equality of the two composite maps with
  scalar multiplication on the identity; it adds no condition and drops none.
- T is any commutative complete A-algebra, with independent universe v:
  `(T : Type v) [CommRing T] [Algebra A T] [IsAdicComplete (Ideal.span {a}) T]`.
  T is not assumed Noetherian.
- The nonnegative torsion threshold is `(t : ℕ)`. `ht` says every x killed
  by some nonnegative power of a and lying in `(span {a_T})^t` is zero.
  This is precisely T[a^infinity] intersect a^t T = 0; k=0 is included.
- The exact bound is `(n : ℕ) (hn : max (2 * h) (h + t) < n)`.
  The source's nonnegative power n is represented by Nat; the inequality
  already forces it positive.
- The initial map is `ψ : R →ₐ[A] T ⧸ (span {a_T})^n`.
- The conclusion supplies `φ : R →ₐ[A] T`; its reduction modulo the
  `(n-h)`th power is pointwise equal to the reduction of ψ. The latter
  reduction is the canonical `Ideal.Quotient.factor` using
  `Ideal.pow_le_pow_right (Nat.sub_le n h)`. Pointwise equality is exactly
  equality of the two algebra homomorphisms. Since n>2h, Nat subtraction
  agrees with the integer exponent n-h in the source.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the module-finite
  generation condition for every ideal (`isNoetherianRing_iff_ideal_fg`).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, finite sums of
  monomials. `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (compatible
  quotient sequences) and `IsAdicComplete` (separated and precomplete).
  `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the ring and
  canonical A-algebra structures.
- Landed dependency `Sheaf.RingTheory.CompletedPolynomialConormal` (group Q147):
  `rigPolynomialCompletion`, `rigPartialDerivative`, `rigJacobianDifferential`.
  The statement dependency list gains the existing node
  `def-per-completed-polynomial-conormal`, now with a usable Lean record on
  the base. Its full module was read during this repair. The conormal map is
  the literal quotient lift of continuous derivatives reduced modulo L.
  It is recorded as A-linear; the two identities are therefore expressed
  pointwise while H remains R-linear. No second definition is delivered.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent` and
  `Ideal.toCotangent` supply L/L² and its quotient map.

The proof dependency `lem-per-completed-polynomial-taylor-evaluation`
currently has neither a Lean record nor an upstream audit declaration, so
there is no proof module to import. It is not needed to type this statement.
The other proof dependency is the adic-completion definition already imported.

Edge cases checked mathematically: q=0 is the empty tuple module, without an
extra inhabitance condition. h=0 gives the required two inverse identities.
t=0 forces a-power torsion to vanish in all of T. a=0 and a a unit are allowed;
for a a unit, completeness forces the complete target to be the zero ring,
which is not excluded by a Nontrivial assumption. L=top, the zero base ring,
and the zero target ring remain meaningful. The strict inequality eliminates
n=0 and ensures n-h>0. For the landed dependency, I=0 gives the original polynomial
ring, I=top gives zero completion, and J=top gives the zero quotient and zero
conormal. The derivative choice is unique even in these cases.

Searches actually run with the prescribed msearch.py wrapper:

1. LeanFinder: “Lift an algebra homomorphism modulo a principal ideal power
   using a power nullhomotopy of the conormal differential”: eight results,
   including formally smooth lifting and `IsAdicComplete.mk_liftAlgHom`.
   They require formal smoothness or an already compatible family, so none
   is this bounded-precision lifting statement.
2. Loogle: `AdicCompletion, LinearMap`: twelve hits about the completion map,
   its bijectivity and linear induction; no conormal lifting theorem.
3. Grep: `pderiv|derivation|conormal` in RingTheory/AdicCompletion: zero hits.
4. LeanSearch: “Continuous partial derivatives and conormal differential
   of an adically completed polynomial ring”: eight hits, including polynomial
   differentiation but no completed conormal arrow.
5. Loogle: `Ideal.Cotangent, LinearMap`: twelve hits, including
   `Ideal.Cotangent.lift`, `Ideal.toCotangent`, and conormal transport;
   no completed-polynomial derivative or conormal arrow.
6. Grep: `rigJacobianDifferential|rigPolynomialCompletion|completedPderiv`:
   zero Mathlib hits.
7. Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for those three names and
   `principal_adic_homomorphism_lift`: zero hits. Direct grep for the item id
   in `lean/WeilConjectures`: zero hits. Broader completed-polynomial/continuous
   derivative searches found the local-ring calculus and formal-power-series
   Jacobian presentations; their rings and topology are different.
8. DAG search found `def-per-completed-polynomial-conormal`, whose
   `lean_removed` explicitly says its old module was deleted as dead code.
   `scompile.py --source Sheaf.RingTheory.CompletedPolynomialConormal`
   returned “Module source unavailable”. That was the state at the returned
   head. During this repair the module is present on the base with Q147's
   Lean record, and is used directly instead of restoring it again.

Validation is rerun for the repaired single module through scompile.py and
both deliver2.py modes. The previous delivered head was 7fd85bac8622; the
current base node retains the original mathematical statement and three
original dependencies. The only new dependency remains the conormal node,
which now has its recorded module on the base. No statement correction or
statement_change is needed. All universes and variables are explicit
(`autoImplicit false`), and the theorem proof remains `sorry`.

## Repair of return (b)

The returned head added `def-per-completed-polynomial-conormal` before that
node had a Lean record on its base. Its restored module could not qualify as
a permitted newly added existing dependency. On the current base, Q147 has
landed the node's module and Lean record (dated 2026-10-24). I read that
module in full and removed the sandbox's duplicate conormal module and node
file. This delivery changes only the item's node and its theorem module,
plus this report. The addition now cites a landed node with a Lean record,
as required by brief-stage2 §5. To use the landed A-linear conormal interface,
I replaced the old composite linear-map equalities by their identical
pointwise equalities, preserving H's R-linearity and both nullhomotopy
identities. The item node was refreshed from the current shared base before
reapplying just its permitted dependency addition and Lean record. This is a
source/interface repair and removal of a redundant module, not an unchanged
re-push. No dependency record is altered and no new definition is introduced.

## Second reading by N5

This is the author's separate second pass, not an independent agent review;
the dispatcher expressly prohibits starting agents. I reopened the current
item, the landed Q147 conormal module, and the repaired theorem module.
The theorem retains the strict bound `max (2*h) (h+t) < n`, the two
nullhomotopy identities, and the original torsion condition. No Noetherian
or nonzerodivisor condition is imposed on T. H remains linear over the
quotient ring R; the canonical differential is the exact landed quotient
lift on L.Cotangent. The pointwise identities express delta(H x)=a^h x
and H(delta x)=a^h x on their respective domains, so no R-linearity
hypothesis was weakened by using the landed A-linear arrow. The conclusion
compares canonical reductions at n-h on every element of the same R.
The finite tuple representation covers zero variables. Relative to the
returned head, the only interface mismatch was the conormal arrow's scalar
ring and implicit A binder; both are fixed by using its recorded signature
and pointwise identities. The duplicate dependency module and node record
are removed. No mathematical statement or source text was changed.
