## Worker report

The module `lean/Sheaf/Algebra/FiniteProjectiveTorAcyclic.lean` states
`CategoryTheory.finiteProjective_tor_acyclic`. It uses Mathlib's
`CategoryTheory.Tor'` in `ModuleCat R`, which is the declaration recorded by
the dependency node `def-weil-pbc-tor-modules`.

The hypotheses are rendered as follows: `R`, `A`, and `B` are commutative
rings with `Algebra R A` and `Algebra R B`; `P` is an additive commutative
group with an `A`-module structure; `hTor` says `IsZero` of the `i`th Tor
object for every natural `i` with `0 < i`; `m` is finite; `s` and `r` are
`A`-linear maps between `P` and the finite free module `Fin m -> A`; and
`hsplit` says `r.comp s = LinearMap.id`. The conclusion installs the induced
restricted `R`-module structure on `P`, passed explicitly to `ModuleCat.of` as
`Module.compHom P (algebraMap R A)`, and says the corresponding Tor object of
`P` with `B` is zero for every positive `i`. This is exactly the node's finite
projective direct-summand and Tor-acyclicity clauses.

Dependency declaration used: `Mathlib.CategoryTheory.Monoidal.Tor`,
`CategoryTheory.Tor'` (via the `mathlib_match` on
`def-weil-pbc-tor-modules`). No project dependency module is imported because
the dependency is a Mathlib leaf.

Edge cases checked: `m = 0` is allowed (`Fin 0 -> A`), `i = 0` is excluded by
the explicit `0 < i` hypothesis, and no nonempty or positive-rank condition is
imposed on `P` or the finite free module. The universe is shared by the
`ModuleCat R` representation required by Mathlib; no mathematical object is
restricted beyond the node's commutative-ring and module hypotheses.

Searches made: LeanFinder query “finite projective module direct summand Tor
vanishing from Tor independent algebras” returned no Tor-independence theorem;
Loogle query “Tor, Module.Projective, direct summand” returned zero hits and
reported unknown `Tor`; grep of Mathlib for `Tor.*direct summand|Tor.*finite
projective` returned no matches; LeanSearch query “finite projective direct
summand Tor vanishing under Tor independent algebras” was unavailable with an
Internal Server Error. The recorded Mathlib `CategoryTheory.Tor'` declaration
was used rather than defining a duplicate Tor notion.

No `STATEMENT-DISPUTED` or node fault.

## Earlier second reading (a previous round; superseded)

The node and module were read together. Every ring, algebra, module, finite
rank, split-map, positivity, and zero-Tor clause has a corresponding explicit
Lean binder or conclusion. The explicit restricted scalar action only supplies
the canonical structure needed to express the node's Tor over `R`; it adds no
hypothesis.
The zero-rank and positive-degree edge cases are preserved. No mismatch was
found.

## Second reading by H1

I independently opened the item node and `FiniteProjectiveTorAcyclic.lean`,
the sole statement dependency `def-weil-pbc-tor-modules`, and the Mathlib
sources `CategoryTheory/Monoidal/Tor.lean`, `CategoryTheory/Abelian/LeftDerived.lean`,
and `Algebra/Category/ModuleCat/{Basic,Monoidal/Basic,Abelian,Projective}.lean`.
The Stacks checkout in this repository has no downloaded TeX. I read the
available copies `/home/ubuntu/c1-stacks-review/perfect.tex`, lines 5144--5214
(`lemma-compare-base-change`, Tag 08IB), and `algebra.tex`, lines 18215--18270
(`section-tor`, Tag 00LY, and `lemma-tor-welldefined`). The affine paragraph of
08IB assumes only commutative algebras R -> A and R -> R' and positive-degree
Tor vanishing. The quasi-compact/quasi-separated assumptions of its scheme
base-change theorem are not assumptions of this elementary module lemma.
The node extracts a finite-summand consequence of that affine Tor condition;
it does not purport to restate the entire scheme theorem.

The node's objects, hypotheses, and conclusion, matched individually:

1. A commutative ring R: `{R : Type u} [CommRing R]`. Exact.
2. Commutative R-algebras A and B: `{A : Type u} [CommRing A] [Algebra R A]`
   and the corresponding B binders. Their R-module structures are induced by
   their algebra maps. Exact; no field, Noetherian, finite-type, flatness,
   nonzero-ring, or characteristic assumption is added.
3. The usual Tor modules, computed by a projective resolution in the first
   variable: `((Tor' (ModuleCat R) i).obj M).obj N`. Exact: `Tor'` is the
   flip of the left-derived right-tensoring functor, and
   `ProjectiveResolution.isoLeftDerivedObj` computes it as homology of the
   chosen resolution tensored with N. The tensor object in ModuleCat is the
   ordinary R-module tensor product. This is the dependency's recorded
   Mathlib match, not a private definition or Tor derived in the wrong factor.
   Abelian, monoidal-preadditive, and projective-resolution instances are
   supplied by Mathlib for all commutative rings, with no extra binder.
4. Tor_i^R(A,B) = 0 for every i > 0: `hTor : ∀ (i : ℕ), 0 < i → IsZero ...`
   with `ModuleCat.of R A` and `ModuleCat.of R B`. Exact. In ModuleCat,
   `IsZero` means the zero module, independently of a choice of zero carrier.
5. An A-module P: `{P : Type u} [AddCommGroup P] [Module A P]`. Exact.
   Its underlying R-action is explicitly `Module.compHom P (algebraMap R A)`
   in the conclusion; no independent, potentially incompatible R-action or
   extra scalar-tower assumption is imposed.
6. P is a direct summand of A^m for some finite m: `(m : ℕ)`,
   `(s : P →ₗ[A] (Fin m → A))`, `(r : (Fin m → A) →ₗ[A] P)`, and
   `(hsplit : r.comp s = LinearMap.id)`. Exact. Universal quantification over
   witnesses states precisely the implication from existence of such a
   splitting, since the conclusion is independent of m, s, and r. Finite
   functions represent the finite free module, including rank zero.
7. Tor_i^R(P,B) = 0 for every i > 0: the final `∀ (i : ℕ), 0 < i → IsZero ...`
   with P restricted to R and B. Exact; the same base ring and variable order
   are used. There is no requirement on degree-zero Tor.

Edge cases: m = 0 (the empty finite index set) is included; its split condition
forces P to be zero. Zero P and zero rings/algebras are allowed. Arbitrary
characteristics are allowed. i = 0 is deliberately outside both vanishing
clauses, as in the node. Schemes and empty schemes are not objects of this
module-level statement. `u` is explicitly bound and arbitrary, not fixed to
Type 0; all objects are represented in one ambient universe as required by
Mathlib's ModuleCat monoidal structure. Collections initially in different
universes can be represented in a common larger universe by lifts; no
cardinality, smallness, or universe-level hypothesis is added to the theorem.
No free variable or implicit universe remains unbound.

Independent searches, using vocabulary different from the first worker:

- LeanFinder, “Higher derived tensor vanishes for a retract of a finite power
  of a Tor independent algebra”: returned `CategoryTheory.isZero_Tor'_succ_of_projective`
  and the corresponding Tor and Rep results, among unrelated ring results.
  I opened Tor.lean: the candidate assumes P projective over R. Our P is
  projective over A, which need not be projective over R, so it is not a match.
- Loogle, `CategoryTheory.Tor', CategoryTheory.Limits.IsZero`: one hit,
  `CategoryTheory.isZero_Tor'_succ_of_projective`, rejected for the same reason.
  Earlier escaped-apostrophe and substring queries were ineffective and
  were superseded by this correctly spelled query.
- Logged grep, `\bTor.*(retract|biprod|directSum|finite|summand)|(retract|biprod|directSum|summand).*\bTor`
  under Mathlib/CategoryTheory: no matches. The first broader case-insensitive
  query matched unrelated words like “functor” and “factor”; it was superseded
  by the word-boundary query. Direct rg of the project's lean/Sheaf and
  WeilConjectures for Tor, tor_acyclic, torAcyclic, and tor_independent found
  Tor-amplitude and opcycle criteria, not this finite A-summand statement.
  The proposed full name does not occur in upstream Lean or Mathlib or
  dag/lean_names_upstream.json.
- LeanSearch, “Tor independence is inherited by a module which is a retract
  of a finite free algebra module”: service returned Internal Server Error,
  recorded as unavailable, not a no-match verdict.

No new definition nodes or dependency modules are present or needed: the sole
Tor dependency's Mathlib realization is usable. There is no statement_change
and no correction to the node's mathematics. No hollow definition is present;
the only theorem still has proof `by sorry`, as stage 2 requires.

Mismatches repaired: H8, the theorem docstring only summarized the two proof
steps and omitted how tensor and homology commute with the finite resolution
sum, and why the split maps give zero Tor. I expanded both steps completely,
including their Tor-definition dependency. H9, the standard copyright/license
header was missing; I added it. I removed the redundant explicit ModuleCat.Basic
import (already supplied by the used monoidal and projective imports).
The remaining imports provide Tor, the tensor structure, the abelian structure,
and enough projectives. The signature was left intact and checked verbatim
against lean.statement; every line is at most 100 characters.
The repaired file compiled cleanly with scompile.py (exit 0, 1.4 seconds),
with no warnings. The mathematical statement passed this independent reading.
