## Worker report

The module `Sheaf.RingTheory.FormallyEtalePowerStep` states
`Ideal.formallyEtale_powerStep`, with one postponed theorem and no new definitions.
The source read was Stacks algebra.tex, Tag 0H1D,
`lemma-formally-etale-lift-infinitesimal`, including its dotted-arrow proof.
The seven proof steps of the DAG node are reproduced in the theorem docstring.
The node's natural-language statement and dependency lists are unchanged.

Hypothesis-by-hypothesis correspondence:

- Commutative rings A and C are `{A : Type u} {C : Type v}` with `[CommRing A]`
  and `[CommRing C]`. Their universes are independent.
- The ring homomorphism phi is encoded by `[Algebra A C]`, with phi equal to
  `algebraMap A C`. Every commutative-ring homomorphism supplies exactly this
  algebra structure by `RingHom.toAlgebra`; this does not restrict phi.
- The ideals are `(I : Ideal A) (J : Ideal C)`. The kernel condition is
  `hI : I = J.comap (algebraMap A C)`, since the kernel of reduction modulo J
  after phi is its inverse image of J. Surjectivity of that composite is `hsurj`.
- The square-zero lifting hypothesis is `hlift`: for every commutative A-algebra E
  and ideal N, `N ^ 2 = ⊥` implies bijectivity of postcomposition with
  `Ideal.Quotient.mkₐ A N` on `C →ₐ[A] E`. Test algebras live in `Type (max u v)`,
  Mathlib's size convention for the equivalent infinitesimal lifting property
  (`Algebra.FormallyEtale.iff_comp_bijective`). Smaller test algebras, including
  both quotients used in the proof, are covered by universe lifting; the test
  universe is not an unrelated smaller universe making the hypothesis vacuous.
- The integer n at least one is `(n : ℕ) (hn : 1 ≤ n)`. Positive integer ideal
  powers are exactly the positive natural powers; no admissible exponent is lost.
- The canonical map f_m is written directly as `Ideal.quotientMap (J ^ m)
  (algebraMap A C)` with containment from `hI.le`, `pow_le_pow_left'`, and
  `Ideal.le_comap_pow`. This map sends `[a]` to `[phi a]` by its definition.
- The chosen inverse g_n is `g : C ⧸ J ^ n →+* A ⧸ I ^ n`. `hleft` and `hright`
  are its two inverse identities for the canonical f_n. This is exactly the
  given isomorphism-with-inverse assumption, not an additional assumption that
  g is A-linear; that compatibility follows from the two identities.

Clause-by-clause correspondence:

- `∃ ell : C →ₐ[A] A ⧸ I ^ (n + 1)` supplies the A-algebra lift.
- The first equality composes its underlying ring map with
  `Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))`, the canonical
  r_n, and equates this to `g.comp (Ideal.Quotient.mk (J ^ n))`.
- The next quantified clause asserts that EVERY A-algebra lift satisfying this
  same equation equals ell; uniqueness is for the lifting equation itself.
- `∀ j, j ∈ J → ∃ a, a ∈ I ∧ Ideal.Quotient.mk (I ^ (n+1)) a = ell j`
  expresses ell(J) contained in the image I/I^(n+1) of I in A/I^(n+1).
- `∀ c, c ∈ J ^ (n+1) → ell c = 0` expresses killing J^(n+1).
- The existential `gnext` is the induced ring homomorphism on C/J^(n+1): its
  composite with the canonical quotient is explicitly ell's underlying map.
  This characterization uniquely determines gnext because the quotient is
  surjective, and also forces its A-algebra compatibility. Thus no arbitrary
  comparison map is substituted for the induced map.
- The next two equalities are `gnext.comp f_(n+1) = RingHom.id _` and
  `f_(n+1).comp gnext = RingHom.id _`, using canonical `Ideal.quotientMap` terms.
- The final equality is `r_n.comp gnext = g.comp s_n`; both reductions use
  `Ideal.Quotient.factor` and the canonical ideal-power containment.
- There are no finite-type, Noetherian, nonzero-ring, proper-ideal, or J=IC
  assumptions. No extra conclusion about a different object is asserted.

Dependency used: `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf, with no
project Lean record required. Its recorded declarations were read:
`AlgHom` (Mathlib.Algebra.Algebra.Hom, structure and docstring),
`Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ` and its surjectivity/kernel
properties (Mathlib.RingTheory.Ideal.Quotient.Operations), and ideal
multiplication and powers (Mathlib.RingTheory.Ideal.Operations, including the
IdemCommSemiring instance). The single public import of
`Mathlib.RingTheory.Ideal.Quotient.Operations` provides these and the canonical
`Ideal.quotientMap`, `Ideal.Quotient.factor`, and `Ideal.le_comap_pow` APIs.
There are no other proof dependency modules to import.

Edge cases checked mathematically: n=1 gives the usual square-zero kernel
I/I²; I=A and J=C give zero quotient rings and the unique maps between them;
J=0 gives I=ker phi and the same argument. The example k→k×k, a↦(a,a), with
J=0×k has J²=J and I=0; ell and all g's are the first projection and all
identities hold although J≠IC. Localization Z→Z[1/2] with J=(3) also satisfies
exactly these hypotheses. Neither zero rings nor positive characteristic are
excluded. No statement dispute, correction, or dependency fault was found.

Searches actually run with msearch.py for this item:

- LeanFinder: "A formally etale algebra map inducing inverse quotient maps modulo
  nth ideal powers has a unique lift of the inverse modulo the next powers
  compatible with reduction". Eight hits, including
  `Algebra.FormallyEtale.comp_bijective`, `.iff_comp_bijective`,
  `Algebra.FormallyUnramified.lift_unique`, and standard-etale lift results.
  They provide the lifting property or individual uniqueness, not this entire
  power-step statement.
- Loogle: `"Algebra.FormallyEtale", "comp"`. Three hits: `.comp`,
  `.comp_bijective`, `.iff_comp_bijective`; no exact match.
- Grep of Mathlib RingTheory:
  `(FormallyEtale|formallyEtale).*(quotient|pow)|quotient.*(FormallyEtale|formallyEtale)`.
  One hit in Etale/Basic.lean at the localization formally-etale instance,
  not the statement being formalized.
- LeanSearch: "Unique lifting of an inverse between ideal power quotients along
  a formally etale algebra with factorization and reduction compatibility".
  Eight hits, including general lift uniqueness and `Ideal.Quotient.liftₐ`,
  none the complete statement.
- rg of both project source trees for
  `lem-sfb-formally-etale-power-step|[Ff]ormally[Ee]tale|formally_etale`
  found no exact match. Read the existing
  `Sheaf.RingTheory.FormallyEtaleAssociatedGraded` in full: its main theorem is
  the downstream all-level/associated-graded result, not this chosen inverse's
  unique lift and the requested identities. Its helper `powerQuotientMap` is
  the same canonical Mathlib construction, so this module uses Mathlib directly
  and defines no duplicate helper. Importing the downstream theorem would
  invert the item's dependency direction.
- rg of both project source trees and dag/lean_names_upstream.json for
  `formallyEtale_powerStep` found no name collision. Read quotientMapₐ,
  liftₐ and factorₐ too when choosing the existing canonical ring-map APIs.

Validation: every compile uses the prescribed scompile.py wrapper against the
published server library. The single delivered module compiled cleanly on the server as both
the sandbox probe and `Sheaf.RingTheory.FormallyEtalePowerStep`; no errors or
non-sorry warnings were reported. The delivery dry run follows this compile.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
