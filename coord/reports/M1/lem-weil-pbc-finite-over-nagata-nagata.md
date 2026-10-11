## Worker report

The module `Sheaf.RingTheory.FiniteOverNagata` states the finite-algebra Nagata
lemma.  It uses the canonical ring map `algebraMap R S`; `[Algebra R S]` gives
that homomorphism and `[Module.Finite R S]` renders “S is a finitely generated
R-module”.  The hypothesis `hR : IsNagataRing R` renders that R is Noetherian
and every prime quotient is N-2.  The conclusion `IsNagataRing S` renders both
that S is Noetherian and that every prime quotient of S is N-2.  The clause
`∀ I : Ideal R, IsNagataRing (R ⧸ I)` is the stated quotient consequence,
including the zero and unit ideals.

The proof is `sorry`, as required for stage 2.  Its documented source route is
Stacks Tags 032T and 032I: contract a prime of S to R, pass to finite domain
quotients and their fraction fields, compare integral closures in finite field
extensions, and apply N-2 finiteness; then use that R → R/I is finite generated
by 1.

Dependencies used: `Sheaf.RingTheory.NagataRing`, declarations
`IsNagataRing`; Mathlib `Mathlib.RingTheory.Finiteness.Defs`, declaration
`Module.Finite`.  The Nagata and N-2 definitions are thereby used through the
recorded dependency declarations `IsNagataRing` and `IsN2` (the latter is
transitively imported by `NagataRing`).

Edge cases checked: `I = ⊥` gives R, `I = ⊤` gives the zero quotient; the
universal quantification over prime ideals includes all primes, and no domain,
finite type, or nonzero assumptions are added.  The finite module condition is
unrestricted and includes rank zero algebras.

Searches: `msearch.py ... leanfinder "finite algebra over a Nagata ring is
Nagata"` and `loogle "Nagata, IsNagataRing"` found no Mathlib declaration;
grep over Mathlib and WeilConjectures found no finite-over-Nagata theorem.
The project already contains the dependency definition
`lean/Sheaf/RingTheory/NagataRing.lean`; its declaration was read directly.
Mathlib `Module.Finite` was verified in `Mathlib/RingTheory/Finiteness/Defs.lean`.

## Earlier second reading (a previous round; superseded)

I reopened the node and module.  The `hR` hypothesis is exactly the node's
Nagata-ring assumption; `[Algebra R S] [Module.Finite R S]` render its specified
ring homomorphism and finite-module condition; and the conjunction contains
both the full Nagata conclusion for S and the explicit quotient clause for every
ideal I.  No prime, ideal, domain, or characteristic case is omitted, and the
proof remains `sorry`.  The signature compiled cleanly with only the expected
sorry declaration warning.

## Second reading by M1

I read the sandbox node and module, all four statement-dependency nodes and their
recorded declarations, and the Stacks source in
`/home/ubuntu/c1-stacks-review/algebra.tex`. Its tags table identifies 032T with
`lemma-quasi-finite-over-nagata`, 032I with
`lemma-quasi-finite-over-Noetherian-japanese`, 032R with `definition-nagata`, and
032F with `definition-N`. These labels and line numbers match the node's source
place. Sections Japanese rings and Nagata rings impose no unstated domain,
characteristic or nonzero hypothesis on the ring-map theorem: the domain
hypotheses belong to the prime quotients in its proof. Tag 032T explicitly includes
finite ring maps; the last paragraph of 032I proves precisely the finite-domain
case used here. No node-statement correction was necessary.

Object/hypothesis/conclusion checklist (H3):

- Object R: `(R : Type u) [CommRing R]`, an arbitrary commutative ring. PASS.
- Hypothesis R Nagata: `(hR : IsNagataRing R)`. I opened
  `Sheaf.RingTheory.NagataRing`: `IsNagataRing R` is exactly
  `IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
  IsN2 (R ⧸ p) (FractionRing (R ⧸ p))`. This is the recorded dependency
  `def-weil-pbc-nagata-ring` and Stacks 032R. PASS.
- Object S: `(S : Type v) [CommRing S]`, an arbitrary commutative ring, with
  independent universe v. PASS after repair of the original common universe u.
- Object φ : R → S: `[Algebra R S]` supplies `algebraMap R S`. For commutative
  rings any unital ring map supplies this algebra structure (via RingHom.toAlgebra),
  and its scalar action is multiplication by its image. Thus this represents every
  map in the node, with no injectivity, domain or centrality restriction added. PASS.
- Hypothesis S finitely generated as an R-module via φ: `[Module.Finite R S]`.
  I opened `Mathlib.RingTheory.Finiteness.Defs`: the class has exactly
  `fg_top : (⊤ : Submodule R S).FG`, and FG means span of a finite set.
  This is the recorded `def-weil-finitely-generated-module`, not finite cardinality
  and not just finite type as an algebra. PASS.
- Conclusion S Noetherian: the first conjunct of `IsNagataRing S` in the first
  outer conjunct. I opened `Mathlib.RingTheory.Noetherian.Defs`: the recorded
  `IsNoetherianRing` is Noetherianity as a module over itself, equivalently every
  ideal finitely generated (`isNoetherianRing_iff_ideal_fg`). PASS.
- Conclusion every prime quotient S/q N-2: the second conjunct of
  `IsNagataRing S`, quantifying every ideal with `[q.IsPrime]`. I opened the
  recorded `Sheaf.RingTheory.JapaneseDomain`: `IsN2 B K` quantifies finite field
  extensions L/K and asserts `Module.Finite B (integralClosure B L)`, with
  `[IsScalarTower B K L]` enforcing the composite algebra action. Here K is
  `FractionRing B`; the fraction-ring, domain and tower instances are the usual
  ones, not extra hypotheses of this theorem. PASS.
- Conclusion for every ideal I ⊆ R, R/I Nagata: the second outer conjunct
  `∀ (I : Ideal R), IsNagataRing (R ⧸ I)`. No prime/proper restriction on I and
  no existential choice; R, S and φ precede the hypotheses and this universal
  consequence. PASS.

Edge cases: zero rings are allowed by CommRing and no Nontrivial instance is
assumed; the zero ring has no prime ideals and is Noetherian. The zero S is a
finite R-module (empty generating family), so rank-zero cases are covered.
I = ⊥ and I = ⊤ are both included, the latter giving the zero quotient. The
prime-ideal quantifier is allowed to be vacuous. There is no characteristic
restriction or fixed positive dimension/rank. Independent `universe u v` now
allows different ring universes. The recorded N-2 definition tests extensions
in the fraction-field universe; finite extensions admit representatives there
by a finite-dimensional basis, so this does not omit a mathematical extension.
Empty schemes and unrelated index sets do not occur in this ring statement.

Independent H4 searches (2026-10-11), using words other than the worker's:

- `msearch.py M1 lem-weil-pbc-finite-over-nagata-nagata leanfinder
  "A module finite ring homomorphism preserves the Nagata property and prime
  quotients are Japanese"`: eight hits, including
  `RingHom.finite_of_algHom_finiteType_of_isJacobsonRing`,
  `RingHom.finite_iff_finiteType_of_isJacobsonRing`, and quasi-finite definitions;
  none is a Nagata/Japanese preservation theorem.
- `msearch.py ... loogle '"Nagata"'`: available, zero hits.
- `msearch.py ... leansearch "A finite algebra over a Noetherian Japanese Nagata
  ring is Nagata"`: service unavailable (Internal Server Error), not evidence
  of absence. LeanFinder, Loogle and direct source searches were available.
- `rg -n 'IsNagataRing|IsN2|finite_over_nagata|Japanese|Nagata ring'` over all
  Mathlib, WeilConjectures and repository lean/Sheaf found only the existing
  Nagata/Japanese dependency definitions and a complete-local Nagata theorem in
  Sheaf; no existing finite-over-Nagata theorem. Broader `nagata|japanese` searches
  also returned unrelated Nagata compactification/criterion references and
  Japanese brackets. The upstream names record has no declaration attached to
  this item. Therefore keep the new theorem module and use the existing notions.

Mismatches and repairs: the common `(R S : Type u)` was replaced by
`(R : Type u) (S : Type v)` with `universe u v`; the node's lean.statement was
updated verbatim. The original proof docstring was an outline omitting
Noetherianity, the localized finite-dimensional domain argument and much of the
closure comparison. I expanded it to all four node proof steps with their cited
DAG dependencies. I added the standard copyright/license/author header. The
mathematical node statement, dependencies, theorem name and conclusion are
unchanged. There are no new nodes, no dependency modules, no copied definitions
and no hollow definitions. The only proof is the theorem's `sorry`, as required
by stage 2. All binders and universes are explicit, both imports are used, and
all Lean lines are at most 100 characters.

Validation: `scompile.py M1 lem-weil-pbc-finite-over-nagata-nagata` compiled the
module on the server in 1.3 seconds with exit code 0 and no warnings. I also
removed the module docstring's unsupported numbered lemma reference, retaining
the exact stable Stacks tag 032T. `RingHom.toAlgebra` and its algebra-map and scalar
identities were opened in Mathlib.Algebra.Algebra.Defs to check the map encoding.
The delivery dry run passed the preflight and server compilation; the final dry
run below includes this source-reference cleanup.
