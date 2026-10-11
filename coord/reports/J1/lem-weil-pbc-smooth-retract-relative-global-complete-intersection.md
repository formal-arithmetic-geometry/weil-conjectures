## Worker report

The module `Sheaf.Paper.SmoothRetractRelativeGlobalCompleteIntersection` states the existence of
natural numbers `n,c`, a family of `c` polynomials in `MvPolynomial (Fin n) R`, the specified
relative global complete-intersection condition, a `Module.Basis` of the cotangent/conormal
module whose vectors are the equation classes, and `R`-algebra maps `σ` and `π` with
`π.comp σ = AlgHom.id R A`.  It also existentially supplies the `A`-algebra structure on the
quotient, identifies its structure map with `σ` on underlying ring homomorphisms, and states
`Smooth A C`.

The binders `(R : Type u) [CommRing R]` and `(A : Type v) [CommRing A] [Algebra R A]
[Smooth R A]` render the commutative rings, algebra structure, and smoothness hypotheses.
The existential `(n c : ℕ)` and `f : Fin c → MvPolynomial (Fin n) R` render the finite
presentation data.  `IsRelativeGlobalCompleteIntersectionPresentation f` is clause (1).
The `Module.Basis (Fin c) C J.Cotangent` and equality
`b j = J.toCotangent ⟨f j, Ideal.subset_span ...⟩` render clause (2), including the specified
classes.  The maps `σ : A →ₐ[R] C` and `π : C →ₐ[R] A`, their composition equation, and the
existential `Algebra A C` with structure-map equality and `Smooth A C` render clause (3), with
`C = MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)` and `J = Ideal.span (Set.range f)`.

Dependencies used are Mathlib's `Algebra.Smooth` (the recorded `def-weil-pbc-smooth-ring-map`),
Mathlib's `MvPolynomial` and evaluation/universal-property declarations (the recorded
`def-weil-pbc-mv-polynomial-ring`), and
`Algebra.IsRelativeGlobalCompleteIntersectionPresentation` from
`Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation` (the recorded
`def-weil-pbc-relative-global-complete-intersection`).  The conormal module is Mathlib's
`Ideal.Cotangent`.

Edge cases checked: `n = 0` and `c = 0` are allowed by `Fin n` and `Fin c`; the empty family
has its canonical empty basis.  The quotient may be the zero ring, and no nonemptiness or
inequality hypothesis is added.  Universes for `R` and `A` are explicit and independent.

Searches executed with `msearch.py`: LeanFinder query “smooth algebra is a retract of a
relative global complete intersection with free conormal basis” returned eight results,
including `Algebra.IsStandardSmooth`, `Algebra.Smooth`, `Algebra.smooth_iff`, and
`Algebra.FormallySmooth.iff_split_injection`, none stating this construction. Loogle query
`Algebra.Smooth, Ideal.Cotangent` returned zero hits. Mathlib grep `retract|complete intersection`
in `RingTheory/Smooth` returned conormal-splitting results in `Kaehler.lean`, completion
retracts in `Flat.lean`, and splitting results in `Basic.lean`, none giving the required
complete-intersection algebra. LeanSearch for “smooth algebra is a retract of a complete
intersection algebra with free conormal module” was unavailable (Internal Server Error).
`rg` for the item id, `smooth_retract_relative`, `complete intersection`, and `IsRelativeGlobal`
in `WeilConjectures/`, and for the item id and proposed name in `lean/Sheaf/` and
`dag/lean_names_upstream.json`, found no existing statement. Existing presentation definitions
and Mathlib's conormal module are used without duplication.

The local Stacks TeX is absent on this machine. The source was checked at
https://stacks.math.columbia.edu/tag/07CG: its smooth special case and its chosen conormal
basis give the three clauses. No statement fault or correction was needed.

## Earlier second reading (a previous round; superseded)

Pending the independently assigned second reader. This worker has checked the clause mapping
above but does not claim an independent second reading.

## Second reading by J1

I independently read the node statement, its Stacks source (Smoothing Ring Maps, Tag 07CG,
lines 567 and 580--588), and the Lean theorem
`Algebra.smooth_retract_relative_global_complete_intersection`.

- Objects and hypotheses: Lean binds commutative rings `R : Type u` and `A : Type v`, an
  `Algebra R A`, and `[Smooth R A]`, exactly the source's smooth `R → A` hypothesis. It
  introduces `n c : ℕ` and `f : Fin c → MvPolynomial (Fin n) R`, representing the finite
  polynomial variables and equations. No Noetherian, nonzero, finite-type, characteristic,
  or universe restriction is added.
- Clause (1): `IsRelativeGlobalCompleteIntersectionPresentation f` is the recorded specified
  presentation predicate for `C = MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)`, matching
  the source's relative global complete-intersection condition on every nonempty fibre.
- Clause (2): `Module.Basis (Fin c) C J.Cotangent` together with
  `b j = J.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩` says that the conormal
  module `J/J²` has precisely the equation classes as a free `C`-basis. `Ideal.Cotangent` is
  Mathlib's conormal module, so no private duplicate notion is introduced.
- Clause (3): the existential `σ : A →ₐ[R] C`, `π : C →ₐ[R] A` and
  `π.comp σ = AlgHom.id R A` render the `R`-algebra retraction. The nested existential
  `[Algebra A C]` with `(Algebra.ofId A C).toRingHom = σ.toRingHom` makes the stated
  `A`-algebra structure exactly the one induced by `σ`, and `Smooth A C` gives the required
  smoothness over `A`.

Quantifier order agrees with the node: presentation data precedes all three clauses, and the
maps precede the existential `A`-algebra structure. The theorem leaves the proof as the single
named `sorry` required at stage 2 and introduces no hidden `let`, local notation, or private
copy. The edge cases `n = 0`, `c = 0`, an empty equation family, and a zero quotient are all
allowed by `Fin`, `Ideal.span`, and the existential formulation; no fibre nonemptiness is
assumed globally. Independent universes `u` and `v` are appropriate for the two rings.

I searched Mathlib's Smooth and Cotangent modules, the source `WeilConjectures/` tree, the
project's `lean/Sheaf/` tree, and `dag/lean_names_upstream.json` for the construction and its
conceptual variants (smooth retract, complete intersection, conormal basis). Only Mathlib's
`Algebra.Smooth`, `MvPolynomial`, and `Ideal.Cotangent`, plus the project's recorded
`IsRelativeGlobalCompleteIntersectionPresentation`, were relevant; no existing theorem states
this result. The existing dependency declaration is imported rather than redefined.

No mismatch was found, so no statement or dependency change was needed. The module compiled
cleanly with `scompile.py`; the only diagnostic permitted by the contract is the theorem's
proof `sorry`.
