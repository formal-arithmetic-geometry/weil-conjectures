## Worker report

Added `Sheaf.RingTheory.PopescuLifting`, stating `Algebra.popescu_lifting`, and the new definition node `def-weil-pbc-finitely-presented-algebra` using Mathlib's `Algebra.FinitePresentation`.

The theorem binds commutative rings `R`, `Λ`, `Cbar`, an `R`-algebra structure, Noetherianity of `R`, and `π`. The two annihilator equalities render the hypotheses on `π` and `π²`. The quotient-algebra map `j` renders `Cbar → Λ/π²Λ`; the conclusion supplies `D`, its ring/algebra structures, `D → Λ`, the quotient base algebra structure, and maps `ψ` and `c`. `Algebra.IsFinitelyPresented R D` is clause (a), `ψ.comp c = j` is diagram commutativity, and the three quantified smoothness clauses encode (b), (c), and (d) using `Algebra.IsSmoothAtPrime`.

Dependencies used: `Sheaf.RingTheory.SingularIdeal` (`Algebra.IsSmoothAtPrime`, blueprint `def-weil-pbc-singular-ideal`), and `Sheaf.RingTheory.FinitePresentedAlgebra` (`Algebra.IsFinitelyPresented`, new dependency node). The latter wraps Mathlib `Algebra.FinitePresentation`.

Edge cases checked include arbitrary universe levels, zero-variable presentations through Mathlib's polynomial formulation, and principal localizations at arbitrary elements. Searches: ripgrep for finite-presentation declarations in Mathlib, `WeilConjectures`, and `lean/Sheaf`; Mathlib source `RingTheory/FinitePresentation.lean`; no existing project declaration matched the node's notion. Server compilation with `scompile.py` passed for both modules.

## New nodes

`def-weil-pbc-finitely-presented-algebra` records the finite-presentation notion and its Mathlib implementation.

## Earlier second reading (a previous round; superseded)

The module and node were read independently after compilation. The binders render the rings, annihilator assumptions, quotient algebra structures, diagram map, finite-presentation conclusion, and smoothness clauses. No declaration uses an implicit variable. The quotient map `ψ` makes the compatibility equation well typed.

## Dependency modules

`def-weil-pbc-finitely-presented-algebra`: no prior project declaration existed for the blueprint notion. The delivered module states `Algebra.IsFinitelyPresented` as a named wrapper around Mathlib's `Algebra.FinitePresentation`; the dependency node records this reason.

## Second reading by H1

This is the independent second reading and supersedes the earlier round above. I opened
the base node, its three dependency nodes, the delivered modules, Mathlib's actual
finite-presentation class and Noetherian definition, and the landed SingularIdeal module.
The cited Stacks checkout is not present under this clone's literature directory; I read
the available Stacks sources at /home/ubuntu/c1-stacks-review/smoothing.tex,
Section The lifting lemma, label lemma-lifting (07CP), including its entire proof, and
algebra.tex definitions definition-finite-type (00F3) and definition-smooth-at-prime
(00TB). The source section has no ambient extra hypotheses. The base node agrees with
07CP; its statement has not been changed.

The node's objects, hypotheses, and conclusions, matched individually:

| Node item | Final Lean rendering | Verdict |
| --- | --- | --- |
| Commutative Noetherian ring R | `(R : Type a) [CommRing R] [IsNoetherianRing R]` | Exact; Mathlib's definition is Noetherianity of R as its own module, equivalently finite generation of every ideal. |
| R-algebra Λ | `(Λ : Type b) [CommRing Λ] [Algebra R Λ]` | Exact; no Noetherianity, finiteness, nonzero, or flatness assumption on Λ. |
| Element π of R | `(π : R)` | Exact. |
| Ann_R(π) = Ann_R(π²) | `hAnnR`, using the module annihilators of the two principal ideals | Exact; an element annihilates the principal ideal iff it annihilates its generator, as in Mathlib's `Submodule.mem_annihilator_span_singleton`. |
| Ann_Λ(π) = Ann_Λ(π²) for their images | `hAnnΛ`, with `algebraMap R Λ π` and `algebraMap R Λ (π ^ 2)` | Exact; algebraMap preserves multiplication and powers. |
| R/π²R → Cbar as an R-algebra map | `[Algebra R Cbar]`, `[Algebra (R ⧸ Ideal.span {π ^ 2}) Cbar]`, and `[IsScalarTower R (R ⧸ Ideal.span {π ^ 2}) Cbar]` | Exact; the tower expresses the required compatibility with the quotient map, rather than an extra mathematical restriction. |
| Cbar → Λ/π²Λ as an R-algebra map | `j : Cbar →ₐ[R] (Λ ⧸ Ideal.span {algebraMap R Λ (π ^ 2)})` | Exact; the target's R-algebra structure is the canonical quotient structure. Surjectivity of R → R/π²R forces compatibility over the quotient as well. |
| Cbar finitely presented over R/π²R | `[Algebra.FinitePresentation (R ⧸ Ideal.span {π ^ 2}) Cbar]` | Added the missing hypothesis, directly using the recorded dependency's Mathlib class. |
| R-algebra D and R-algebra map D → Λ | Existential `D`, its `CommRing` and `Algebra R D`, and `φ : D →ₐ[R] Λ` | Exact; these witnesses precede all required properties. |
| R-algebra map Cbar → D/πD | `c : Cbar →ₐ[R] (D ⧸ Ideal.span {algebraMap R D π})` | Replaced the arbitrary ring map by the required algebra map. This makes the left square commute with the canonical bottom structure map. |
| Induced bottom arrow D/πD → Λ/πΛ | `ψ`, with `ψ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp φ.toRingHom` | Fixed its codomain and tied it to φ. Surjectivity of the quotient projection uniquely determines ψ. |
| Canonical right vertical arrow Λ/π²Λ → Λ/πΛ and right-square commutativity | `red.comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _` and `ψ.comp c.toRingHom = red.comp j.toRingHom` | Exact. The equation uniquely specifies the reduction map; the square now compares the composites to Λ/πΛ, as in 07CP. |
| (a) D finitely presented over R | `Algebra.FinitePresentation R D` | Exact, with Mathlib's notion. |
| (b) R → D smooth at every prime not containing π | `∀ q : PrimeSpectrum D, algebraMap R D π ∉ q.asIdeal → IsSmoothAtPrime R q` | Exact. |
| (c) R → D smooth at primes containing π over the smooth locus of Cbar | Quantification over `PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π})`, smoothness at `PrimeSpectrum.comap c.toRingHom q`, and conclusion at `PrimeSpectrum.comap (Ideal.Quotient.mk _) q` | Exact; primes of this quotient correspond precisely to primes of D containing π. The smoothness premise is over R/π²R. |
| Map Cbar/πCbar → D/πD used in (d) | Existential `cmod` with `cmod.comp (Ideal.Quotient.mk _) = c.toRingHom` | Exact induced map; the quotient projection is surjective, so no free choice remains. |
| (d) That map is smooth at every prime over the same smooth locus | Last clause uses `@IsSmoothAtPrime ... cmod.toAlgebra q` with base Cbar/πCbar | Fixed the original clause, which incorrectly asserted smoothness over R/π²R. The base and the algebra structure now specify exactly the relative map of (d). |

Dependencies: SingularIdeal's `Algebra.IsSmoothAtPrime` was read at its definition:
it means an element outside the prime with a smooth principal localization, exactly
00TB. Mathlib's `Algebra.IsSmoothAt` instead means formal smoothness of the local ring,
so I did not substitute it. Noetherianity uses the recorded Mathlib `IsNoetherianRing`.
Finite presentation uses `Algebra.FinitePresentation` from
Mathlib.RingTheory.FinitePresentation, whose `out` gives finitely many polynomial
variables and a surjection with finitely generated kernel; `FinitePresentation.iff`
gives the quotient presentation of 00F3, including zero variables and zero relations.
All three dependency signatures are usable as recorded.

Edge cases: no `Nontrivial`, domain, field, characteristic, or nonempty-spectrum
hypothesis occurs. For π = 0 the quotient projections are isomorphisms, clause (b)
is vacuous, and (c), (d) retain their full meanings. For π a unit the quotient spectra
are empty and (b) covers all primes of D. The zero ring and zero quotient rings are
allowed; prime quantifiers are then empty when appropriate. Empty families and empty
schemes are not objects introduced in this ring-theoretic statement; empty spectra
and presentations with n = 0 or m = 0 are covered. The ring universes a, b, c are
independent. Changed the existential D from Type c to Type (max a c): the polynomial
construction over R has size max a c, so a large base ring is not excluded when Cbar
is small. No tests over a smaller universe or hidden implicit variables remain.

Independent searches (recorded in searches.jsonl):

- LeanSearch: `annihilator lifting finitely presented algebra smooth modulo square`:
  service returned Internal Server Error; recorded unavailable, not a no-match verdict.
- Loogle: `Algebra.FinitePresentation`: found the class and its quotient, self,
  polynomial, equivalence, and transitivity results. Opened the class at line 44
  and its quotient characterization; it is exactly the existing dependency notion.
- LeanFinder: `desingularization lifting algebra through quotient by pi squared
  preserving smooth locus`: returned StandardEtalePair.lift and smooth-at-prime
  standard-smooth/localization results. These assume different smoothness data and
  do not state this lifting lemma.
- msearch grep on all Mathlib: `07CP|popescu_lifting|annihilator.*lifting|lifting.*annihilator`:
  zero hits.
- Independent rg on WeilConjectures, lean/Sheaf, Mathlib's Smooth files, and upstream
  name records: `popescu`, `07CP`, `annihilator.*span`, `IsFinitelyPresented`,
  `finitely.presented`, and declaration searches for `IsSmoothAtPrime` and
  `Algebra.FinitePresentation`. No existing exact lifting theorem. The existing
  project smooth-at-prime predicate and Mathlib finite-presentation class are used.
- DAG search and direct opening found that def-weil-pbc-finitely-presented-algebra
  already exists on the base, with status mathlib and an exact mathlib_match.

Mismatches repaired: the finite-presentation hypothesis on Cbar was missing;
the independently supplied quotient algebra structures could disagree with the
R-actions; c was not an R-algebra map; ψ went to the wrong quotient and was unrelated
to φ; the right-square equation had the wrong target; (d) had the wrong base;
D's universe could exclude the construction; the theorem docstring lacked the
proof. The final module carries all eighteen node proof steps, including their
named dependencies, and the usual copyright header. Its only proof is `sorry`;
there are no definitions, extra lemmas, or proofs of compatibility hidden in data.
The quotient-map witnesses and defining equations avoid introducing helper notions
or proving anything in stage 2.

The supposed new finite-presentation node was not new: its base node already has the
usable Mathlib match, and its delivered replacement also omitted the finiteness of
the variable set and recorded no searches. The wrapper module duplicated Mathlib.
Removed both its sandbox node copy and its module instead of replacing a correct
base record. Also removed the duplicate finite-presentation entry in stmt_deps,
restoring exactly the base list. There are no new nodes or dependency modules in
the final delivery; the earlier sections describing those files are historical.
No node statement was corrected, and no unit statement changes.

Validation: scompile.py compiled the sole final module on the server in 1.8 seconds,
with no errors or warnings. Inspected all binders and the explicit last-clause
algebra structure; the lean.statement record is verbatim the final theorem signature.
