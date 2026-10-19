## Worker report

The module `Sheaf.RingTheory.JTwoFiniteAlgebraCriterion` states
`isOpen_regularLocus_of_finite_algebras`, with `sorry` as its entire proof.
No definition is introduced and no mathematical statement is changed. The source is
Stacks, More on Algebra, Tag 07PC, lemma-J-2, implication (3) implies (1), with
J-1 and J-2 expanded by Tag 07P7. I read the source lemma and proof in
`literature/stacks-project/more-algebra.tex` and the item's complete six-step split.
The declaration docstring carries all six proof steps and their cited nodes.

The previous worker's stale-assignment diagnosis was incorrect. The ledger entry
at 2026-10-18 19:46 UTC and the item's `reviewed` record refer to N0's stage-1
split. The current node has no `lean` or `reviewed_lean` record. This delivery
provides its first stage-2 statement; it does not redeliver that stage-1 split.

Every hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| R is a commutative ring | `(R : Type u) [CommRing R]` |
| R is Noetherian | `[IsNoetherianRing R]` |
| For every commutative R-algebra B | `hfinite : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B], ...` |
| B is finitely generated as an R-module | `[Module.Finite R B]` in that universal hypothesis |
| The subset of Spec B where B localized at q is regular local | `{q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime q.asIdeal)}` |
| That subset is Zariski open | `IsOpen` applied to that subset in `hfinite` |
| For every finite type commutative R-algebra C | `(C : Type (max u v)) [CommRing C] [Algebra R C] [Algebra.FiniteType R C]` |
| The regular locus of C is open | `IsOpen {q : PrimeSpectrum C | IsRegularLocalRing (Localization.AtPrime q.asIdeal)}` |
| Equivalently R is J-2 | The conclusion is the expanded universal J-2 clause used in the existing `IsQuasiExcellent` definition; this adds no separate excellence or G-ring conclusion. |

`PrimeSpectrum B` is the underlying Zariski topological space of
`AlgebraicGeometry.Spec (CommRingCat.of B)`. Thus using it for the locus does not
replace Spec by a different topological space. Both the hypothesis and the
conclusion use the very same local regularity predicate. No reducedness, domain,
nontriviality, locality or characteristic hypothesis is imposed on R, B or C.
All variables and the universes `u v` are explicit, and `autoImplicit` is false.
The test algebras and the concluding algebra live in the same universe
`max u v`, at least that of R; the quantification cannot become vacuous through
an independently smaller universe. The declaration is uniform in both universes,
including `v = u` and arbitrarily larger algebra universes.

I read every statement dependency's full natural statement, Lean record and
relevant declaration signature/docstring. The interfaces reused are:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded
  `def-weil-pbc-noetherian-ring` predicate.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the recorded
  `def-weil-finitely-generated-module` predicate.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and its
  underlying `PrimeSpectrum`, as recorded by `def-weil-affine-spectrum`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  as recorded by `def-weil-pbc-localization-at-prime`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the
  unchanged ring clause of `def-weil-regular-scheme`'s `mathlib_match`.
  The recorded module `Sheaf.AlgebraicGeometry.IsRegularScheme` is also
  publicly imported; the theorem only uses that node's ring clause.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, the algebra-instance
  form in the `mathlib_match` of `def-weil-pbc-finite-type-algebra`.
  Its recorded `RingHom.FiniteType f` unfolds to exactly this predicate for
  `f.toAlgebra`; `RingHom.finiteType_algebraMap` explicitly relates the forms.
  No interface repair or private substitute is necessary.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, whose last conjunct
  is precisely the expanded universal J-2 conclusion, and `IsExcellent`.
  I read both definitions in full; the theorem asserts neither the additional
  G-ring clause nor universal catenarity.

The already stated proof dependencies are imported without `public`:
`Sheaf.RingTheory.JTwoResidueFieldCriterion` supplies
`isOpen_regularLocus_of_residueField_finite_models`;
`Mathlib.RingTheory.Noetherian.Basic` supplies `IsNoetherianRing.of_finite`;
`Mathlib.FieldTheory.PurelyInseparable.Basic` supplies `IsPurelyInseparable`.
The remaining proof dependencies are already statement dependencies. I read the
residue-field criterion's entire signature and proof docstring, and the two
Mathlib signatures, before writing the proof plan. No proof dependency import
was omitted for a cycle.

Edge cases checked before writing:

- R the zero ring: any unital R-algebra is the zero ring; both spectra are
  empty and the loci are open. There is no `[Nontrivial R]` binder.
- B or C the zero algebra over an arbitrary R: the regular locus is empty
  and therefore open. No assertion that the zero ring is regular local occurs.
- R a field, the identity algebra, and a finite field extension: their spectra
  have a single regular point. The general quantifiers retain these cases.
- Nonreduced R and B: their regular loci may be empty; the theorem only
  assumes openness and never requires nonemptiness for arbitrary B.
- The zero-generator finite type case C = R, polynomial algebras with at
  least one variable, and every characteristic are included. Module-finiteness
  of C is not assumed.
- In the proof plan, characteristic zero uses the identity residue-field
  model; positive characteristic includes exponent zero (`n_i = 1`). The
  regular generic point is invoked only for the domain models inside fields.

Searches made for an existing statement:

1. `msearch.py Q10 lem-per-j2-finite-algebra-criterion leanfinder
   "A Noetherian ring is J-2 if all its module-finite algebras have open regular locus"`:
   8 hits, concerning Orzech's property, Noetherian spectra, finite-type
   Noetherianity and smooth flatness. None has this hypothesis and conclusion.
2. `msearch.py Q10 lem-per-j2-finite-algebra-criterion loogle
   '"IsRegularLocalRing", "IsOpen"'`: zero hits.
3. `msearch.py Q10 lem-per-j2-finite-algebra-criterion grep
   "JTwo|IsJTwo|J2Ring|regularLocus" RingTheory`: zero Mathlib hits.
4. `rg -n "lem-per-j2-finite-algebra-criterion|isOpen_regularLocus|JTwo|IsJTwo|J2Ring|regularLocus"`
   on the source project's `WeilConjectures` and the shared project's `lean/Sheaf`:
   the source project has no hit. The shared library has the residue-field
   criterion and the prime-quotient criterion, both with different hypotheses;
   other hits are imports, consumers, or this item's citation in the proof
   docstring of `CompleteLocalExcellent`. None already states this criterion.
5. I also searched `J2|JTwo|regularLocus|j2_finite|jTwo` in the shared
   `lean/Sheaf/RingTheory` and upstream `WeilConjectures/RingTheory` and
   `WeilConjectures/Mathlib/RingTheory`; results add no exact declaration.

No new nodes, dependency repairs or statement corrections are needed.
There is no statement dispute. Only the item's `lean` field changes in its
node copy; the existing split and independent stage-1 review are preserved.

Validation: the prescribed `scompile.py` compiled the sandbox and library-module
forms in 3.1 and 2.1 seconds with no errors or warnings. The prescribed
`deliver2.py Q10 lem-per-j2-finite-algebra-criterion --no-push` printed
`OK (dry run): commit 942d6a52c1 passes the preflight and compiles; nothing pushed`.
A local data comparison confirmed that only `lean` changes in the node and
that every module line is at most 100 characters. The final delivery command
repeats the compile and preflight on this report.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
