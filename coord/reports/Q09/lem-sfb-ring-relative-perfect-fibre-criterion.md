## Worker report

The module `Sheaf.RingTheory.RelativePerfectFibreCriterion` states
`DerivedCategory.finiteTorAmplitude_iff_boundedBelow_and_residueFibres_boundedBelow`.
It contains one theorem, with proof `sorry`, and no definitions or auxiliary theorems.
Only the item's `lean` record is changed. No statement correction or new node is needed.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0GHJ,
`lemma-bounded-on-fibres-relatively-perfect`, statement and entire proof
(lines 22204–22252 in this checkout). Its R-perfect condition is finite Tor dimension
under the already assumed pseudo-coherence. The node's expanded proof is reproduced
step by step in the theorem docstring.

Hypotheses and clauses:

- Commutative rings R and A and the homomorphism R → A are
  `{R A : Type u} [CommRing R] [CommRing A] [Algebra R A]` with structure map
  `algebraMap R A`. Algebra structures on commutative rings specify arbitrary unital
  ring homomorphisms; no injectivity is assumed.
- Flatness is `_hflat : (algebraMap R A).Flat`; finite presentation is
  `[Algebra.FinitePresentation R A]`. Both are the exact recorded Mathlib notions.
- Unbounded ordinary module derived categories are `DerivedCategory (ModuleCat.{u} R)`
  and `DerivedCategory (ModuleCat.{u} A)`, with explicitly bound independent localization
  universes `wR` and `wA` in their `HasDerivedCategory` instances. There is no bounded
  derived-category restriction, universe equality, or Noetherian assumption.
- The object is `C : DerivedCategory (ModuleCat.{u} A)` and pseudo-coherence is
  `_hpc : IsPseudoCoherent C`. Its existing definition is exactly a bounded-above
  finite-free model isomorphic to C in D(A).
- Restriction to the base is
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj C`.
  This exact functor applies ordinary restriction termwise and then localizes.
- Condition (1) is `∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat.{u} R) a b ...`.
  The existing `torAmplitudeIn` quantifies over every `N : ModuleCat.{u} R`, puts N
  in degree zero by `singleFunctor ... 0`, and requires derived tensor cohomology
  concentrated in [a,b]. Its `homologyConcentratedIn` is `IsGE a ∧ IsLE b`;
  Mathlib's `DerivedCategory.isGE_iff` and `isLE_iff` identify this exactly with
  vanishing for j < a or b < j. The a,b existential precedes every test module.
- Condition (2), first clause, is `∃ c : ℤ, ∀ j : ℤ, j < c → IsZero (H^j C)`;
  `homologyFunctor (ModuleCat.{u} A) j` is H^j. The term `homology` uses the
  cochain grading ℤ, so this is lower, not upper, boundedness.
- Every prime is quantified by `∀ p : PrimeSpectrum R`. The residue module is
  `ModuleCat.of R p.asIdeal.ResidueField`. Mathlib's `Ideal.ResidueField` is the
  residue field of `Localization.AtPrime p.asIdeal` and has an
  `IsFractionRing (R ⧸ p.asIdeal)` instance. It therefore supplies exactly the
  node's k(p) and its canonical R-action, with no extra choice or hypothesis.
- The fibre clause is `∀ p, ∃ c, ∀ j, j < c → IsZero (H^j (... ⊗ k(p)[0]))`.
  The tensor is the existing K-flat derived tensor on D(R), applied to restriction
  of C. Testing its vanishing in D(R) is equivalent to testing in D(k(p)):
  exact restriction of scalars retains the same cohomology module and reflects zero.
  Only vanishing is asserted; no residue-field-linear map or additional structure
  is discarded from a conclusion. The bound c is inside `∀ p`, so can depend on p.
- The equivalence is `↔`, and the two clauses of (2) are joined by `∧`.
  Neither direction is weakened. No nonzero-ring, finite-dimensionality, or uniform
  primewise bound is added.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined by `Module.Flat` for the
  scalar structure of the homomorphism; `RingHom.flat_algebraMap_iff` confirms the
  algebra-map specialization.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, whose data
  assert a surjection from a polynomial ring in finitely many variables with FG kernel.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`, the localization at quasi-isomorphisms.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, which says tensoring on each side preserves
  quasi-isomorphisms. This recorded dependency is publicly imported; the derived
  tensor construction below is built from precisely this K-flat machinery.
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- The existing `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` supplies
  `DerivedCategory.torAmplitudeIn`; `...HasMonoidalDerivedCategory` and
  `...GrothendieckAbelian.Monoidal.FlatResolution` supply the existing K-flat derived
  tensor and ordinary-module instances. No private tensor or Tor predicate is introduced.
- Mathlib's `ModuleCat.restrictScalars`, `CategoryTheory.Functor.mapDerivedCategory`,
  `DerivedCategory.singleFunctor`, `DerivedCategory.homologyFunctor`,
  `PrimeSpectrum`, and `Ideal.ResidueField` provide the remaining standard constructions.

The module imports every available recorded proof-dependency module, using plain imports:
`Mathlib.Algebra.MvPolynomial.Basic`,
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
`WeilConjectures.RingTheory.FlatModuleAtPrime`,
`Sheaf.RingTheory.BoundedPseudoCoherentStalkwisePerfect`,
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`, and
`Mathlib.Algebra.Module.Projective`. Flatness, finite presentation and pseudo-coherence
are already public imports. The proof dependencies
`lem-sfb-flat-fp-quotient-pseudocoherent`,
`lem-weil-pbc-polynomial-ring-field-regular-ring`, and
`lem-sfb-regular-fibre-local-perfect` have no recorded Lean modules in the read checkout;
they are named in the proof docstring and need no interface to state this theorem.

Edge cases checked before writing and on the second pass:

- C = 0: choose [0,0] on the left; C and all fibres vanish in every degree.
- R = 0: its spectrum is empty and every unital R-algebra A is zero. The fibre
  quantifier is correctly vacuous and C is zero, so both conditions still hold.
- A = 0 with R arbitrary: C and all its derived fibres are zero.
- Identity map R → R and a field base are included. No positive-degree or
  characteristic restriction is present, and a complex shifted into any integer
  degree is allowed by the existential integer bounds.
- Different lower bounds at different primes are explicitly permitted. No bound
  on C is inferred merely from the fibre condition: its separate lower bound remains.
- The single common universe u for rings and modules is an ambient universe choice;
  any given pair of small rings can be placed in a common universe. Test modules
  inhabit this same universe, which contains R and its residue fields, so the
  universal module test cannot become vacuous by choosing a smaller universe.
- Independent `wR` and `wA` compile, so the statement imposes no identification of
  localization universes to obtain the tensor or the exact restriction functor.

Searches made:

1. `msearch.py ... leanfinder` with query
   "A pseudo coherent complex over a flat finitely presented algebra has finite Tor
   dimension over the base iff it and all derived residue fibres are bounded below":
   eight hits, concerning smoothness/ordinary flatness or ordinary Tor; no equivalent
   derived pseudo-coherent fibre criterion.
2. `msearch.py ... loogle '"torAmplitudeIn"'`: zero hits in the Mathlib search service.
   Source search finds the project's existing predicate, used above rather than copied.
3. `msearch.py ... grep 'relative.*[Pp]erfect|[Pp]erfect.*[Ff]ib[r]?e|torAmplitudeIn'`:
   seven Mathlib hits, all relative perfect closures of fields, not this assertion.
4. `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for relative perfection,
   fibre criteria, `torAmplitudeIn`, derived tensor, and derived restriction of scalars
   find the existing pseudo-coherence and Tor predicates and related theorems, including
   the bounded stalkwise perfection proof dependency. None states this criterion.
5. Exact item-id search in `lean/WeilConjectures`, the upstream name index, and
   `coord/repair-notes` finds no existing binding or released repair for this item.
   The proposed full declaration name has no collision in Mathlib or either source root.
6. The prescribed CompactObject example is withdrawn in the current checkout
   (`/-! Withdrawn: no declarations remain. -/`); its node has no usable Lean record.
   The module header and record follow the current stage-2 brief and landed statement
   modules instead.

Validation: prescribed `scompile.py Q09 lem-sfb-ring-relative-perfect-fibre-criterion`
compiled both sandbox and library module cleanly (1.7 s and 2.2 s); no errors or
non-sorry warnings. `autoImplicit` is disabled; all variables and universe levels
are explicitly bound. One named theorem remains postponed, as required for stage 2.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q09

Re-read the DAG statement and the complete generated signature after compilation.
This was a second pass by the same worker; the dispatcher prohibits starting other
agents and the maintainer performs the independent review of this delivery.
Matched commutative rings and arbitrary algebra map, flatness, finite presentation,
unbounded D(A), pseudo-coherence, a ≤ b and all test modules in (1), and both the
global lower bound and prime-dependent residue lower bounds in (2). Checked that
`IsZero` applies to module objects (not bare types), that the fibre coefficient
carries the canonical R-action, and that restriction forgets only scalar structure,
not cohomology. Checked the definitions of `torAmplitudeIn`, `homologyConcentratedIn`,
`IsPseudoCoherent`, `Ideal.ResidueField`, and `mapDerivedCategory` in their source files.
The parentheses express precisely (1) ↔ ((global bound) ∧ (all fibre bounds)).
No mismatch was found and no statement or dependency record was changed.
