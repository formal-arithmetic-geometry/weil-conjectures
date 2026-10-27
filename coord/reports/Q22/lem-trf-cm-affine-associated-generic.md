## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayAffineAssociatedGeneric` states
`AlgebraicGeometry.Scheme.Modules.associatedPoints_unit_spec_iff_minimalPrime_and_generic`.
Its proof is `sorry`; it introduces no definitions and proves nothing.
The node changes only in `lean`. No new nodes, dependency repairs, statement
corrections, or disputed statements are needed.

Hypothesis and clause correspondence:

- The commutative Noetherian ring T is `{T : Type u} [CommRing T]
  [IsNoetherianRing T]`, for an explicitly bound arbitrary universe `u`.
- For every prime ideal, `hcm : ∀ p : PrimeSpectrum T, ...` asserts the equality
  `(IsLocalRing.depth (R := Localization.AtPrime p.asIdeal)
  (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) =
  ringKrullDim (Localization.AtPrime p.asIdeal)`. PrimeSpectrum packages exactly
  a prime ideal and its primality proof, so this quantifies over all primes.
  Coercion to `WithBot ℕ∞` compares the recorded depth and dimension without
  truncating either. There is no extra finite dimension or domain hypothesis.
- W is exactly `Spec (CommRingCat.of T)`, whose underlying points are
  definitionally `PrimeSpectrum T`. The arbitrary point is `(q : PrimeSpectrum T)`.
- Condition (i) is `q ∈ Scheme.Modules.associatedPoints
  (SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)`.
  Mathlib's `SheafOfModules.unit` is the structure sheaf as its own module:
  its sections are the ring sections with multiplication as scalar action.
  The recorded `associatedPoints` definition asks that the stalk-ring maximal
  ideal lie in `RingTheory.annihilatorAssociatedPrimes` of this module stalk,
  using `RingedSpace.moduleStalkFunctor`. This is the node's exact element
  annihilator condition, without replacing it by the general radical-annihilator
  associated-prime predicate. An element with proper maximal annihilator cannot
  be zero, since zero has annihilator the whole ring; thus the node's explicit
  nonzero requirement is already implied.
- Condition (ii) is `q.asIdeal ∈ minimalPrimes T`: minimal among all prime ideals,
  as witnessed by Mathlib's `minimalPrimes_eq_minimals`. No closed-point condition.
- Condition (iii) is `∃ Z ∈ irreducibleComponents (Spec (CommRingCat.of T)),
  IsGenericPoint q Z`. This quantifies over exactly the scheme's irreducible
  components, with genericity `closure {q} = Z`. Component membership implies
  irreducibility and closedness; genericity implies membership of q in Z.
- The conclusion is `(i ↔ ii) ∧ (ii ↔ iii)`, logically exactly the asserted
  three-way equivalence, including every implication.

Statement dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-localization-at-prime | Mathlib.RingTheory.Localization.AtPrime.Basic | Localization.AtPrime |
| def-weil-pbc-depth | WeilConjectures.RingTheory.Depth | IsLocalRing.depth, Ideal.depth |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec |
| def-trf-relative-assassin | Sheaf.AlgebraicGeometry.RelativeAssassin | AlgebraicGeometry.Scheme.Modules.associatedPoints |
| def-weil-pbc-annihilator-associated-primes | WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes | RingTheory.annihilatorAssociatedPrimes (through associatedPoints) |
| def-weil-pbc-module-stalk | WeilConjectures.Topology.PresheafModuleStalkFunctor | PresheafOfModules.moduleStalkFunctor (presheaf interface); the scheme specialization used by associatedPoints is RingedSpace.moduleStalkFunctor |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible | irreducibleComponents |

Every recorded statement-dependency module is a public import. Plain proof imports
supply StructureSheaf.IsLocalization.to_stalk and the function-field clause of its
node, IsLocalization.isNoetherianRing, the finite-dimensional Noetherian local ring
instance, Ideal.mem_minimalPrimes_of_depth_ge, the localization order isomorphisms,
the two associated-prime localization/minimal-prime results, and
PrimeSpectrum.zeroLocus_minimalPrimes. These match all the recorded proof dependencies.
The docstring carries all four proof steps and their node identifiers.

Source read: local `literature/stacks-project/divisors.tex`, Tag 05DC,
`lemma-base-change-relative-assassin`, including its final CM associated-prime
argument; `algebra.tex`, Tags 0BUS (`lemma-CM-ass-minimal-support`),
05BV (`lemma-ass-minimal-prime-support`), and 05BZ (`lemma-localize-ass`).
Mathlib signatures/docstrings for every recorded statement dependency were read,
as were the upstream depth, annihilator-associated-prime and stalk modules and
the RelativeAssassin definition. No external source is needed.

Edge cases checked mathematically before writing:

- Zero ring: Spec is empty; the hcm quantifier is vacuous and there is no q,
  so no artificial nontriviality assumption is needed.
- A field: its zero prime has dimension and depth zero, is associated via 1,
  and is generic for the sole component.
- Dual numbers k[ε]/(ε²): the unique prime is minimal and is the annihilator
  of the nonzero element ε; reducedness would wrongly exclude this valid case.
- k[x]: the generic prime satisfies all three conditions; a nonzero prime is
  not associated because its positive-depth localization has no element with
  maximal annihilator, and it is neither minimal nor component-generic.
- k × k: both component generic points satisfy all three conditions.
- The CM assumption is substantive: k[x,y]/(x²,xy) has an embedded associated
  prime (x,y) (annihilator of x), which is not minimal. Its offending local ring
  has depth zero and positive dimension, so hcm excludes it.
- No restriction is imposed on characteristic, reducedness, irreducibility,
  equidimensionality, or global finite Krull dimension.

Searches actually run through msearch.py for this item:

- leanfinder: “Associated points of the spectrum of a Noetherian Cohen Macaulay
  ring are minimal primes and generic points of irreducible components”. Eight
  hits, including PrimeSpectrum.zeroLocus_minimalPrimes,
  PrimeSpectrum.vanishingIdeal_irreducibleComponents, quasiSober, and the
  field/fraction-ring associated-prime result; none states the entire item.
- loogle: `associatedPrimes, minimalPrimes`. Zero hits.
- grep: `Cohen.?Macaulay|associatedPrimes.*minimalPrimes|minimalPrimes.*associatedPrimes`.
  Two hits, the signature lines of
  Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes;
  this is only one direction and has no CM or structure-sheaf clause.
- leansearch: “Associated points of a Cohen Macaulay Noetherian affine scheme
  are exactly the minimal primes”. Eight hits: associatedPrimes, minimalPrimes,
  IsAssociatedPrime, the minimal-prime inclusion, zero-dimensional ring facts,
  minimalPrimes_eq_minimals, and the membership lemma. None is an exact match.
- rg of the live WeilConjectures and Sheaf algebraic-geometry/ring-theory trees:
  `associatedPoints|Cohen.?Macaulay|associated.*generic|associated.*minimal`.
  Found the local associated-prime theorem, existing CM applications and
  Scheme.Modules.associatedPoints. These give ingredients, not this equivalence.
- rg of all WeilConjectures and Sheaf:
  `associatedPoints.*iff|associatedPoints.*minimal|cm_affine|cmAffine` found only
  the distinct fibre-assassin open-containment/base-change theorem.
- rg of WeilConjectures for this node id found no existing declaration.
  The chosen declaration name was also absent from both Lean roots and
  dag/lean_names_upstream.json.

Validation: scompile.py compiled the module both in the sandbox and under its
library module name without errors or warnings (1.4 seconds each).

## Second reading by Q22

This is the assigned worker's second reading, not a claim of an independent
agent review: the dispatcher brief prohibits starting other agents and delegates
independent review to the maintainer. Reopening the node and final file, I checked
all binders and both conjuncts against the three conditions. The only subtle
encoding is condition (i): the recorded module-associated-point definition uses
an element annihilator, the unit module really is O_W, and properness forces its
witness nonzero. Condition (iii) quantifies over components of the actual Spec
scheme. The depth equality retains its full value in WithBot ℕ∞ and all primes.
No mismatch was found and no statement correction was made.
