## Worker report

The module `Sheaf.RingTheory.JZeroFiniteTypeDomainDescent` states
`RingHom.exists_nonempty_regular_open_of_finiteType`, with the sole proof `sorry`.
It defines no new notion. The node copy changes only `lean`.

### Statement correspondence

- The commutative ring `R` is `(R : Type u) [CommRing R]`.
- Noetherianity is `[IsNoetherianRing R]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`.
- The base is a nonzero integral domain by `[IsDomain R]`. Together with `CommRing`,
  this supplies exactly nontriviality and the zero-product condition in the node.
- The target is `(S : Type v) [CommRing S] [IsDomain S]`, again a nonzero domain.
- The ring homomorphism is `(f : R →+* S)`; injectivity is
  `(hinj : Function.Injective f)`.
- The finite-type condition is `(hft : f.FiniteType)`. Mathlib's `RingHom.FiniteType`
  is `Algebra.FiniteType R S` for precisely `f.toAlgebra`, not an independently chosen
  algebra structure. Thus the hypothesis concerns the same map as `hinj`.
- The existence of the open `V` is the existential in `hS`, with
  `V : Set (PrimeSpectrum S)`, `IsOpen V`, and `V.Nonempty`.
- At each prime `q ∈ V`, regularity of the prime localization is exactly
  `IsRegularLocalRing (Localization.AtPrime q.asIdeal)`. Its prime instance comes from
  the point `q`; the class includes Noetherianity, locality, and the dimension condition.
- The conclusion uses `∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ ...`.
  Its last clause is `∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)`.
  There is no restriction to principal opens or added requirement relating `U` to `V`.

`PrimeSpectrum A` has the Zariski topology and is definitionally the underlying space
of the recorded `AlgebraicGeometry.Spec (CommRingCat.of A)`:
`Spec.topObj` is `TopCat.of (PrimeSpectrum A)`. The node only uses the topology and
prime localizations of this spectrum. No alternative spectrum or regularity predicate
is introduced. The independent, explicit universes `u v` allow rings of different sizes.

### Recorded dependency declarations

Read the dependency nodes and the full signatures/docstrings of the declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg` (all ideals finitely generated).
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` and `RingHom.FiniteType`
  (the latter unfolds to the former for `f.toAlgebra`).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  its underlying-space construction `Spec.topObj` was read in
  `Mathlib.AlgebraicGeometry.Spec`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, the
  quotient localization at the prime complement.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, `IsRegularRing`.
  Only the exact ring clauses of `def-weil-regular-scheme` are needed here.

All five statement-dependency modules are public imports. The already recorded proof
modules are ordinary imports: `Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness`
(`Module.noetherian_algebra_module_generic_freeness`),
`Sheaf.RingTheory.LocalizationOfRegularRing` (`RingTheory.isRegularRing_of_localization`),
and `Sheaf.RingTheory.RegularRingFaithfullyFlatDescent`
(`IsRegularRing.of_faithfullyFlat`). Mathlib proof imports provide the basic-open basis
and localization correspondence, localization away, freeness, tensor products, and
faithful flatness. Finite-type Noetherian permanence is in the public finite-type module.
The theorem docstring carries every step of the node's seven-step natural-language proof
and identifies the dependency nodes used by each step.

### Source and edge cases

The local Stacks TeX files are absent. Read the source online:
[Tag 07PA](https://stacks.math.columbia.edu/tag/07PA) and
[Tag 07P7](https://stacks.math.columbia.edu/tag/07P7).
Their hypotheses and the expanded meaning of J-0 agree with the node. No statement
correction, disputed statement, dependency module, or new node is needed.

Checked before writing:

- Zero rings are excluded by each domain hypothesis, as the node explicitly requires.
  In particular the empty spectrum and an empty purported regular open cannot satisfy
  the hypotheses; `V.Nonempty` and the conclusion's `U.Nonempty` remain explicit.
- A field and the identity inclusion satisfy the intended dimension-zero case; no
  positive-dimension, proper-open, or non-field hypothesis has been imposed.
- Finite type permits zero algebra generators, including identity maps and finite
  quotient presentations. It does not mean finite as a module.
- A nonempty regular open is not assumed to be the entire regular locus or to be the
  image/preimage of another open. The conclusion promises only the required existence.
- `S` is not separately assumed Noetherian: it follows from the given Noetherian base
  and finite type. No faithfulness, flatness, or nonzero-rank hypothesis is added.
- The proof's generic-free basis may be infinite. Its index set is nonempty because
  the localized target is nonzero; the docstring retains the coordinate argument for
  faithful flatness rather than inferring it for a possibly zero free module.

### Searches

All service searches used `msearch.py Q28 lem-exc-j0-finite-type-domain-descent`.

1. LeanFinder query: "An injective finite type map from a Noetherian integral domain
   to a domain with a nonempty regular open subset implies the base has a nonempty
   regular open subset". Eight hits, including `exists_integral_inj_algHom_of_fg`,
   `fg_of_fg_of_fg`, and geometric germ-injectivity facts. Their displayed signatures
   do not assert this regular-open descent theorem.
2. Loogle query: `IsRegularLocalRing, PrimeSpectrum, RingHom.FiniteType`.
   Zero hits.
3. LeanSearch query: "J-0 descends along an injective finite type map of domains".
   Eight irrelevant finite-support/injective-map hits; no match.
4. Mathlib grep query: `JZero|J_0|J0|j0|regularLocus|regular_locus`, under `RingTheory`.
   Sixteen hits involving graded-ring projections and local variables; no match.
5. Direct `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for J-0, regular-locus, regular-open, and finite-type-domain descent names found
   no declaration of this theorem. Searching the exact node id found only the proof
   citation in `Sheaf.RingTheory.JTwoResidueFieldCriterion`; reading that module showed
   its declaration is the different J-2 criterion. No declaration in the upstream
   project names this node.
6. Direct exact-name searches for `exists_nonempty_regular_open_of_finiteType` and
   `JZeroFiniteTypeDomainDescent` across Mathlib, the upstream project, the side sources,
   and the upstream-name index returned no match before creating the module.

### Validation

The declaration is checked with `set_option autoImplicit false` and explicit universes.
The module has the required source/blueprint docstrings, only a named theorem with a
whole `sorry` proof, and no line exceeding 100 characters. Compilation and delivery
preflight use only the prescribed `scompile.py` and `deliver2.py --no-push` wrappers.
The independent second reading is left to the next worker.

## Second reading by Q28

I independently opened the DAG node, its sandbox Lean module, all five statement-dependency
records and their Mathlib declarations. I also read the three imported project proof modules.
No mathematical or Lean mismatch was found, so the Lean file and node record are retained
verbatim. This reading adds only this report section.

Source check: read the Stacks `more-algebra.tex` directly from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
including the opening of `section-singular-locus`, `definition-J` (07P7), and
`lemma-J-0-goes-down` (07PA), and checked the corresponding tag pages
https://stacks.math.columbia.edu/tag/07PA and
https://stacks.math.columbia.edu/tag/07P7. The section defines the regular locus by regularity
of prime localizations; 07PA assumes precisely a Noetherian domain R, an injective finite-type
map, and a domain S satisfying J-0. The Noetherianity required to speak of J-0 for S follows
from finite type over R, so its omission as an independent Lean binder is exact.

My object/hypothesis/conclusion checklist, in the node's order:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative base ring R | `(R : Type u) [CommRing R]` | Exact; no field assumption. |
| R Noetherian | `[IsNoetherianRing R]` | Exact, the recorded abbreviation; every ideal is finitely generated. |
| R a nonzero integral domain | `[IsDomain R]` | Exact; this class includes `Nontrivial` and multiplicative cancellation away from zero. |
| Commutative nonzero domain S | `(S : Type v) [CommRing S] [IsDomain S]` | Exact, with independent universe. |
| Spec R and Spec S | `PrimeSpectrum R`, `PrimeSpectrum S` | Exact underlying topological spaces of the recorded affine spectra. `Spec.topObj` is `TopCat.of (PrimeSpectrum R)`. No scheme structure is used by this statement. |
| Ring map R to S | `(f : R →+* S)` | Exact unital ring homomorphism. |
| Injectivity of this map | `(hinj : Function.Injective f)` | Exact. |
| Finite type of this same map | `(hft : f.FiniteType)` | Exact: `RingHom.FiniteType` unfolds to the recorded `Algebra.FiniteType` for `f.toAlgebra`. No unrelated algebra instance is assumed. |
| A nonempty open V in Spec S | `hS : ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ V.Nonempty ∧ ...` | Exact existential hypothesis. |
| Every prime q in V has regular-local S_q | `∀ q ∈ V, IsRegularLocalRing (Localization.AtPrime q.asIdeal)` | Exact recorded localization and regular-local classes, including the prime instance from q. |
| A nonempty open U in Spec R exists | `∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ ...` | Exact existential conclusion. |
| Every prime p in U has regular-local R_p | `∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)` | Exact; neither a restriction to principal opens nor an extra relation to V. |

I read `IsRegularLocalRing` in Mathlib: it extends `IsLocalRing` and
`IsNoetherianRing` and equates maximal-ideal span finrank with Krull dimension. This is exactly
the ring clause of `def-weil-regular-scheme`; its scheme-level clause is not needed. The
localization is the recorded quotient construction at the prime complement. Thus all notions
are shared dependency declarations, with no private copy or missing interface. The delivery
contains no new definition node or dependency module; H12/H13 require no extra files.

Edge cases: zero rings and empty spectra are excluded by the node's domain assumptions,
exactly as by Lean's domain classes. Empty V is excluded by `V.Nonempty`, and the conclusion
explicitly excludes empty U. Fields, dimension zero, identity maps and zero algebra generators
are allowed. There is no characteristic restriction, finite-field assumption, positive-rank
assumption, chosen index set, flatness assumption or bound on the dimension. Both ring
universes are explicitly bound and independent; prime spectra and their localizations stay in
the respective ring universes. No implicit universe equality restricts the theorem.

Independent searches (2026-10-16), using vocabulary different from the first writer:

- LeanFinder via `msearch.py`: "A generically regular finite type domain over an injective
  Noetherian domain has a generically regular base". Read all eight returned signatures:
  finite generation in towers, geometric reducedness, Noether normalization, quasi-finiteness,
  and Noetherian gluing; none is this statement.
- Loogle via `msearch.py`: `IsRegularLocalRing, IsOpen, Function.Injective`; zero hits.
- LeanSearch via `msearch.py`: "Nonempty regular locus descends through a finite type inclusion
  of integral domains". Eight hits on going down, subrings of domains, prime zero loci,
  integral-scheme sections and localization inhabitation; none is this theorem.
- Direct `rg` across Mathlib RingTheory/AlgebraicGeometry, upstream `WeilConjectures`, and
  project `lean/Sheaf`: `generically.regular`, regular/open/locus combinations, J-zero/J-0,
  and regular/finiteType combinations. Hits concern regular elements, graded degree-zero
  projections, regular schemes over perfect fields or unrelated Koszul statements. No
  existing regular-open descent theorem was found. The related project localization,
  faithful-flat descent and generic-freeness theorems have different conclusions and are
  correctly imported as proof tools.

H5/H6/H8/H9: there are no definitions, instances or auxiliary theorems in the delivered module;
its sole named theorem has exactly `by sorry`. Its declaration and module docstrings cite
07PA/07P7 and the correct blueprint id. The declaration docstring reproduces all seven node
proof steps, including the localization identifications and the nonempty infinite-basis
argument for faithful flatness. Public imports supply each statement dependency, ordinary
imports supply the stated proof tools. All lines are at most 100 characters. Explicit
`universe u v` and `autoImplicit false` leave no unbound variables. I mechanically compared
the signature from `theorem` through the conclusion against `lean.statement`: verbatim equal.

Validation: `scompile.py Q28 lem-exc-j0-finite-type-domain-descent` on the delivered file
compiled both sandbox and library module successfully (5.5 s and 2.8 s), with no errors or
warnings. No statement correction or citer audit was necessary. No mismatch was repaired;
this second reading preserves the correct statement and adds its independent evidence.
