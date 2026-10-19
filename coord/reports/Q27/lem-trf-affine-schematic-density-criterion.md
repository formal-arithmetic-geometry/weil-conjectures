## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSchematicDensityCriterion` states
`AlgebraicGeometry.affine_schematic_density_criterion`, with its only proof `sorry`.
The docstring carries all five proof steps of the node, including the empty-family case.
No definition, helper theorem, or statement correction is required.

The source was read directly in `literature/stacks-project/algebra.tex`,
`lemma-when-injective-covering` (Tag 0565), and `morphisms.tex`,
`example-scheme-theoretic-closure` (Tag 056C) and
`lemma-characterize-scheme-theoretically-dense` (Tag 01RE).
The source tag-to-label records were checked in `tags/tags`.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| An arbitrary commutative ring A | `(A : Type u) [CommRing A]`, with explicit universe `u` and no nontriviality assumption |
| n >= 0 and f_1,...,f_n in A | `(n : ℕ) (f : Fin n → A)`; the shift from labels 1,...,n to Fin n is canonical reindexing |
| A_f = A[1/f] and its canonical ring map | `Localization.Away (f i)` and `algebraMap A (Localization.Away (f i))` |
| Natural map A to the finite direct sum of A_f_i | `fun a : A ↦ fun i : Fin n ↦ algebraMap A (Localization.Away (f i)) a` |
| Map a to (f_1*a,...,f_n*a) in A^n | `fun a : A ↦ fun i : Fin n ↦ f i * a` |
| Injectivity of those maps is equivalent | The first parenthesized `Function.Injective ... ↔ Function.Injective ...` |
| D(f_i) = primes not containing f_i | `PrimeSpectrum.basicOpen (f i)`, whose definition is exactly this set |
| U is the union of these opens in Spec A | `⨆ i : Fin n, PrimeSpectrum.basicOpen (f i)`, with ambient scheme specified as `Spec (.of A)` |
| j is the canonical open immersion of U | The canonical immersion of this open is implicit in the existing predicate `SchematicallyDenseOpen`; it is not an arbitrary morphism or an extra hypothesis |
| Injectivity of O_Spec(A) to j_* O_U is equivalent to the preceding conditions | The second conjunct equates localization-tuple injectivity with `SchematicallyDenseOpen (Z := Spec (.of A)) ...` |

Finite direct sums are represented by their canonically isomorphic finite products of
coordinates. This is the same additive map under that identification, including n = 0;
no infinite-family claim is substituted. The conjunction `(P ↔ Q) ∧ (P ↔ R)` asserts
exactly the three conditions' equivalence and supplies each explicitly.

Dependency declarations inspected and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`. The declaration constructs the affine locally ringed
  space as a scheme; its carrier is `PrimeSpectrum A`.
- `def-weil-ring-localization-away`: `Localization.Away`, in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, defined as localization at `Submonoid.powers`.
  The ring and canonical algebra-map structures come from
  `Mathlib.RingTheory.Localization.Away.Basic`, imported publicly.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`, the locally-ringed-space open-immersion predicate.
  It is available through the public import of `SchematicallyDenseOpen`.
- `def-trf-schematically-dense-open`: `AlgebraicGeometry.SchematicallyDenseOpen`, in
  `Sheaf.TraceFormula.SchematicallyDenseOpen`. This landed definition says that for every
  open W the actual restriction map `Z.presheaf.map (homOfLE inf_le_left).op` from W to
  W intersect U is injective. Its full definition and docstring were read: it is exactly
  the sheaf-injectivity condition here, with the canonical open immersion. Its existing
  node is added to `stmt_deps`, as authorized for reuse of landed notions; it is unchanged.
- Proof dependency `lem-weil-pbc-affine-open-section-vanishing-prime` is a Mathlib match:
  `Scheme.evaluation_eq_zero_iff_notMem_basicOpen` in
  `Mathlib.AlgebraicGeometry.ResidueField`; `IsAffineOpen.fromSpec_preimage_basicOpen`,
  `IsAffineOpen.fromSpec_primeIdealOf`, `IsAffineOpen.basicOpen`, and
  `IsAffineOpen.isLocalization_basicOpen` in `Mathlib.AlgebraicGeometry.AffineScheme`;
  `PrimeSpectrum.mem_basicOpen` in `Mathlib.RingTheory.Spectrum.Prime.Topology`.
  Their full signatures and surrounding docstrings were read. `ResidueField` imports the
  affine-scheme material and is imported without `public` for the future proof.
- Proof dependency `lem-weil-pbc-spec-localization-away-basic-open` is a Mathlib match:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`, `localization_away_isOpenEmbedding`, and
  `localization_away_comap_range`, in `Mathlib.RingTheory.Spectrum.Prime.Topology`, imported
  without `public`. Their signatures establish the basic-open basis and localization image.

Edge cases checked mathematically before writing:

- n = 0: both tuples have singleton underlying codomain (the zero additive group), so
  injectivity is equivalent to A being subsingleton. The union is empty; restriction to
  the empty subscheme is injective on every open exactly for the zero ring's empty spectrum.
- A the zero ring: Spec A is empty, all localizations and tuple sources are subsingleton,
  and every condition holds. No `[Nontrivial A]` binder excludes this case.
- Every f_i = 0, or all f_i nilpotent: the union is empty and all localizations are zero;
  multiplication-tuple injectivity forces A = 0, in agreement with both other conditions.
- One f_i is a unit: that coordinate makes both algebra maps injective, and the union is
  the whole spectrum, whose restriction is the identity.
- Zero divisors are permitted, with no claim that each coordinate is injective: in Z/6,
  f = (2,3) jointly gives injective tuples although each multiplication coordinate fails.
  In Z/4 with f = (2), all three conditions fail.
- The arbitrary ring universe is retained; the finite index introduces no independent
  universe restriction or vacuous test-family condition.

Searches made using `msearch.py Q27 lem-trf-affine-schematic-density-criterion`:

1. LeanFinder, query `For finitely many elements f_i of a commutative ring A, injectivity
   of A to product A[1/f_i] is equivalent to injectivity of multiplication by the tuple
   f_i and schematic density of the union of D(f_i)`: eight hits, including
   `PrimeSpectrum.toPiLocalization_injective`, `MaximalSpectrum.toPiLocalization_injective`,
   `Localization.algebraMap_injective_of_span_eq_top`, and `Localization.awayMap_injective_iff`.
   The first two concern all prime/maximal localizations; the third assumes a cover of the
   whole spectrum; the fourth concerns a map between two localizations. None is this result.
   The returned `StructureSheaf.toBasicOpen_injective` was not found under that name in the
   pinned source; its search signature concerns A_f to sections on D(f), not this theorem.
2. Loogle, query `Localization.Away, Function.Injective`: four hits, the preceding
   span-equals-top and away-map results, `awayMap_injective_of_dvd`, and
   `exists_awayMap_injective_of_localRingHom_injective`; none states the finite-tuple criterion.
   Candidate signatures were checked in `Mathlib/RingTheory/Localization/Away/Basic.lean`.
3. Mathlib grep, query
   `schematicallyDense|SchematicallyDense|injective.*[Ll]ocaliz|[Ll]ocaliz.*injective`,
   subdirectory `AlgebraicGeometry`: six hits, concerning homogeneous localization and
   spreading-out arguments, with no exact theorem.
4. LeanSearch, query `The map from a commutative ring to finitely many principal
   localizations is injective iff multiplication by the tuple is injective`: eight hits;
   the preceding prime-localization and away-map results plus injectivity preserved under
   localization and local injectivity criteria. None is the statement here.
5. `rg -n` for schematic-density names and the item ID in both the upstream
   `WeilConjectures/` and side-project `lean/Sheaf/`: found the existing general predicate
   `SchematicallyDenseOpen` and applications to modifications, but no affine tuple criterion.
   Further `rg` for `iSup.*basicOpen|basicOpen.*iSup|Injective.*Away|Injective.*fun.*f i`
   found cover and Cech constructions, not the theorem.
6. Declaration-collision searches for `affine_schematic_density_criterion` and
   `AffineSchematicDensityCriterion` in `dag/lean_names_upstream.json`, upstream sources,
   pinned Mathlib, and `lean/Sheaf/` returned no matches.

Validation: `scompile.py Q27 lem-trf-affine-schematic-density-criterion` compiled the
module against the side-project overlay with no errors and no warnings. Both automatic
implicit options are disabled. Every source line has at most 100 characters.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q27

This is this worker's second pass over the node, source, compiled file, and dependency
interfaces. No separate agent was started, as the dispatcher brief prohibits it; the
maintainer supplies the independent review of this delivery.

Rechecked each binder: A is any commutative ring, n includes zero, and f has exactly n
entries. Rechecked each actual map: localization is by `algebraMap`, multiplication is
on the left by f_i, and the sheaf restriction is the existing definition's restriction
from W to W intersect U for every open W. Checked the explicit ambient scheme in the
predicate: its carrier is the prime spectrum used by the basic opens, so no change of
space or extra transport is assumed. The finite-coordinate product encoding agrees
with the node's finite direct sums, including the empty family. Checked that the
conclusion's first iff is localization versus multiplication and its second iff is
localization versus sheaf injectivity, with no clause lost or extra hypothesis.
The needed general density predicate had already landed, so it was reused and its
node added to the dependencies instead of introducing another definition. No mismatch
requiring a statement correction or dependency-interface repair was found.
