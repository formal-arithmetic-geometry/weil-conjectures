## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllDecomposedLocusConstructible` states
`AlgebraicGeometry.Scheme.Hom.primeToEllDecomposedLocus_indConstructible` with proof
`sorry`. It introduces no definitions or additional nodes. Only the item's `lean`
record changes. The declaration docstring gives all six steps of the accepted
DAG proof, including the localization isolating the selected generic field factor,
the fibre degree-sum argument, and the topology equivalence.

### Statement correspondence

- Schemes X and Y: `{X Y : Scheme.{u}}`, with one explicit, arbitrary universe u.
  Morphism Y → X: `(f : Y ⟶ X)`. All variables and universes are explicitly bound.
- Noetherian X, in the node's finite affine Noetherian-cover sense:
  `[IsNoetherian X]`. Mathlib's `isNoetherian_iff_of_finite_affine_openCover` in
  `Mathlib.AlgebraicGeometry.Noetherian` identifies this class with precisely the
  stated finite-cover condition; it is not merely a Noetherian underlying space.
- Prime ell: `(ell : ℕ) (hell : ell.Prime)`.
- Étale morphism: `[Etale f]`, the recorded affine-locally étale ring-map definition.
- The subset is written inline in both conclusions as
  `{x : X | ∃ y : Y, f y = x ∧ (f.residueFieldMap y).hom.Finite ∧
    ¬ ell ∣ f.residueDegree y}`. Thus the witness is a point of the actual source Y,
  its image is exactly x, the canonical residue-field map is finite, and its degree
  is not divisible by ell. `RingHom.Finite` means finite as a module through the
  displayed map, hence finite-dimensional for these fields. `residueDegree` is
  `Module.finrank` for that SAME canonical map. The field extension has direction
  κ(f(y)) → κ(y), agreeing with the node. No arbitrary algebra structure is used.
- Ind-constructibility, explicitly a union of locally closed subsets:
  `∃ S : Set (Set X), (∀ s ∈ S, IsLocallyClosed s) ∧ ⋃₀ S = ...`.
  `IsLocallyClosed` means the intersection of a Zariski open with a Zariski closed.
  A set of subsets allows unions of any size needed here without an artificial
  index-universe bound or a nonempty-index requirement.
- Equivalent openness formulation: the second conjunct is
  `IsOpen[constructibleTopology X] ...`. Giving both properties states both node
  formulations; the final proof-docstring step explains their equivalence on a
  Noetherian scheme. The topology is Mathlib's exact compact-open/complement
  subbasis, not the Zariski topology. `open scoped Topology` exposes its notation.
- The absence of quasi-compactness or separation assumptions on Y and f is
  retained. There are no instances or hypotheses asserting either property.

### Dependency declarations

Read each recorded declaration and docstring in the current Lean source:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (`def-pc-scheme`).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff`, together with `isNoetherianRing_iff_ideal_fg`
  (`def-weil-pbc-noetherian-ring`). The actual scheme hypothesis uses
  `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`,
  following the project's NOETHERIAN SCHEME convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (`def-weil-etale-morphism`).
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.residueField`,
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` and
  `AlgebraicGeometry.Scheme.Hom.residueDegree` (`def-weil-residue-field`).
- `Mathlib.Topology.Spectral.ConstructibleTopology`: `constructibleTopology`,
  using the node's exact `mathlib_match` (`def-weil-pbc-constructible-topology`).

All stated proof dependencies' modules are also imported, using plain imports
when not already public statement dependencies. These include
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` (finite locally free),
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` (closed-immersion residue
fields), `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`, and
`Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAway`, together with Mathlib's
closed/open immersions, finite morphisms, affine schemes, ring-hom properties,
pullbacks and their carriers, finite-flat rank, and étale rings over fields and
base change. No recorded interface needed repair.

### Sources and edge cases

Read ILO Exposé II 2.1.1, 2.2.1, Proposition 2.2.2 and its proof (printed pp. 26–27),
and Corollary 2.2.4, from the local PDF. The text of 2.2.1 reverses the residue-field
extension in print; 2.1.1 and the proof use κ(y)/κ(x), exactly as the already-reviewed
node and this statement do. Also read the current blueprint ancestor's proof in
`literature/blueprint/latest/`, not an older snapshot. No node correction is needed.

Checked the empty source and empty target: the locus is empty and the union can
be empty (`S = ∅`). For the identity, every point has finite degree one, so the
locus is all X for every prime ell. Over a field, the assertion covers any étale
source, including an infinite disjoint union; no finite covering or source
compactness assumption was introduced. A lift of degree divisible by ell is
excluded unless another lift has a permissible degree. In a split fibre the
condition asks for one residue-field factor, not that the total fibre rank is
prime to ell. Non-reduced X and non-separated Y are allowed, and ell may equal a
residue characteristic. The explicit finite-map conjunct prevents interpreting
Mathlib's default degree zero for infinite extensions as a genuine finite degree.
The prime condition is exactly the node's and imposes no characteristic condition.

### Searches

- `msearch.py`, LeanFinder: “For an etale morphism over a Noetherian scheme the
  locus admitting a residue field extension of finite degree prime to ell is ind
  constructible”. Eight results concern étale loci and polynomial factorization;
  none states this locus assertion.
- `msearch.py`, Loogle: `AlgebraicGeometry.Scheme.Hom.residueDegree,
  constructibleTopology`. Zero results.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `decomposed|residueDegree|ind.?[Cc]onstructible`. Four results: the residue-degree
  definition and identity computation, and its use in algebraic cycles; no theorem.
- `rg` in the project `lean/WeilConjectures` and `lean/Sheaf`: searched
  `residueDegree|primeToEll|prime_to_ell|decomposedLocus|indConstructible`, then
  `decomposed|[Dd]ecomposed|prime.to.ell.*locus|locus.*prime.to.ell`.
  `PrimeToEllAlterationTopology` defines covering families, not the point locus or
  its constructibility; no duplicate assertion was found. The family convention
  uses the same finite residue-field map and residue degree as this statement.
- `grep -rn` for this item's id in `lean/WeilConjectures`: no hits.
- `rg` for the proposed declaration names in `dag/lean_names_upstream.json`,
  Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no hits.

There is no STATEMENT-DISPUTED finding, new node, dependency repair or statement
change. The only initial elaboration error was missing the `Topology` notation
scope, repaired by `open scoped Topology`.

## Validation

Compilation uses only the prescribed `scompile.py` server wrapper. The delivered
file is a module, all theorem proofs are `sorry`, and no line exceeds 100 columns.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
