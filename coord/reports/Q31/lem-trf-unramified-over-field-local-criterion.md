## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion` states
`AlgebraicGeometry.unramified_over_field_iff_local_criterion`, with a single `sorry`
and no definitions or proofs. The item's statement, dependencies and proof are unchanged.
No repair note for this item is present in `coord/repair-notes`.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the scheme and its specified structure
  morphism are `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))`.
- Locally of finite type is the assumption `[LocallyOfFiniteType f]`. No finite type,
  quasi-compactness, separatedness or nonemptiness assumption is added.
- Unramifiedness is exactly the dependency's recorded inline form
  `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`, including its local
  finite type clause despite that already being assumed.
- The equivalence is `↔`, and every point is quantified by `∀ y : Y`.
- Closedness is `y ∈ closedPoints Y`, definitionally `IsClosed ({y} : Set Y)`.
- The local ring equals its residue field by the canonical map:
  `Function.Bijective (Y.residue y)`. `Scheme.residue` is the quotient map from
  `Y.presheaf.stalk y` to `Y.residueField y`; its bijectivity is precisely that this
  canonical map is an isomorphism. This is stronger than the existence of an unrelated
  abstract ring isomorphism, and is the meaning specified in the node's proof.
- Finite extension is `(f.residueFieldAlgebraMap y).Finite`, namely finiteness as a
  module for the canonical homomorphism `k →+* Y.residueField y`.
- Separable algebraic extension is
  `@Algebra.IsSeparable k (Y.residueField y) _ _ (f.residueFieldAlgebraMap y).toAlgebra`.
  The algebra argument is explicit: the extension is induced by this particular `f`.
  `Algebra.IsSeparable` includes algebraicity because a nonalgebraic element has zero,
  hence nonseparable, minimal polynomial.
- Empty `Y` is allowed: there is no `[Nonempty Y]`, and the right-hand pointwise
  condition is vacuous. Both sides hold for the empty scheme over `k`.

Dependency interfaces read and used:

- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (read its all-affine-pairs signature).
- `def-weil-unramified-morphism`: that same module, plus the Mathlib scheme limits
  and open-immersion interfaces; use its recorded conjunction with
  `AlgebraicGeometry.IsOpenImmersion` and `CategoryTheory.Limits.pullback.diagonal`.
  Read the diagonal construction and scheme open-immersion abbreviation.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.residue` and
  `Scheme.Hom.residueFieldMap` (definitions and naturality read).
  `WeilConjectures.ZetaSeries` supplies the already defined
  `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`; its full definition was read.
  It composes the base-field residue identification with `f.residueFieldMap`, so
  there is no new notion or arbitrary algebra structure here.
- `def-weil-closed-points`: its `mathlib_match` is `closedPoints` in
  `Mathlib.Topology.JacobsonSpace`; the definition and `mem_closedPoints_iff` were read.
  Its absent `lean` record is valid for a Mathlib dependency and needs no repair.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; read its docstring, full class and algebraicity consequence.

Proof imports follow the recorded plan: `Mathlib.RingTheory.Etale.Kaehler`
(`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`),
`Mathlib.RingTheory.Kaehler.Basic`, `Mathlib.RingTheory.Unramified.Basic`,
`Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`,
`Sheaf.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood`
(`AlgebraicGeometry.FormallyUnramified.exists_neighbourhood_of_stalkMap`), and
`WeilConjectures.AlgebraicGeometry.Thickening` (`IsFirstOrderThickening`).
The last source was read with `scompile.py --source` because the old source checkout
has no such file. The fibre-decomposition proof node has no recorded declaration or
Mathlib match on the supplied base, so no corresponding import is available; it is
named in the proof docstring and no substitute theorem is introduced.

Source and edge cases checked: read Stacks `morphisms.tex`,
`lemma-unramified-over-field` (02G7), its proof, and
`lemma-unramified-at-point` (02GF), especially condition (6). The source field-fibre
characterization and its local form agree with the statement. An arbitrary, even
infinite, disjoint union of spectra of finite separable fields is allowed (no
quasi-compactness assumption). `Spec k` satisfies all clauses. A finite purely
inseparable field extension fails the separability clause and unramifiedness; dual
numbers fail bijectivity of the residue map; on the affine line the generic point
fails closedness and finiteness, and the closed-point stalks are not fields.
There is no characteristic restriction. All variables and the universe are explicit.
No statement dispute or correction is needed.

Searches made with `msearch.py` (the actual results are in `searches.jsonl`):

- LeanFinder: “A scheme locally of finite type over a field is unramified iff every
  point is closed and the canonical map from its local ring to its residue field is
  bijective and the residue extension is finite separable”: 8 hits, including
  `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq` and algebraic local criteria;
  none is the global scheme equivalence with all displayed clauses.
- Loogle: `Algebra.FormallyUnramified, IsLocalRing`: 12 algebra-level hits, including
  finite/separable residue fields and maximal-ideal criteria. They do not state this
  scheme-level equivalence.
- Grep: `unramified.*field|unramified.*stalk|iff_map_maximalIdeal_eq`: 25 hits,
  including `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` and
  `Mathlib.RingTheory.Unramified.LocalRing`; no exact statement.
- LeanSearch: “scheme unramified over field local rings residue fields finite
  separable”: 8 hits, principally residue-field instances and formal unramifiedness;
  no exact scheme-level statement.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` with
  `unramified.*field|unramified.*[Ss]talk|unramified.*iff` found finite/separable
  residue results, discreteness, the stalk-neighbourhood theorem and geometric-fibre
  criteria, but no exact equivalence. Read the upstream formally-unramified module
  and the side discreteness and geometric-fibre modules to check these candidates.
- `grep -rn` for the exact item id in upstream `WeilConjectures` returned no match.
  The exact new declaration name was also checked against Mathlib, upstream and the
  upstream name index; it does not duplicate an existing declaration.

The dispatcher reported a previous stage-1-style delivery refusal for the existing
item node. The preserved sandbox contained only `.brief*` markers, no statement
module, node copy or report. This delivery supplies the missing stage-2 artifacts
and uses `deliver2.py`, which updates the existing node's `lean` record.

Validation: `scompile.py Q31 lem-trf-unramified-over-field-local-criterion` compiled
this file cleanly as both a sandbox module (31.7 seconds) and its library module
(46.9 seconds), with no errors or warnings. Each invocation retained the 60-second
limit. All proof dependencies having usable recorded modules are imported; the
unstated fibre-decomposition node is the only unavailable proof import.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
