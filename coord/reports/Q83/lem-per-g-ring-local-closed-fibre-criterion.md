## Worker report

The module `Sheaf.RingTheory.LocalClosedFibreCriterion` states
`RingHom.isRegular_iff_flat_isGeometricallyRegular_closedFiber_of_completion`.
It has one theorem, with `sorry` as the whole proof, and introduces no definitions.
The source was read directly: `literature/stacks-project/more-algebra.tex`,
Theorem `theorem-fs-regular` (Tag 0H7U), equivalence (1) and (2), and its proof.
The node agrees with the source. No statement correction, new node, or dependency repair.

Clause-by-clause correspondence:

- The commutative rings are `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  Independent explicit universes allow arbitrary sizes of both rings.
- Noetherianity is `[IsNoetherianRing R] [IsNoetherianRing S]`.
- Locality of both rings is `[IsLocalRing R] [IsLocalRing S]`; their named maximal
  ideals are `IsLocalRing.maximalIdeal R` and `IsLocalRing.maximalIdeal S`.
- The homomorphism `f` is encoded by `[Algebra R S]`, hence `algebraMap R S`.
  This is the prescribed regular-ring-map convention, not a finite-type condition:
  every commutative ring homomorphism equips its target with this algebra structure.
- Locality of `f`, equivalently `f(m) ⊆ n`, is
  `[IsLocalHom (algebraMap R S)]`, as in Mathlib's `local_hom_TFAE`.
- The canonical completion is `AdicCompletion (IsLocalRing.maximalIdeal R) R`;
  its algebra map sends `r` to its compatible residue classes modulo all powers.
  The harmless level zero is the zero quotient and does not change the inverse limit
  over the positive powers in the node.
- The only substantive extra hypothesis is `hcompletion`, regularity of that
  canonical `algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)`.
  It does not require that every prime localization have a regular completion map.
- The left side of the equivalence is `(algebraMap R S).IsRegular`.
- The first conjunct on the right is `(algebraMap R S).Flat`.
- The second is `Algebra.IsGeometricallyRegular
  (IsLocalRing.maximalIdeal R).ResidueField
  ((IsLocalRing.maximalIdeal R).Fiber S)`.
  This uses Mathlib's canonical fibre and its canonical left residue-field action,
  as required by the FIBRE RING convention. The residue field at the maximal ideal
  is canonically the quotient `k = R/m`: Mathlib's
  `Ideal.bijective_algebraMap_quotient_residueField` applies because `m` is maximal.
  Under this identification the fibre is `k ⊗[R] S ≅ S/mS`, where
  `bar a ⊗ s` maps to `f(a)s mod mS`, and `bar s` maps to `1 ⊗ s`.
  These are inverse maps and intertwine the k-actions; changing a representative
  by `m` or `mS` contributes zero. Thus this is the precise closed-fibre condition,
  using the canonical fibre presentation rather than a separate quotient definition.
- The imported `Algebra.IsGeometricallyRegular` includes Noetherianity and tests
  every finite purely inseparable field extension (in `Type (max u v)`). Its
  `IsRegularRing` conclusion is Mathlib's Noetherian regular ring condition.
- There is no completeness, finite-type, characteristic, or separability assumption.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, with the ring and
  canonical algebra structure from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and
  `Algebra.IsGeometricallyRegular` (the recorded def-weil-pbc-g-ring declarations).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`.
- The canonical maximal ideal, local-map condition, residue field, and fibre are
  Mathlib's `IsLocalRing.maximalIdeal`, `IsLocalHom`, `Ideal.ResidueField`, and
  `Ideal.Fiber`. There is no private copy of any of these notions.

All available proof-dependency modules are imported without `public` (those already
public for the statement remain public). The quotient-local-ring Mathlib clauses
are supplied by `Mathlib.RingTheory.LocalRing.Quotient`; completion locality,
completeness, localization Noetherianity, quotient Noetherianity, and completion
faithful flatness use the Mathlib modules recorded on the respective DAG leaves.
The remaining imports are the recorded geometric-regular-local-field adic-smooth,
flat closed-fibre adic-smooth, source-target completion, Noetherian completion,
complete-local regularity, regular composition, and regular permanence modules.
No import cycle was encountered. The theorem docstring reproduces all six proof
steps, including the Noetherian-fibre hypothesis needed for regular composition.

Edge cases checked by reading the definitions and source:

- Local rings are nonzero in Mathlib, as in the source; locality implies `mS ⊆ n`,
  so the closed fibre is nonzero. No zero-fibre case is silently removed.
- Fields are allowed (maximal ideal zero); the completion is the field and the
  right-hand side is precisely geometric regularity of the target over that field.
- The identity map is allowed, including when the local ring is not regular;
  the closed fibre is its residue field and the criterion concerns the map.
- Arbitrary residue characteristic and imperfect residue fields remain covered;
  the imported definition tests finite purely inseparable extensions, including
  the identity extension, and does not replace geometric regularity by regularity.
- Neither completion of `S` nor completeness of either original ring is a binder.
  No Noetherianity is inferred from a finite-type assumption.

Searches (2026-10-24):

- `msearch.py ... leanfinder`, query "A local map of Noetherian local rings with
  regular source completion is regular if and only if flat with geometrically
  regular closed fibre": 8 hits, about smooth maps, smooth algebras, and localization;
  none states this criterion (smoothness includes different finiteness conditions).
- `msearch.py ... loogle`, query `"IsRegularLocalRing", "Flat"`: 0 hits.
- `msearch.py ... leansearch`, query "regular local ring map flat geometrically
  regular closed fiber regular completion source": 8 hits, including `RingHom.Flat`,
  local-hom closed-point lemmas, smooth maps, regular sequences, and flat completion;
  no exact statement.
- `msearch.py ... grep`, query
  `GeometricallyRegular|regular.*closed.[Ff]ib|closed.[Ff]ib.*regular`, RingTheory:
  0 hits in Mathlib.
- `rg` over `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory` for
  closed-fibre and completion regularity finds the dependencies and other results
  with different conclusions (regular local target, formal smoothness, completions).
  Searches for `isRegular_iff_flat.*` and `isRegular.*closedFiber|isRegular.*closedFibre`
  found no instance of the present criterion.
- Searching the item id over `lean/WeilConjectures` and `lean/Sheaf` finds only the
  proof-plan citation in `Sheaf.RingTheory.CompletedBaseRegularity`, not a declaration.
  The chosen full declaration name and module name have no source or index collision.

Validation: `scompile.py Q83 lem-per-g-ring-local-closed-fibre-criterion` compiled
both the sandbox and library module presentations, 1.3 seconds each, with no errors
or warnings. All variables and universes are explicitly bound; no diagnostic commands.

## Second reading by Q83

The dispatcher explicitly prohibits starting another agent, and the maintainer supplies
an independent review. This section records the worker's second pass, not a claim of
an independent second worker.

Reopened the node, the source theorem, and the completed Lean file. Matched both
commutative Noetherian local rings with their four instance pairs; the homomorphism
and its locality with `Algebra R S` and `IsLocalHom (algebraMap R S)`; the regular
source completion with `hcompletion`; and both right-hand conjuncts and the left-hand
regularity with the indicated three predicates. Verified that the residue field and
closed fibre are canonical presentations of `R/m` and `S/mS`, including the field
structure and its action. Verified finite purely inseparable testing is inherited
from the recorded definition and that no completeness or finite-type restriction
has entered. The explicit theorem universes remain independent. There were no
mathematical mismatches, no new definitions, and no changes needed on this pass.
