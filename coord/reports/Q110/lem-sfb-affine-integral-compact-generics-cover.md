## Worker report

The module `Sheaf.AlgebraicGeometry.AffineIntegralCompactGenericsCover` states
`AlgebraicGeometry.exists_affine_integral_surjective_compact_genericPoints` with
`sorry` as its whole proof. No definitions or helper theorems are introduced.
The node is unchanged except for its `lean` record.

Clause-by-clause reading:

- “Let Y be an affine scheme”: `(Y : Scheme.{u}) [IsAffine Y]`. The universe `u`
  is explicitly declared and arbitrary.
- “There exist a reduced affine scheme C”: `∃ (C : Scheme.{u}) ...,
  IsReduced C ∧ IsAffine C ∧ ...`. Reducedness is the recorded Mathlib notion;
  its sectionwise definition is equivalent to reducedness of every local ring.
- “a surjective integral morphism p : C → Y”: `(p : C ⟶ Y)` with the conjuncts
  `Surjective p ∧ IsIntegralHom p`. Integrality includes affineness of the
  morphism and integrality on every affine target open. No finite-type or
  finite-presentation condition is introduced.
- “the set of generic points of the irreducible components”: `genericPoints C`.
  Mathlib defines this as `{x | closure {x} ∈ irreducibleComponents C}`, exactly
  the generic-point characterization in the node. It is neither the set of all
  generic points of arbitrary irreducible closed subsets nor the component index
  type given a discrete topology.
- “with the subspace Zariski topology, is quasi-compact”: `CompactSpace
  (genericPoints C)`. A set coerces to its subtype with the induced topology.
  Mathlib's compactness has no Hausdorff requirement; equivalently, every open
  cover has a finite subcover. `isCompact_iff_compactSpace` identifies this with
  `IsCompact (genericPoints C)` in `C`.
- “Y need not be reduced or Noetherian; the empty scheme is allowed”: no such
  assumptions occur, and no `Nonempty` binder occurs for either scheme.

Recorded statement dependencies used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (available through
  the public scheme imports). Affineness is `AlgebraicGeometry.IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme`, with `Scheme.isoSpec` identifying its
  canonical definition with the node's spectrum presentation.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-weil-surjective-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, which publicly imports Integral;
  use `AlgebraicGeometry.IsIntegralHom`, not `IsFinite` or `IsIntegral` of a scheme.
- `def-weil-irreducible-components`: Mathlib's `irreducibleComponents`, used inside
  `genericPoints` from the publicly imported `Mathlib.Topology.Sober`.

Proof-only imports: `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`
(the node's recorded residue-field theorem),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`integralClosure`), and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (the quasi-separatedness
clause of the affine-qcqs leaf). The affine spectrum, affine stalk localization,
affine-cover integrality criterion, and affine compactness leaves are already
available through the imported Mathlib modules. The proof dependency
`lem-sfb-idempotent-annihilator-generic-retraction` has neither a Lean record nor a
Mathlib match on the read base, so there is no module to import for it. It is not
needed to type this statement; its six-step mathematical use is retained in the
proof docstring and the unchanged DAG proof.

Edge cases checked mathematically before writing:

- Empty `Y`: take the empty affine scheme `C = Spec 0`. Reducedness includes the
  zero ring, the unique map is integral and surjective, and the generic-point
  subtype is empty and compact. The signature excludes none of this.
- Nonreduced `Y`, for example `Spec(k[ε]/ε²)`: reducedness is asserted only of `C`.
  Integrality does not mean injectivity of the map on coordinate rings.
- Arbitrarily many irreducible components and non-Noetherian bases: no finite
  component condition, finite morphism condition, or Noetherian condition occurs.
  Compactness concerns the induced topology, not finiteness of the generic set.
- Universe: the product of residue fields indexed by primes of a ring in `Type u`
  and its integral-closure subring stay in `Type u`; choosing `C : Scheme.{u}`
  therefore does not prevent the construction in the unchanged proof.

Searches made (2026-10-24; all via the prescribed wrappers and read-only sources):

- `msearch.py ... leanfinder "Every affine scheme admits a reduced affine integral
  surjective cover whose generic point subspace is quasi compact"`: 8 hits, affine
  open-cover and quasi-affine declarations only; no match for this theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsIntegralHom,
  AlgebraicGeometry.Surjective"`: 0 hits.
- `msearch.py ... grep "genericPoints|[Cc]ompact.*[Gg]eneric|[Gg]eneric.*[Cc]ompact"
  AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "An affine scheme admits a reduced integral surjective
  cover with quasi compact space of generic points"`: 8 hits, ordinary affine
  covers and reducedness lemmas; none provides the required cover.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for generic-point compactness and
  integral covering declarations: existing generic-point and affine-cover facts,
  but no theorem asserting this reduced integral surjective cover. The generic
  compactness helper in `GenericQuasiSeparatedness.lean` concerns compact opens
  after localization of a finite type algebra over a domain, a different statement.
- `rg -n "lem-sfb-affine-integral-compact-generics-cover" lean/WeilConjectures`:
  no occurrence. Name searches in both project roots, Mathlib and
  `dag/lean_names_upstream.json` found no collision for the proposed declaration.
- Read Mathlib `Topology/Sober.lean` and `Topology/Irreducible.lean`: existing
  `genericPoints`, `IsGenericPoint`, and `irreducibleComponents` supply precisely
  the needed notions, so no replacement definition was written.

Read the actual source PDF at
https://davidrydh.se/papers/submersion20100305.pdf, printed pages 13–14:
Definition (3.8), Properties (3.9)(iii),(vi), and the affine paragraph of the proof
of Theorem (3.10). The reduction there supplies exactly the hypotheses and
conclusions recorded in this node. No statement correction or dispute is needed.

Validation: the prescribed `scompile.py Q110
lem-sfb-affine-integral-compact-generics-cover <module>` compiled both its sandbox
and library module forms successfully (2.2 s and 2.3 s), with no reported error or
unexpected warning. Every variable and universe is explicitly bound, with
`autoImplicit false` also set in the file.

## Second reading by Q110

This dispatcher assignment explicitly permits no other agents; the maintainer
performs the independent review after delivery. This section records a separate
self-check, not a claim that another worker reviewed the module.

Reopened the JSON statement and the completed Lean module. The single base
hypothesis is `IsAffine Y`; all five conclusions are present: reduced C, affine C,
surjective p, integral p, and compact generic-point subtype. The two scheme binders
share the declared arbitrary universe. The morphism has source C and target Y.
`genericPoints` unfolds to the closure/irreducible-component test, and its subtype
uses the subspace Zariski topology. No nonemptiness, reduced-base, finite-type,
Noetherian, or finite-component restriction was added. No mismatch was found and
no statement or proof-plan field was changed. The docstring follows all six DAG
proof steps, including the noninjective residue-product map and empty-ring case.
