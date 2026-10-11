## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite` states
`AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`.
For a morphism `f : X ⟶ S` of schemes, its signature is exactly
`IsQuasiFinite f ↔ IsLocallyQuasiFinite f ∧ AlgebraicGeometry.QuasiCompact f`.
The predicates are the four definitions in `pqf-def-quasifinite`, imported from
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
`IsQuasiFinite` expresses locally finite type, quasi-compactness, and isolated
points in each scheme-theoretic fibre; `IsLocallyQuasiFinite` quantifies
`IsQuasiFiniteAtPoint` over all points; and `QuasiCompact` is the same
quasi-compact morphism predicate in the node's conclusion. The theorem proof is
`sorry`, as required at stage 2.

The node's only hypothesis is that `f` is a morphism of schemes; this is the
explicit binders `{X S : Scheme.{v}} (f : X ⟶ S)`. The conclusion has both
directions of the equivalence, with local quasi-finiteness and quasi-compactness
as the right-hand conjunction. No extra separation, finite-type, or nonemptiness
hypothesis is introduced.

Dependency declaration used: `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`,
`IsLocallyQuasiFinite`, `IsQuasiFinite`, and `HasFiniteFibres` from
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` (node `pqf-def-quasifinite`).
That project declaration is the exact Stacks Tag 01TD notion, whereas Mathlib's
`LocallyQuasiFinite` omits the local finite-type requirement. The definition node was added to `stmt_deps` under brief-stage2 §5's
permission to add nodes already landed with a Lean record. No other field is
changed except `lean`.

Edge cases checked: the binders allow arbitrary schemes, including empty schemes;
the universal point quantifier in `IsLocallyQuasiFinite` is therefore vacuous on
an empty source, and no nonempty fibre or dimension assumption is imposed.

Source checked: [Stacks Tag 01TJ](https://stacks.math.columbia.edu/tag/01TJ),
whose morphism binder and equivalence match the theorem exactly. The local
literature files are absent on this machine.

Searches made:

- LeanFinder query “scheme morphism quasi-finite if and only if locally
  quasi-finite and quasi-compact”: found only
  `AlgebraicGeometry.LocallyQuasiFinite`, `locallyQuasiFinite_iff`, and
  `LocallyOfFiniteType`, and quasi-compactness lemmas; eight hits, no combined
  equivalence.
- Loogle query `AlgebraicGeometry.LocallyQuasiFinite,
  AlgebraicGeometry.QuasiCompact`: nine component hits including
  `locallyQuasiFinite_iff_isFinite_fiber` and `finite_preimage_singleton`;
  none states the Stacks-predicate equivalence.
- grep query `quasiFinite.*iff|LocallyQuasiFinite.*QuasiCompact|quasi-finite.*quasi-compact`
  in Mathlib AlgebraicGeometry: found component lemmas in
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`, but no combined theorem.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no existing
  theorem for this equivalence; the only matching project notion is the recorded
  `QuasiFiniteMorphism` dependency.

## New nodes

None.

## Dependency modules

None: the dependency declaration is already usable and available on the server.

LeanSearch query “quasi-finite morphism is equivalent to locally quasi-finite and
quasi-compact”: unavailable, Internal Server Error; no match verdict inferred.

## Second reading by C1

I read the node statement, its source (blueprint node order 200 and Stacks
Project Tag 01TJ), the dependency node `pqf-def-quasifinite`, and the Lean
module independently. The source says: (1) introduce schemes `X` and `S` and a
scheme morphism `f : X ⟶ S`; (2) conclude the equivalence that `f` is
quasi-finite exactly when it is locally quasi-finite and quasi-compact. The
Lean binders `{X S : AlgebraicGeometry.Scheme.{v}} (f : X ⟶ S)` render (1).
The left side `IsQuasiFinite f` renders quasi-finite using the dependency's
Stacks 01TD definition (locally finite type, quasi-compactness, and every
fibre point isolated). The first right conjunct `IsLocallyQuasiFinite f`
renders locally quasi-finite using the same dependency (quasi-finite at every
source point, including its finite-type affine condition). The second right
conjunct `AlgebraicGeometry.QuasiCompact f` renders quasi-compactness. The
outer `↔` renders both directions in the same order as the source. Every
object, hypothesis, and conclusion clause matches; no extra separation,
Noetherian, finite-type, characteristic, or nonemptiness assumption appears.

The empty source scheme is covered: the point quantifier in
`IsLocallyQuasiFinite` is vacuous, while the morphism and quasi-compactness
predicates remain those of the statement. Empty target schemes, zero rings in
affine presentations, and arbitrary universe `v` are not excluded. There is no
natural-number parameter or characteristic hypothesis in this node.

I checked the declaration signatures in
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: the four predicates are the
project's definitions and are not Mathlib's weaker `LocallyQuasiFinite` notion.
Searches were repeated with LeanFinder (scheme quasi-finite equivalence),
Loogle (the two predicate names), `rg` over `lean/Sheaf` and
`WeilConjectures/`, and grep over Mathlib's AlgebraicGeometry quasi-finite
files. They found only component notions and lemmas, with no existing
combined equivalence. The LeanSearch service was unavailable, as recorded in
the worker searches. The dependency node is already landed and is cited in
`stmt_deps`; no new node or dependency module is needed.

The only discrepancy found was in the original repository copy of the node,
whose `stmt_deps` was empty despite the theorem using the Stacks predicates.
The worker sandbox copy already records the landed dependency
`pqf-def-quasifinite`; I retained that correction and changed no Lean
signature. The module compiled cleanly with `scompile.py`, with its sole proof
remaining `sorry` as required for stage 2.
