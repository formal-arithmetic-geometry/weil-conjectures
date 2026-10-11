## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated` states
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`, with proof `sorry`.
It uses Mathlib's scheme fibre `Scheme.Hom.fiber`, its first projection `fiberι`, and
`fiberHomeo`-compatible topology, together with the project's Stacks predicate
`IsQuasiFiniteAtPoint`.

Clause-by-clause reading:

| Node clause | Lean rendering |
| --- | --- |
| Morphism of schemes | `{X S : AlgebraicGeometry.Scheme.{u}}` and `f : X ⟶ S` |
| Locally of finite type | `[AlgebraicGeometry.LocallyOfFiniteType f]` |
| Point and quasi-finiteness at it | `x : X` and `hfx : IsQuasiFiniteAtPoint f x` |
| Fibre over `s = f x` | `f.fiber (f x)` |
| First projection | `f.fiberι (f x)` |
| Unique point above `x` | `∃ ξ, f.fiberι (f x) ξ = x ∧ (∀ η, f.fiberι (f x) η = x → η = ξ)` |
| Isolated point | `IsOpen ({ξ} : Set (f.fiber (f x)))` |
| Equivalent subspace formulation | `IsOpen ({ξ} : Set (f.fiber (f x))) ↔ IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))` |

The subtype point `⟨x, rfl⟩` is the point corresponding to `x` in the subspace
`f ⁻¹' {f x}`; this is required for the stated equivalence to typecheck. The
existential uniqueness clause makes the unique point explicit, while `fiberι` is the
canonical projection supplied by Mathlib.

Dependencies used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and morphisms `X ⟶ S` (Mathlib).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` (Mathlib).
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, and the fibre
  homeomorphism API (Mathlib `Mathlib.AlgebraicGeometry.Fiber`).
- `pqf-def-quasifinite`: `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint` from
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.

Edge cases checked: the fibre may be empty in general, but under the given point `x`
there is a canonical fibre point; no nonempty or separated hypothesis is added. Empty
fibres away from `x`, singleton fibres, zero-dimensional schemes, and arbitrary scheme
universes are permitted. The subtype formulation handles the subspace topology exactly.
No characteristic, reducedness, or Noetherian hypothesis is introduced.

Searches (2026-10-11):

- `msearch.py ... leanfinder "quasi-finite at a point implies the point is open in its fibre"`:
  `LocallyQuasiFinite` and related topology lemmas, but no exact Stacks predicate.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt, IsOpen"`:
  found `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`; it uses Mathlib's
  stalk-map notion and omits the Stacks local finite-type condition, so it is not exact.
- `msearch.py ... grep "QuasiFiniteAt\\|isOpen_singleton_asFiber"` in Mathlib:
  found `Scheme.Hom.QuasiFiniteAt` and its criterion in
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`: no existing theorem with this
  statement; the only relevant existing declaration is the dependency predicate above.

No statement correction or new node was needed. The source is Stacks Project Morphisms,
Lemma 01TH (proof of (1) implies (2)); the theorem proof remains intentionally `sorry`
for stage 2.

## Earlier second reading (a previous round; superseded)

Independent reading of the node, source place, dependency declarations, and Lean module
found the statement clauses rendered faithfully. The canonical fibre point and the
subspace point are typed explicitly, and compilation produced no errors or warnings.

## Second reading by F1

I independently opened the item node, all four statement-dependency nodes and their
recorded declarations, the delivered module, and Stacks morphisms.tex at Definition
01TD and Lemma 01TH. The local Stacks copy is
`/home/ubuntu/c1-stacks-review/morphisms.tex`; its tags/tags confirms both labels.
The first paragraph of the proof of 01TH is precisely (1) implies (2).
The source assumes only schemes, a morphism, a point, and local finite type;
there is no standing Noetherian, separatedness, base-field or characteristic assumption.

Object/hypothesis/conclusion checklist (H3):

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes X and S | `{X S : AlgebraicGeometry.Scheme.{u}}` | Exact; Mathlib locally ringed spaces with affine neighbourhoods. |
| Scheme morphism f | `(f : X ⟶ S)` | Exact; Mathlib Scheme.Hom is a morphism of locally ringed spaces. |
| Locally of finite type | `[AlgebraicGeometry.LocallyOfFiniteType f]` | Exact; the dependency class requires finite-type appLE maps on affine opens, the node's equivalent affine-cover condition. |
| Point x | `(x : X)` | Exact; the underlying scheme point type. |
| s = f(x) | `f x` throughout | Exact, no independent or unconstrained base point. |
| Scheme-theoretic fibre X_s | `f.fiber (f x)` | Exact; read Fiber.lean: pullback of f and S.fromSpecResidueField. |
| First projection p | `f.fiberι (f x)` | Exact; read Fiber.lean: pullback.fst. |
| Quasi-finite at x | `(hfx : IsQuasiFiniteAtPoint f x)` | Exact; read QuasiFiniteMorphism.lean: affine U containing x, affine V, U ≤ preimage V, finite-type appLE algebra, and the recorded IsQuasiFiniteAtPrime at the corresponding prime. |
| Existence of a fibre point over x | `∃ ξ : f.fiber (f x), f.fiberι (f x) ξ = x ∧ ...` | Exact; point chosen after the hypotheses. |
| Unique point over x | `∀ η : f.fiber (f x), f.fiberι (f x) η = x → η = ξ` | Exact; uniqueness in the entire fibre, not only the affine chart. |
| Isolation in X_s | `IsOpen ({ξ} : Set (f.fiber (f x)))` | Exact; singleton open in the fibre scheme topology. |
| Equivalent isolation in the subspace f inverse(s) | `IsOpen ({ξ} : Set (f.fiber (f x))) ↔ IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))` | Exact; the subtype has the induced topology and the canonical point x. |

The existential conclusion conjoins precisely the existence, uniqueness, openness and
its subspace equivalence asserted by the node. No signature change is needed.
Read `Scheme.Hom.fiberHomeo`, `fiberHomeo_apply` and `asFiber`: they confirm that the
projection identifies this fibre with exactly the intended subspace. Read the
recorded ring predicate `Algebra.IsQuasiFiniteAtPrime` as well: it uses the canonical
fibre-spectrum homeomorphism and openness of the corresponding prime singleton,
with finite type supplied by the affine witness. All notions come from their
recorded dependency modules; no private copy or hollow data is present.

Edge cases: empty X has no x, so the universal theorem has no instances to check;
empty S admits no image of a supplied x. Although other fibres can be empty, the
fibre over f x contains f.asFiber x, so no extra Nonempty assumption is required.
Singleton fibres and nonreduced schemes are included. Zero rings correspond to the
empty affine case, without excluding it. There are no index sets, integer n or
characteristic hypotheses. The arbitrary bound universe u covers schemes of any
size in a common universe; all universes and variables are explicitly bound.
There are no extra instances beyond local finite type.

Independent searches (2026-10-11):

- LeanFinder via msearch: "an isolated singleton in the scheme theoretic fibre of a
  morphism at a point" found asFiber, fiber, fiberι and fibre structure declarations,
  but no theorem with the project's IsQuasiFiniteAtPoint hypothesis.
- Loogle via msearch: `AlgebraicGeometry.Scheme.Hom.fiberHomeo` found the homeomorphism
  and its projection compatibility lemmas; opened those declarations in Fiber.lean.
- Grep via msearch: `IsQuasiFiniteAtPoint|isOpen_singleton_asFiber` found Mathlib's
  quasiFiniteAt_iff_isOpen_singleton_asFiber. I opened its signature and QuasiFiniteAt
  definition: it uses the stalk-map ring quasi-finiteness predicate, whereas our
  dependency is the Stacks affine-neighbourhood predicate. This requires a comparison
  theorem and is not an exact existing rendering of this node. The worker report's
  claim that the candidate theorem omits local finite type is inaccurate: its
  signature does have `[LocallyOfFiniteType f]`; it is the predicate that differs.
- LeanSearch via msearch: "quasi finite at a point implies its singleton is open in
  the scheme fibre" returned Internal Server Error, recorded unavailable without
  an absence verdict.
- Direct rg on Mathlib AlgebraicGeometry, WeilConjectures and project lean/Sheaf,
  using `IsQuasiFiniteAtPoint|isolated_in_fiber|quasiFiniteAt.*isOpen|isOpen.*asFiber|isolated.*fibre|isolated.*fiber`,
  found the dependency predicate, Mathlib candidate, and related isolated-point
  theorems, but no existing declaration of the delivered implication. Thus retaining
  this module is appropriate (H4).

Mismatches repaired: missing project copyright/license/authors header (H9), and a
proof docstring that compressed five node steps into one sentence (H8). Added the
header and expanded the docstring into the five steps, naming the affine chart,
residue-field naturality, open-fibre product, affine-spectrum identification,
prime-bijection and fibre-homeomorphism dependencies. The theorem signature and
node lean.statement are unchanged. No mathematical statement correction, new node
or dependency module is required. The single theorem retains `by sorry`; no proof
was supplied, and there are no definitions in this delivery.
