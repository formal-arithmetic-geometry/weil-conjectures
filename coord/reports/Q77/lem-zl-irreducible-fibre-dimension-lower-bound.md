## Worker report

The module `Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound` states the
irreducible finite type fibre-dimension lower bound from Stacks Project Tag 0B2L,
parts (2)(a) and (2)(b).  It introduces a natural number `r` by the equation
`topologicalKrullDim X = topologicalKrullDim (closure (Set.range f.base) : Set Y) +
(r : WithBot ℕ∞)`, then states the pointwise lower bound and the dense-open equality
locus.  Every proof is `sorry` as required for stage 2.

The original node wrote `r = dim X - dim Z`, but `WithBot ℕ∞` has no subtraction
operation, so that statement cannot be typed.  The source proves finiteness and a
transcendence-degree difference, so the corrected statement uses the equivalent
existential natural-number representative `r` and records the additive equation.
The only citer, `lem-zl-finite-type-fibre-image-dimension-bounds`, still holds: it
uses precisely this natural-number difference and the dense-open equality locus.

The Lean rendering of each hypothesis and clause is:

- `k` is a field: `(k : Type u) [Field k]`.
- `X` and `Y` are schemes of the same universe: `{X Y : Scheme.{u}}`.
- They are schemes over `Spec k`: `[X.Over (Spec (.of k))]` and
  `[Y.Over (Spec (.of k))]`.
- `X` is irreducible: `[IrreducibleSpace X]`.
- `X` is finite type over `k`: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`.
- `Y` is finite type over `k`: `[LocallyOfFiniteType (Y ↘ Spec (.of k))]` and
  `[QuasiCompact (Y ↘ Spec (.of k))]`.
- `f` is a `k`-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`.
- The dimension decomposition is the existential `∃ r : ℕ, topologicalKrullDim X =
  topologicalKrullDim (closure (Set.range f.base) : Set Y) + (r : WithBot ℕ∞)`.
- The lower bound is `(∀ x : X, (r : WithBot ℕ∞) ≤
  topologicalKrullDimAt (f.asFiber x))`.
- The equality locus is both dense and open, rendered as `Dense {x : X |
  topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)}` and the corresponding
  `IsOpen` clause.

Dependency declarations used:

- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  from Mathlib's finite-type morphism APIs (the recorded dependency
  `def-weil-finite-type-morphism`).
- `AlgebraicGeometry.Scheme.Over` and `Scheme.Hom.IsOver` from
  `Mathlib.AlgebraicGeometry.Over` (the recorded dependency
  `def-weil-scheme-over-base`; available through the imported scheme APIs).
- `topologicalKrullDim` from `Mathlib.Topology.KrullDimension` (the recorded
  dependency `def-kun-topological-krull-dimension`).
- `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `asFiber` and the fibre residue-field
  construction from `Mathlib.AlgebraicGeometry.Fiber` (the recorded dependency
  `def-pc-scheme-fibre`).
- `topologicalKrullDimAt` from `WeilConjectures.Mathlib.Topology.KrullDimension`
  (the recorded dependency `def-kun-topological-dimension-at-point`).
- `TopologicalSpace.IsIrreducible`/`IrreducibleSpace` from Mathlib topology (the
  recorded dependency `def-weil-irreducible-components`).

Edge cases checked: irreducibility supplies nonemptiness, so the generic-point argument
has a point; the empty scheme is therefore outside the hypotheses.  Zero-dimensional
schemes give `r = 0`; for the structural map to `Spec k`, `r = dim X` and every local
fibre dimension is `dim X`.  The natural-number existential avoids any
undefined subtraction involving `⊥` or `⊤` in `WithBot ℕ∞`.

Searches made:

- `msearch.py Q77 ... leanfinder` for the full fibre lower-bound sentence: only generic
  fibre, dominance and fibre API declarations; no dimension inequality (no match).
- `msearch.py Q77 ... loogle "topologicalKrullDim, fiber, irreducible, dimension"`:
  0 hits; the service reported unknown identifier `fiber`.
- `msearch.py Q77 ... grep "dimension.*(fiber|fibre)|closure.*image" AlgebraicGeometry`:
  no matching theorem.
- `rg` over `WeilConjectures` and `lean/Sheaf` for fibre-dimension lower bounds and
  generic fibre dimension: only unrelated fibre APIs and smoothness results.
- `grep -rl 'lem-zl-irreducible-fibre-dimension-lower-bound' dag/nodes`: only this node
  and its single citer were found.

## Statement corrected

The correction is forced by Lean's type: `topologicalKrullDim` is `WithBot ℕ∞`, which
has no subtraction.  The source's transcendence-degree computation supplies a natural
number difference, represented by the additive equation in the corrected statement.
The citer `lem-zl-finite-type-fibre-image-dimension-bounds` holds because it invokes the
lemma componentwise for exactly the same natural-number difference and equality locus.

## Second reading by Q77

Independent maintainer second reading, 2026-10-18 (not the original worker).

## Material and source read

Read packet.md, all 67 lines of check-brief2.md, the snapshot's stage-2 brief and delivery-errors,
the item JSON (including statement_change and its old proof), all six statement-dependency
records, the delivered Lean module and the delivered report at
`coord/reports/Q77/lem-zl-irreducible-fibre-dimension-lower-bound.md`.
There is no root snapshot/report.md; the committed report is the one reproduced in the packet.
Read all eight proof steps and the statements of their cited nodes in the read-only group clone.

The cited varieties.tex was absent from the local literature trees. Read the actual TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
`lemma-dimension-fibres-locally-algebraic`, and the official rendered Tag 0B2L at
https://stacks.math.columbia.edu/tag/0B2L. Parts (2)(a),(b) and the generic-point
transcendence-degree calculation are precisely the source of this node. The source permits
locally algebraic schemes; the already specified node deliberately concerns finite type
schemes. No extra finite-type restriction was introduced by this delivery.

## Hypotheses and conclusions

- Field k: `(k : Type u) [Field k]`, with no characteristic or algebraic-closedness condition.
- Schemes X,Y over k: `{X Y : Scheme.{u}}`, the two `Over (Spec (.of k))` instances.
  `Scheme.Over` is `OverClass`; the structure map is exactly `X ↘ Spec (.of k)`.
- X irreducible: `IrreducibleSpace X` includes `Nonempty X`. Neither reducedness nor integrality
  is imposed.
- Both schemes finite type: each structure map has `LocallyOfFiniteType` and `QuasiCompact`.
  This is the recorded dependency's conjunction, not an additional Noetherian hypothesis.
- k-morphism f: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`; `Hom.isOver_iff` is the commuting
  structure-map equation, with no properness, separatedness, dominance or flatness condition.
- Natural dimension difference: `∃ r : ℕ`, with `topologicalKrullDim X =
  topologicalKrullDim (closure (Set.range f.base) : Set Y) + (r : WithBot ℕ∞)`.
  The closure has the subtype topology. This is image closure, not the dimension of Y.
- Every source point: `∀ x : X, (r : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)`.
  `asFiber x` has type `f.fiber (f x)` and is the inverse fibre homeomorphism at x.
  Thus it is local topological dimension at the correct point, not stalk dimension or
  the global dimension of that fibre.
- Both final clauses use exactly the same r: `Dense` and `IsOpen` of the entire equality
  locus. They do not merely produce an unspecified dense open subset.

All clauses match, in the proper quantifier order. The single universe u is the ordinary
Mathlib Scheme/Over/fibre category universe, with arbitrary u; it does not specialize to
small schemes in a fixed universe, force a site/coefficient universe equality, or discard
an arbitrary lift case. Every variable is bound and autoImplicit is false.

## Exact dependency declarations and uniqueness

Inspected the declarations and their surrounding docstrings in the pinned source tree:
`Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:43` (all affine pairs are finite type),
`Morphisms/QuasiCompact.lean:43` (compact-open preimages), `AlgebraicGeometry/Over.lean:36,46`
(Over and IsOver), `AlgebraicGeometry/Fiber.lean:38,41,46,103,119` (fibre, projections,
homeomorphism, asFiber), `AlgebraicGeometry/ResidueField.lean:237` (canonical residue point),
`Topology/KrullDimension.lean:39` (krullDim of irreducible closed sets), and
`Topology/Irreducible.lean:46,52,107,174` (preirreducibility, nonempty irreducibility,
components and IrreducibleSpace).

`WeilConjectures/Mathlib/Topology/KrullDimension.lean:343` really defines local dimension by
`⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`; no data is hollow. The minimum exists
in the well-ordered extended dimension type. Inspected the recorded closed-irreducible
transcendence-degree, locally algebraic dimension, and open bounded-fibre-locus modules in
the group clone and the finite-dimensionality declaration in upstream FiniteType.lean:212.
Read the missing-local-copy residue-field module using the authorized
`scompile.py --source WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`:
its exact theorem includes both factor compatibilities and the field-quotient clause.

Independent rg searches over Mathlib AlgebraicGeometry, upstream WeilConjectures, and the
group's lean/Sheaf for dimension/fibre, topologicalKrullDim with fibre, and generic/dimension
found no duplicate of this theorem. Existing results concern smooth, flat or otherwise
special families, fibre constructions, or cohomological bounds. The delivery's recorded
LeanFinder, LeanSearch, Loogle and grep searches were also read; an unavailable/unknown-name
Loogle query was identified as such. No new notions or private replacement definitions
are introduced. There are no new definition nodes or dependency modules to validate.

## Source correction, citer audit, and proof

The additive natural-number representative is a valid source-based §1(C) correction. Both
global dimensions here are finite, the image closure is nonempty, and the generic
residue-field tower gives a nonnegative finite difference. Hence the existential additive
equation characterizes the same difference; it does not weaken the statement or introduce
infinite subtraction. statement_change records the old statement, source and changed proof.

The sole direct citer in the group DAG is
`lem-zl-finite-type-fibre-image-dimension-bounds`; there is no second direct citer to open.
Read its entire statement and proof, in particular steps 2 and 4. Step 2 applies the result
to reduced irreducible components; step 4 combines the same r with the fibre upper bound.
Both uses remain valid with the additive equation, so its `holds: true` verdict is correct.

Checked the eight steps: Noetherianity and compact subsets give finite-type f; permanence
and base change give finite-dimensional fibres; sobriety supplies the generic point;
image closure has its image as generic point; the transcendence-degree tower gives r;
the generic fibre is irreducible and has the compatible generic residue field; its local
dimension is r; the open bounded-dimension locus at each finite local value contains the
generic point; and the locus at r is dense open and equals the equality locus. Each cited
statement supplies the fact used. No missing canonical construction, arbitrary map, hollow
choice, or unstated statement prerequisite is concealed here.

## Edge cases

The empty X is excluded exactly because irreducible means nonempty. A morphism from such X
to empty Y cannot exist. Fibres evaluated at f(x) are always nonempty, even if other fibres
are empty. For dimension-zero X, r=0; the identity also has r=0. For a structural map to
Spec k, r=dim X and local fibre dimension equals dim X; it is not merely a nonnegativity
claim. Nonreduced irreducible schemes and all field characteristics remain covered. The
finite-type hypotheses preclude infinite global dimensions; the extended type nevertheless
retains its standard bottom convention. There are no index-set or zero-object parameters.

## Findings and complete fixes

1. H8: the delivered theorem docstring compressed eight steps into four sentences, omitting
   the dependency identifiers, finiteness argument for arbitrary local fibre dimensions,
   and compatible residue-field calculation. The replacement module spells out all eight
   steps with their cited nodes. The statement and sorry proof are unchanged.
2. H9 / stage-2 brief §3: the delivered imports omitted the already stated proof modules.
   Added ordinary imports of ClosedIrreducibleDimensionTrdeg, DimensionLocallyAlgebraic,
   LocalFibreDimensionOpen, upstream finite-type dimension, and fibre-product residue fields.
3. H11: the second-reading section explicitly said no second reading occurred. The complete
   replacement report preserves the Worker report and provides this actual independent
   clause-by-clause review under the exact required heading. It also corrects the worker's
   misleading constant-map/nonnegativity edge-case sentence.
4. The snapshot report/packet contains no concrete recorded compiler output. This is repaired
   by recording the successful independent reproductions below, rather than inventing an
   earlier run. No mathematical or signature defect was found.

The fixes are complete replacements at
`fixes/lean/Sheaf/DeligneLaumon/IrreducibleFibreDimensionLowerBound.lean` and
`fixes/lem-zl-irreducible-fibre-dimension-lower-bound.report.md`, in the stage-2 merge tool's
accepted formats. No node-record replacement is necessary: a byte-for-byte comparison of
the theorem signature (keyword through the space before `:=`) with lean.statement is True,
both before and after the fixes. No line in the fixed Lean file exceeds 100 characters.

## Compiler and isolation evidence

Ran only the authorized per-file wrapper, never lake build or a global build:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q77
lem-zl-irreducible-fibre-dimension-lower-bound
snapshot/lean/Sheaf/DeligneLaumon/IrreducibleFibreDimensionLowerBound.lean`

Exit 0: sandbox check 3.0 s; library-path check 2.1 s. No errors or warnings printed.

Repeated for the complete replacement under `fixes/lean/...`:
exit 0, sandbox check 2.4 s; library-path check 2.1 s. No errors or warnings printed.
The wrapper reports a server compile with a private side overlay; its printed temporary
artifact directories were `/dev/shm/nt-tmp/nt-local-compile-blzmxmmh/.lbuild` and
`/dev/shm/nt-tmp/nt-local-compile-69rvdi9a/.lbuild`. This is server-confirmed per-file evidence,
not an assertion that the current wrapper compiled on the local host.

Read the shared origin/newtargets-dag route-pivot dropped list and tested its intersection
with all statement/proof dependency ids: empty. There is no item repair-note at the named
shared ref; no infinity/dg/model machinery appears in this delivery. No pro-etale substitute
is involved. No definitions, local proofs beyond sorry, new axioms, live Lean writes,
git mutations, claims, merges or deliveries were made. Only this review and fixes were
written. The recorded immutable head is f1cbb1ef790ec9dcf80ecbdcd629c859292b6f03.
