## Worker report

The module defines the degree over a field, the predicate that a natural number bounds
all fibre degrees, and the predicate that such a bound exists. All three are definitions;
there are no theorem proofs.

The hypothesis `f : X ⟶ Y` is the node's morphism of schemes; `X` and `Y` are arbitrary
`Scheme.{u}`. The point `y : Y` in `BoundsFiberDegrees` ranges over every base point.
`Y.residueField y` is its residue field, `f.fiber y` is the scheme-theoretic fibre, and
`f.fiberToSpecResidueField y` is its structure morphism to the residue-field spectrum.
The clause that each fibre is finite over its residue field is
`IsFinite (f.fiberToSpecResidueField y)`. The degree clause is
`degreeOverField (Y.residueField y) (f.fiber y) (f.fiberToSpecResidueField y) ≤ n`.
In `degreeOverField`, the algebra structure is induced by the composite
`(Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ t.appTop`, and `Module.finrank K Γ(T, ⊤)`
is the dimension of global sections. The hypothesis `n ≥ 0` is represented by
`n : ℕ`. The final clause is `∃ n : ℕ, BoundsFiberDegrees f n`.

Dependencies used: `Mathlib.AlgebraicGeometry.Fiber` provides
`AlgebraicGeometry.Scheme.Hom.fiber`, `fiberToSpecResidueField`, and
`AlgebraicGeometry.Scheme.residueField`; `Mathlib.AlgebraicGeometry.Morphisms.Finite`
provides `AlgebraicGeometry.IsFinite`; `Mathlib.AlgebraicGeometry.Scheme` provides
`AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, `Scheme.ΓSpecIso`, and `Γ(T, ⊤)`;
`CategoryTheory.Limits.pullback` underlies the recorded fibre declaration.

Edge cases: an empty base satisfies the universal bound clause vacuously; the
existential bound still has the witness `0`. An empty fibre has zero global-section
dimension and is finite over its residue field, so `n = 0` is permitted. A nonempty
degree-zero fibre cannot pass the finite-plus-degree clause without the corresponding
finite-dimensional algebra actually having dimension zero. The definitions impose no
characteristic or nonemptiness assumption on the residue field. The universe `u` is
arbitrary.

Searches: `msearch leanfinder` with "finite fibres of a scheme morphism with uniformly
bounded degree measured by dimension of global sections over residue field" returned
finite-fibre results but no degree-bound predicate; `msearch loogle` with
`AlgebraicGeometry.Scheme.Hom.finrank, AlgebraicGeometry.Scheme.Hom.fiber` returned no
hits; `msearch grep` with `universally.?bounded|fiber.*degree|fibre.*degree` under
Mathlib AlgebraicGeometry returned no hits. `rg` for universally-bounded and degree
names in the source repository and `lean/Sheaf` found no match. `grep -rn` for this
node ID in `WeilConjectures` found no match. The preexisting node's LeanSearch and
LeanFinder results were also read. `Scheme.Hom.finrank` in Mathlib's `FlatRank.lean`
measures finite flat rank but does not provide this predicate.

The Stacks `morphisms.tex` checkout is absent from this machine's `literature` tree;
the node's quoted source statement, tag, and source-place description were used.

## Second reading by H1

Independent comparison with the node and Stacks Project, Morphisms, Section 29.58,
Definition Tag 03J4 (the local `morphisms.tex` checkout is absent; the Stacks page was
read directly). The node's objects, hypotheses, and conclusions match as follows:

- The arbitrary morphism `f : X ⟶ Y` between `Scheme.{u}` objects matches the node's
  `f : X → Y`; there is no finiteness, separation, Noetherian, field, or characteristic
  hypothesis on `f`, `X`, or `Y`.
- For each `y : Y`, `Y.residueField y` is the node's `κ(y)`, `f.fiber y` is its
  `X ×_Y Spec κ(y)`, and `f.fiberToSpecResidueField y` is the second projection.
  These were checked in the dependency node records and Mathlib `Fiber.lean`.
- `IsFinite (f.fiberToSpecResidueField y)` is precisely the node's requirement that
  the fibre be finite over `κ(y)`. Mathlib `IsFinite` requires an affine morphism
  with finite ring maps on affine opens, as in the dependency node.
- `(f.fiberToSpecResidueField y).finrankΓ ≤ n` is the degree inequality. The source
  checkout's `Scheme.Hom.finrankΓ` is `Module.finrank` of global sections with the
  algebra structure from `ΓSpecIso.inv ≫ t.appTop`; this is exactly the degree in the
  node and in the paragraph before Stacks 03J4. It is defined without extra instances.
- `n : ℕ` gives the node's nonnegative integer. `∀ y : Y, ... ∧ ...` retains the
  universal quantifier and both clauses in the same order. The final
  `∃ n : ℕ, BoundsFiberDegrees f n` is the node's universal boundedness clause.

Edge cases: an empty `Y` makes the universal predicate vacuous and permits witness
`0`; an empty fibre is finite and has degree zero. A zero bound permits exactly
finite fibres of degree zero. No characteristic is selected. Universe `u` is
arbitrary for the scheme objects and residue fields. The Stacks source calls `n`
an integer, while the node expressly restricts to `n ≥ 0`; the code follows the node.

Independent searches: `msearch leanfinder` for "uniform bound on degrees of finite
scheme fibres of a morphism" found finite-fibre results but no general bound;
`msearch loogle` for `Scheme.Hom.finrankΓ, Scheme.Hom.fiberToSpecResidueField`
found no match (Loogle does not index the source-checkout name); `msearch grep` for
`universally bounded fibres|finite fibre degree bound` found no match. `rg` over
Mathlib AlgebraicGeometry, the source `WeilConjectures` tree, and repository
`lean/Sheaf` found no existing general bound predicate. The source does contain
`Scheme.Hom.finrankΓ`, exactly the degree of global sections, and `fiberDegree`,
which requires an affine-morphism instance and is not the general bound predicate.
The source's `exists_forall_fiberDegree_SpecMap_le` is only for standard etale
algebras, so is a special case.

Mismatch and repair: the first draft duplicated the existing degree notion as
`degreeOverField`. I removed that definition and used `Scheme.Hom.finrankΓ` in
`BoundsFiberDegrees`, imported its source module, and removed the duplicate name
from the node's `lean.declarations`. The worker report above describes the first
draft; this second reading records the delivered version. No theorem is proved,
no definition contains `sorry`, and the revised file compiles cleanly.
