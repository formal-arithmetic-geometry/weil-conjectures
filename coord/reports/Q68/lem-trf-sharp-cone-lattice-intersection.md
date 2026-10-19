## Worker report

The module `Sheaf.GroupTheory.SharpConeLatticeIntersection` states
`AlgebraicGeometry.sharp_fs_monoid_cone_lattice_intersection`, with one `sorry` proof
and no new definitions. The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence (in the explanation below, `G` abbreviates
`Additive (Algebra.GrothendieckGroup (Multiplicative P))`, and `V` abbreviates
`TensorProduct ℤ ℚ G`; these are explanations, not new Lean definitions):

- The additive commutative monoid is `(P : Type u) [AddCommMonoid P]`, with `u`
  explicitly declared. There is no nontriviality, positive-rank or cancellation
  typeclass assumption restricting its cases.
- Finite generation, integrality and saturation are exactly
  `hfs : IsFineSaturatedMonoid (Multiplicative P)`. Opening the dependency's
  definition gives a finite generating set, injectivity of the canonical group
  completion map, and the positive-integer saturation condition. The type tag
  changes addition to multiplication for this existing predicate, without changing
  any elements or imposing a new structure on them.
- Sharpness is `hsharp : ∀ p : P, IsAddUnit p → p = 0`: every additively invertible
  element is zero. Zero is always an additive unit, so this is precisely the
  node's “0 is its only invertible element.”
- The group completion is the actual `G` just displayed, not a supplied abstract
  group or an arbitrary embedding. Its additive notation comes from `Additive`.
- `V = ℚ ⊗[ℤ] G` follows the existing characteristic-rank definition. Tensor
  symmetry canonically identifies this with the node's `G ⊗[ℤ] ℚ`; under that
  identification the node's `g ⊗ 1` is our `1 ⊗ g`. The rational scalar action is
  the canonical one on the first factor. This is purely a tensor-order convention.
- `(C : PointedCone ℚ V)` with `hC` fixes `C` to
  `PointedCone.hull ℚ (Set.range (fun p ↦ 1 ⊗ [p]))`. `PointedCone.hull` is
  `Submodule.span` over the nonnegative rationals; `PointedCone.mem_hull_set`
  gives precisely finite sums of nonnegative rational multiples, including zero
  coefficients and the empty sum. The parameter and equality are a way to name
  the prescribed `C`, not a further mathematical condition on `P`.
- Clause (a), finite free group: the first conjunct is
  `∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ G)`. A basis records existence and
  uniqueness of every integral coordinate expansion, including `r = 0`.
- Clause (a), lattice embedding: the second conjunct is
  `Function.Injective (fun g : G ↦ (1 : ℚ) ⊗ₜ[ℤ] g)`.
- Clause (b), rational polyhedrality with lattice generators: the third conjunct is
  `∃ (m : ℕ) (v : Fin m → G), C = PointedCone.hull ℚ (Set.range
  (fun j ↦ 1 ⊗ v j))`. Its finitely many generators are in the actual group
  completion, as required. The same hull definition gives the stated coefficient
  description.
- Clause (b), pointedness in the node's convention: the fourth conjunct is
  `∀ x : V, x ∈ C → -x ∈ C → x = 0`. Because the cone contains zero this is
  exactly `C ∩ (-C) = {0}`. Mathlib's word `PointedCone` alone only records zero
  membership, so it would not suffice for this clause.
- Clause (b), spanning by differences: the fifth conjunct is
  `∀ x : V, ∃ a ∈ C, ∃ b ∈ C, x = a - b`. This explicitly states the node's
  difference formulation, rather than merely a linear-span conclusion.
- Clause (c): the final conjunct says for each `g : G`,
  `1 ⊗ g ∈ C ↔ ∃ p : P, [p] = g`. Together with injectivity this is precisely
  the equality of the image of `P` with `C ∩ G` inside `V`; no replacement
  lattice or choice of lattice is used.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` is the recorded module of
  `def-trf-fs-log-blowup` and is publicly imported. Its `IsFineSaturated`
  definition uses `AlgebraicGeometry.IsFineSaturatedMonoid`, provided by its
  public import `Sheaf.AlgebraicGeometry.LogRegularPair`; that definition's
  complete docstring and signature were read. The same modules use the actual
  Grothendieck group and the tensor order used here. No repair is needed.
- `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup` supplies
  `Algebra.GrothendieckGroup`, `.of` and its group structure, through those
  public imports. The docstrings explicitly identify the group completion and
  warn that the map need not be injective without integrality; integrality is
  retained in `hfs` and tensor injectivity is a conclusion, not assumed.
- `Mathlib.Geometry.Convex.Cone.Pointed` supplies `PointedCone.hull`; its
  definition and the full signature of `mem_hull_set` were read.
- The proof dependency `lem-trf-fg-torsionfree-group-free` has status `mathlib`.
  Its recorded `mathlib_match`, `Module.basisOfFiniteTypeTorsionFree'` in
  `Mathlib.LinearAlgebra.FreeModule.PID`, was read with its docstring and full
  signature: finite and torsion-free modules over a PID receive a sigma of a
  natural number and a basis indexed by `Fin n`. This module is imported for
  the postponed proof. The docstring records all six DAG proof steps, including
  finite generation, torsion-freeness, coordinate injectivity, finite cone
  generation, denominator clearing, and sharpness.

Source checked: the local ILO PDF was read using `pdftotext -layout`. VIII 3.1.17
on printed p. 101 defines saturation by positive powers in the group completion;
Remark 3.1.29 on printed p. 103 discusses the combinatorial fan description.
As the node already states, the full lattice-cone argument is its explicit
agent expansion, not a verbatim theorem in those paragraphs.

Edge cases checked before writing:

- The zero monoid is allowed: `r = m = 0`, zero group and rationalization,
  zero cone, trivial injection, and differences `0 - 0` satisfy every clause.
- Empty generating families and empty conical sums are allowed; a cone hull
  always contains zero. Neither cone nor lattice requires a nonzero vector.
- Zero coefficients are included because the hull uses nonnegative scalars.
- Nontrivial units are excluded exactly by sharpness, not by an extra
  cancellativity or torsion-free hypothesis; the latter properties must follow.
- Saturation is the positive-integer condition already in the dependency,
  with no accidental condition at integer zero.
- No universe equality, positivity of rank, or `Nontrivial V` instance is used.

Searches for an existing statement or notion:

1. `msearch.py ... leanfinder` query “A finitely generated saturated sharp
   integral additive monoid equals the lattice points of the rational cone in
   its group completion”: eight results, including number-field fundamental
   cone integer sets, `ConvexCone.IsGenerating.isReproducing`, and
   `IsAffineMonoid.toFG`; no sharp fs monoid lattice-intersection theorem.
2. `msearch.py ... leansearch` query “A sharp saturated finitely generated
   monoid is the lattice part of its rational cone”: eight results, including
   `ConvexCone.Pointed`, `ConvexCone.gc_hull_coe`, `AddMonoid.fg_def`, and
   `IsAffineMonoid.toFG`; none states the item. This search exposed the
   difference between Mathlib's pointed terminology and the node's terminology.
3. `msearch.py ... loogle` query
   `PointedCone.hull, AddMonoidAlgebra, Algebra.TensorProduct`: zero hits;
   service reports unknown identifier `Algebra.TensorProduct`. This query is
   unavailable for matching; the correct `TensorProduct` and hull sources were
   opened directly instead.
4. `msearch.py ... grep` query
   `cone.*lattice|lattice.*cone|IsAffineAddMonoid|IsFineSaturatedMonoid`:
   twenty results about number-field fundamental cones, the affine-monoid
   abbreviation, and unrelated lattice cones. No matching theorem.
5. Direct `rg -n` of
   `cone.*lattice|lattice.*cone|IsFineSaturatedMonoid|sharp_cone|sharpCone` in
   `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the side project's
   `lean/Sheaf` found the usable fs predicate and its callers, and the existing
   `Sheaf.Paper.GordanRationalCone` module. That module was opened: its Gordan
   lemma concerns finite generation of lattice points given an already free
   lattice and finite cone; it neither states this theorem nor supplies its
   saturation argument.
6. Direct `grep -rn` of the item id in upstream `WeilConjectures` found no
   declaration. Direct `rg -n` of the new declaration name in Mathlib, upstream,
   `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

No node fault, disputed statement, new notion, or dependency repair was found.

## Second reading by Q68

This is the author's second pass, as directed by the dispatcher brief: no other
agent was started. Independent review is supplied by the maintainer on delivery.
With the node and module open, I checked the additive monoid and fs predicate,
sharpness, actual group completion, tensor symmetry convention, and the equality
fixing the canonical cone. I then matched the six conclusion conjuncts to finite
basis, rationalization injection, finite lattice cone generators, absence of a
line, difference spanning, and the lattice-intersection assertion. In particular,
`PointedCone` does not silently replace the stronger no-line clause, the final
biconditional uses the canonical image in the actual completion, and both finite
index sets may be empty. The module has one theorem with a `sorry` proof and its
six-step natural-language proof. No mathematical mismatch was found and no
statement correction was made.
